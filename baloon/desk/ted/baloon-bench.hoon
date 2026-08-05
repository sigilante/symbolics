::  /ted/baloon-bench
::
::  Benchmarks as DATA, over %fyrd, so that a measurement is not a thing
::  scraped off a terminal.  Driven by scripts/bench.sh.
::
::  WHY THIS EXISTS.  The generators print their timings through
::  ~>(%bout ...), which is a slog: it goes to the ship's output and
::  nowhere else.  Reading it back means scraping the tmux pane, and in
::  one afternoon that produced four distinct failures -- a baseline
::  sampled after the send, a `took` count that is not monotonic because
::  the pane's history is 2.000 lines, a clear-history that leaves the
::  visible screen alone, and a -test that ran BEFORE its |commit landed
::  and returned a false green on a negative control.  The last one is
::  the reason this exists: a measurement harness that can silently
::  report the wrong build is worse than no harness.
::
::  %fyrd is synchronous and returns the thread's product, so the caller
::  cannot read a stale answer and cannot race the commit.  It is the
::  same mechanism scripts/test.sh already uses for the suites.
::
::  HOW THE CLOCK WORKS.  ~>(%bout ...) cannot help here -- it prints,
::  it does not produce.  Arvo's `now` is fixed for the duration of an
::  event, so two +get-time calls around a computation return the same
::  value.  Instead the work is bracketed by two zero-length sleeps:
::
::      sleep ~s0      ->  a fresh event begins
::      t0 = now           the event's clock
::      <the work>         runs INSIDE that event
::      sleep ~s0      ->  behn fires at t0, already past, so the next
::      t1 = now           event's `now` is real time after the work
::
::  so t1 - t0 is the work plus one behn round trip.  That round trip is
::  not free and it is not subtracted: run +nop to measure it, which is
::  what scripts/bench.sh does before anything else.  Sub-millisecond
::  numbers from this harness should be read as "small", not as exact.
::
::  THE PRODUCT CARRIES A CHECK, not just a duration.  A benchmark that
::  measures a crash, or an arm that returned instantly because it did
::  nothing, is the failure mode a bare number cannot show -- so every
::  job returns something derived from its answer, and bench.sh prints
::  it beside the time.
::
/-  spider, *baloon, *racoon
/+  strandio, baloon, racoon, vh=vanhoeij, cas=baloon-cases
/+  rr=racoon-roots, fmt=racoon-fmt, ba=baloon-alg
=,  strand=strand:spider
=/  zx  zx:racoon
=/  zm  zm:baloon
=>
|%
::    $job:  what to measure, as a FLAT four-tuple
::
::  A $% with named fields would read better and does not survive ;; --
::  clamming [%nop ~] needs a normalizer for the ~ and there is not one.
::  So the wire format is a tag and three atoms, which clams trivially,
::  and each branch names its own fields on arrival.  Cords are atoms,
::  which is why the polynomial arguments fit here too.
::
::      [%nop 0 0 0]          the behn round trip, so the harness floor
::                            is measured rather than assumed
::      [%vh k side 0]        Swinnerton-Dyer SD_k.  side 0 is
::                            Zassenhaus (+firr:zx), side 1 is van Hoeij
::                            with the lattice FORCED (+fact:vh f 0) --
::                            forced because +factor falls through
::                            +lat-min at r = 4 and r = 8 and would
::                            measure Zassenhaus twice
::      [%lll r m bits]       +lll on a lattice of r + m rows
::      [%alg 'p' 'q' 0]      the sum of two algebraic numbers, with van
::                            Hoeij BOUND IN.  /ted/racoon-bench runs the
::                            same measurement on the default binding,
::                            and lives over there so that racoon/desk
::                            keeps building without Baloon
+$  job  [tag=@tas a=@ b=@ c=@]
--
^-  thread:spider
|=  arg=vase
=/  m  (strand ,vase)
^-  form:m
::  ;; and not !<: the %noun mark hands the thread a vase typed `*`, so
::  !< cannot nest it into $job and fails the strand before it starts.
::  Clamming the raw noun is the shape /ted/test.hoon uses for the same
::  reason -- it pattern-matches q.arg rather than casting it.
::
::  The unwrap is because a %fyrd payload may arrive either bare or
::  behind a leading ~, depending on how the caller wrote it --
::  /ted/test.hoon reads [~ path] and scripts/bench.sh sends the job
::  itself.  No tag is 0, so a null head is unambiguously the wrapper.
=/  raw=*  ?:(?@(q.arg & =(~ -.q.arg)) +.q.arg q.arg)
=/  j=job  ;;(job raw)
::  build OUTSIDE the bracket: constructing the input is not the
::  measurement, and for +lll it is a third of the work.  Two typed legs
::  rather than one forked one -- a ?- over the job would infer a union
::  of zol and zmat that neither branch below could cast out of.
=/  f=zol    ?:(=(%vh tag.j) (sd:cas a.j) ~)
=/  b=zmat   ?:(=(%lll tag.j) (lattice:cas a.j b.j c.j) ~)
::  the algebraic operands, likewise built before the clock starts --
::  canonicalizing one is itself a factorization
=/  ab=(unit [anum:ba anum:ba])
  ?.  =(%alg tag.j)  ~
  =/  pa=(unit zol)  (redz:fmt a.j)
  =/  pb=(unit zol)  (redz:fmt b.j)
  ?~  pa  ~
  ?~  pb  ~
  =/  ia  (isolate:rr u.pa)
  =/  ib  (isolate:rr u.pb)
  ?~  ia  ~
  ?~  ib  ~
  `[(make:ba u.pa (rear ia)) (make:ba u.pb (rear ib))]
::  INSIDE the bracket: only the arm under test.  Nock is eager, so
::  binding the product to a leg computes it -- nothing here is elided.
;<  ~       bind:m  (sleep:strandio ~s0)
;<  t0=@da  bind:m  get-time:strandio
=/  fs=(list zol)
  ?.  =(%vh tag.j)  ~
  ?:  =(0 b.j)  (firr:zx f)
  (fact:vh f 0)
=/  red=zmat  ?:(=(%lll tag.j) (lll:vh b) ~)
=/  sum=(unit anum:ba)  ?~(ab ~ `(add:ba -.u.ab +.u.ab))
;<  ~       bind:m  (sleep:strandio ~s0)
;<  t1=@da  bind:m  get-time:strandio
::  OUTSIDE it: the check.  This is not pedantry -- +reduced is the
::  SPECIFICATION of +lll, a full Gram-Schmidt over rationals, and
::  computing it inside the bracket made every %lll reading about 60%
::  too high before anyone noticed.  A check that costs more than a
::  +lent belongs after the clock stops.
=/  chk=@ud
  ?+  tag.j  ~|(%bad-job !!)
    %nop  0
    ::  the factor count: 1 means irreducible, which is the answer for
    ::  every SD_k, and is what a silently-empty result would not give
    %vh   (lent fs)
    ::  1 if the product is LLL-reduced, which is the whole contract
    %lll  ?:((reduced:vh red) 1 0)
    ::  the degree of the sum's minimal polynomial: 0 means the input
    ::  did not parse, which bench.sh reports rather than hiding
    %alg  ?~(sum 0 (deg:ba u.sum))
  ==
::  microseconds: @dr counts 2^-64 seconds, so scale before dividing to
::  keep the integer division from flooring everything short to zero
=/  us=@ud  (div (mul (sub t1 t0) 1.000.000) (bex 64))
(pure:m !>([us chk]))
