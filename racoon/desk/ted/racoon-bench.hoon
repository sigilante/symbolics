::  /ted/racoon-bench
::
::  Benchmarks as DATA, over %fyrd.  Driven by scripts/bench.sh; see
::  /ted/baloon-bench for why the sleep bracket is the clock and why a
::  slog was not good enough.
::
::  This one covers phase A: the sum of two real algebraic numbers,
::  which is a bivariate resultant plus one factorization, and is the
::  measurement SPEC A8 got wrong from theory.
::
::  RACOON ONLY, and that is the point.  /lib/racoon-alg is a door over
::  its recombination step, defaulting to +firr:zx, so this file
::  measures the Zassenhaus column without Baloon anywhere on its import
::  list -- racoon/desk still builds alone.  The van Hoeij column is
::  /ted/baloon-bench's %alg job, which is the same split
::  /gen/racoon-alg-bench and /gen/baloon-alg-bench already use.  The
::  fifteen lines of parsing below appear in both, which is the price of
::  that layering and is cheaper than the dependency.
::
::  Polynomials arrive as TEXT and are parsed with +redz:fmt, so no
::  literal is transcribed here and the caller picks the case.  Both
::  operands are canonicalized outside the timed region: parsing and
::  root isolation are not what is being measured.
::
/-  spider, *racoon
/+  strandio, racoon, rr=racoon-roots, fmt=racoon-fmt, al=racoon-alg
/+  rf=racoon-rf
=,  strand=strand:spider
=/  qx  qx:racoon
=>
|%
::    $job:  what to measure, as a FLAT four-tuple
::
::  Same wire format as /ted/baloon-bench, and for the same reason: a
::  $% with named fields does not survive ;;.  Cords are atoms, so the
::  two polynomials ride in .a and .b.
::
::      [%alg 'p' 'q' 0]      the sum of two algebraic numbers
::      [%int d fam 0]        +integrate:rf on a degree-d denominator,
::                            at the DEFAULT binding.  SPEC F9.6.
+$  job  [tag=@tas a=@ b=@ c=@]
::    +int-case:  the integrand for the %int benchmark
::
::  Two families, because "expensive to factor" and "integrable" pull
::  against each other -- the denominators Zassenhaus finds hard are
::  irreducible with many modular factors, and an irreducible
::  denominator of degree > 2 usually has IRRATIONAL residues, which
::  SPEC F6 puts out of range.  So:
::
::    fam 0   1 / prod_(i=1..d) (x - i)
::            splits completely, so r = d and every residue is
::            rational.  Zassenhaus finds all d factors at cardinality
::            one, which is the cheap end of recombination.
::
::    fam 1   (x^d + 1)' / (x^d + 1)
::            irreducible, and the residue is 1 by construction, since
::            int g'/g is log g.  MEASURED r = 2 at every degree here,
::            not the large r this was reached for -- x^d + 1 splits
::            into two modular pieces and the +lat-min gate never
::            engages.  What it measures is the single-factor path:
::            Hermite and one residue on a high-degree denominator,
::            with no partial-fraction spread.
::
::  Both are built rather than transcribed, so neither can be a wrong
::  literal.  The same twelve lines appear in /ted/baloon-bench: the
::  two bindings live in different desks on purpose, which is what
::  keeps racoon/desk building alone.
++  int-case
  |=  [d=@ud fam=@ud]
  ^-  qol
  ?:  =(0 fam)
    =/  i=@ud    1
    =/  acc=qol  ~[[--1 1]]
    |-  ^-  qol
    ?:  (gth i d)  acc
    $(i +(i), acc (mul:qx acc ~[[(dif:si --0 (sun:si i)) 1] [--1 1]]))
  %-  canon:qx
  (weld ~[`frac`[--1 1]] (weld (reap (dec d) `frac`[--0 1]) ~[`frac`[--1 1]]))
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
::  %int: SPEC F9.6, at the door's DEFAULT binding.  Built outside the
::  bracket, since constructing a degree-16 denominator is not the
::  measurement.
=/  ig=rfun:rf
  ?.  =(%int tag.j)  zero:rf
  =/  g=qol  (int-case a.j b.j)
  ?:  =(0 b.j)  (new:rf ~[[--1 1]] g)
  (new:rf (pderiv:rf g) g)
?:  =(%int tag.j)
  ;<  ~       bind:m  (sleep:strandio ~s0)
  ;<  t0=@da  bind:m  get-time:strandio
  =/  r  (integrate:rf ig)
  ;<  ~       bind:m  (sleep:strandio ~s0)
  ;<  t1=@da  bind:m  get-time:strandio
  ::  the check is the number of logarithmic terms: an integrand that
  ::  fell out of range returns ~ and would otherwise look merely fast
  =/  chk=@ud  ?~(r 0 (lent ls.u.r))
  =/  us=@ud   (div (mul (sub t1 t0) 1.000.000) (bex 64))
  (pure:m !>([us chk]))
?>  =(%alg tag.j)
=/  pa=(unit zol)  (redz:fmt a.j)
=/  pb=(unit zol)  (redz:fmt b.j)
::  a parse failure returns 0 rather than crashing, so bench.sh reports
::  "check 0" instead of an opaque thread failure
?~  pa  (pure:m !>([0 0]))
?~  pb  (pure:m !>([0 0]))
=/  ia  (isolate:rr u.pa)
=/  ib  (isolate:rr u.pb)
?~  ia  (pure:m !>([0 0]))
?~  ib  (pure:m !>([0 0]))
::  +isolate produces roots ascending, so +rear is the largest
=/  a  (make:al u.pa (rear ia))
=/  b  (make:al u.pb (rear ib))
::  INSIDE the bracket: only the arm under test.  Nock is eager, so
::  binding the sum to a leg computes it.
;<  ~       bind:m  (sleep:strandio ~s0)
;<  t0=@da  bind:m  get-time:strandio
=/  sum  (add:al a b)
;<  ~       bind:m  (sleep:strandio ~s0)
;<  t1=@da  bind:m  get-time:strandio
::  OUTSIDE it: the check.  The degree of the sum's minimal polynomial
::  is the whole point of the operation -- a run that returned early, or
::  one that failed to reduce, does not produce it -- and +deg is a
::  +lent, so charging it to the measurement would be arbitrary.
=/  chk=@ud  (deg:al sum)
=/  us=@ud  (div (mul (sub t1 t0) 1.000.000) (bex 64))
(pure:m !>([us chk]))
