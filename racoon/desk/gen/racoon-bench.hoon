  ::  /gen/racoon-bench
::::  Racoon benchmark generator
::
::  Usage:  +racoon-bench
::
::  Prints a plain table of timings.  There are NO performance gates in
::  Milestone A (SPEC S11.4): the numbers exist to be recorded in README.md as
::  the denominator for Milestone B speedup claims.
::
::  Method.  Each row wraps a fold over a PRECOMPUTED input list in
::  ~>(%bout ...), which slogs "took ..." and returns the accumulator.  Inputs
::  are built outside the timed region so that list construction is not
::  charged to the arm.  Returning the accumulator forces every call, which
::  keeps the work from being elided.
::
::  Read a row as: the label line, then the "took" line the runtime slogs for
::  it.  Divide by the iteration count for per-call cost.
::
::  SPEC S11.4 also names polynomial rows -- mul/gcd over a 61-bit F_p at
::  degrees 16/64/256, gcd:zx at degree 64, factor:zx at degree 32.  Those
::  arms do not exist until Phases 1-3; +polynomial-rows below is where they
::  land, and it is deliberately left empty rather than faked.
::
/-  *racoon
/+  racoon
=/  nz  nz:racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
:-  %say
|=  *
:-  %noun
::  iteration count per row; raise it here if a row is too fast to resolve
=/  n=@ud  100
|^  ^-  ~
    ~&  '::'
    ~&  '::  racoon-bench -- Milestone A baselines, no gates'
    ~&  [%iterations n]
    ~&  '::'
    ~&  '::  +nz  integers and number theory'
    =/  a  bench-gcd
    =/  b  bench-egcd
    =/  c  bench-isqrt
    =/  d  bench-is-prime-small
    =/  e  bench-is-prime-61-bit
    =/  f  bench-crt
    =/  g  bench-ratrec
    ~&  '::'
    ~&  '::  +qq  rational scalars'
    =/  h  bench-qq-add
    =/  i  bench-qq-mul
    =/  j  bench-qq-div
    =/  k  bench-qq-cmp
    ~&  '::'
    ~&  '::  +zx  Z[x]  (mx/qx rows await Phases 1-3)'
    =/  l  polynomial-rows
    ~&  '::'
    ::  consume every accumulator so nothing is elided
    ~&  [%checksum :(add a b c d e f g h i j k l)]
    ~
::
::  Input supplies, built outside the timed regions.
::
++  seed  0xbeef.cafe.0000.0001
::    +naturals:  n pseudorandom naturals below hi
++  naturals
  |=  [count=@ud hi=@ud]
  ^-  (list @ud)
  =/  gen  ~(. og seed)
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  =(0 count)  out
  =^  r  gen  (rads:gen hi)
  $(count (dec count), out [r out])
::    +naturals-from:  n pseudorandom naturals in [lo, lo + span)
++  naturals-from
  |=  [count=@ud lo=@ud span=@ud]
  ^-  (list @ud)
  %+  turn  (naturals count span)
  |=(r=@ud (add lo r))
::    +cycle:  repeat a nonempty list until it has count elements
++  cycle
  |=  [count=@ud src=(list @ud)]
  ^-  (list @ud)
  ?~  src  ~
  =/  rem=(list @ud)  src
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  =(0 count)  out
  ?~  rem  $(rem src)
  $(count (dec count), rem t.rem, out [i.rem out])
::    +fracs:  n canonical rationals
++  fracs
  |=  count=@ud
  ^-  (list frac)
  %+  turn  (naturals count 100.000)
  |=(r=@ud (new:qq (sun:si r) +((mod r 997))))
::
::  Timed rows.  Each slogs its label, then ~>(%bout) slogs the elapsed time.
::
++  bench-gcd
  =/  xs  (naturals n 1.000.000.000.000.000.000)
  =/  ys  (naturals n 1.000.000.000.000.000)
  ~&  '  gcd:nz            60-bit x 50-bit'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  ?~  ys  acc
  $(xs t.xs, ys t.ys, acc (add acc (gcd:nz i.xs i.ys)))
::
++  bench-egcd
  =/  xs  (naturals n 1.000.000.000.000.000.000)
  =/  ys  (naturals n 1.000.000.000.000.000)
  ~&  '  egcd:nz           60-bit x 50-bit'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  ?~  ys  acc
  $(xs t.xs, ys t.ys, acc (add acc d:(egcd:nz i.xs i.ys)))
::
++  bench-isqrt
  =/  xs  (naturals n 18.446.744.073.709.551.616)
  ~&  '  isqrt:nz          64-bit'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  $(xs t.xs, acc (add acc (isqrt:nz i.xs)))
::
++  bench-is-prime-small
  =/  xs  (naturals-from n 1.000.000 1.000.000)
  ~&  '  is-prime:nz       ~20-bit'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  $(xs t.xs, acc (add acc ?:((is-prime:nz i.xs) 1 0)))
::
++  bench-is-prime-61-bit
  ::  The worst case, and the only honest one: 61-bit PRIMES.  A random
  ::  61-bit odd number is almost always rejected by trial division against
  ::  the witness schedule, so sampling the range measures early exit rather
  ::  than Miller-Rabin.  On a prime every witness runs to completion.
  =/  ps=(list @ud)
    :~  2.305.843.009.213.693.951
        2.305.843.009.213.693.921
        2.305.843.009.213.693.907
        2.305.843.009.213.693.723
        2.305.843.009.213.693.693
        2.305.843.009.213.693.669
    ==
  =/  xs  (cycle (div n 10) ps)
  ~&  '  is-prime:nz       61-bit primes  (n/10 iterations)'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  $(xs t.xs, acc (add acc ?:((is-prime:nz i.xs) 1 0)))
::
++  bench-crt
  =/  xs  (naturals n 1.000.000)
  ~&  '  crt:nz            four coprime moduli'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  =/  c  (crt:nz ~[[i.xs 7] [i.xs 11] [i.xs 13] [i.xs 17]])
  $(xs t.xs, acc (add acc r.c))
::
++  bench-ratrec
  =/  m=@ud   1.000.003
  =/  bd=@ud  (isqrt:nz (div (dec m) 2))
  =/  xs      (naturals n m)
  ~&  '  ratrec:nz         20-bit modulus'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  =/  u  (ratrec:nz i.xs m bd bd)
  $(xs t.xs, acc (add acc ?~(u 0 q.u.u)))
::
++  bench-qq-add
  =/  xs  (fracs n)
  =/  ys  (fracs n)
  ~&  '  add:qq'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  ?~  ys  acc
  $(xs t.xs, ys t.ys, acc (add acc q:(add:qq i.xs i.ys)))
::
++  bench-qq-mul
  =/  xs  (fracs n)
  =/  ys  (fracs n)
  ~&  '  mul:qq'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  ?~  ys  acc
  $(xs t.xs, ys t.ys, acc (add acc q:(mul:qq i.xs i.ys)))
::
++  bench-qq-div
  =/  xs  (fracs n)
  =/  ys  (fracs n)
  ~&  '  div:qq'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  ?~  ys  acc
  ::  skip zero divisors: +div crashes on them by SPEC S8
  ?:  =(--0 p.i.ys)  $(xs t.xs, ys t.ys)
  $(xs t.xs, ys t.ys, acc (add acc q:(div:qq i.xs i.ys)))
::
++  bench-qq-cmp
  =/  xs  (fracs n)
  =/  ys  (fracs n)
  ~&  '  cmp:qq'
  ~>  %bout
  =|  acc=@
  |-  ^-  @
  ?~  xs  acc
  ?~  ys  acc
  $(xs t.xs, ys t.ys, acc (add acc ?:(=(%eq (cmp:qq i.xs i.ys)) 1 0)))
::
::    +zpoly:  a canonical zol of the given degree, from the pinned seed
::
::  Every coefficient is drawn from [off+1, off+1.000.001), hence strictly
::  positive, so the leading coefficient is nonzero and the list is canonical
::  by construction.  +zx arms require canonical input (R5), so a supply that
::  could end in --0 would be feeding them out-of-domain values.
++  zpoly
  |=  [d=@ud off=@ud]
  ^-  zol
  %+  turn  (naturals-from +(d) +(off) 1.000.000)
  |=(c=@ud ^-(@s (sun:si c)))
::
::    +polynomial-rows:  the SPEC S11.4 polynomial timings
::
::  Phase 1 supplies +zx arithmetic, timed below.  The rows S11.4 names by
::  degree -- mul:mx and gcd:mx at 16/64/256 over a 61-bit F_p, gcd:zx at
::  degree 64, factor:zx at degree 32 -- need arms from Phases 1-3 that do
::  not exist yet, and are not faked here.
++  polynomial-rows
  ^-  @
  =/  a16   (zpoly 16 0)
  =/  b16   (zpoly 16 7)
  =/  a64   (zpoly 64 0)
  =/  b64   (zpoly 64 7)
  =/  a256  (zpoly 256 0)
  =/  b256  (zpoly 256 7)
  =/  p  (bench-zx-mul a16 b16 '  mul:zx            degree 16   (n iter)' n)
  =/  q
    (bench-zx-mul a64 b64 '  mul:zx            degree 64   (n/10)' (div n 10))
  =/  r  (bench-zx-mul a256 b256 '  mul:zx            degree 256  (1 iter)' 1)
  =/  s  (bench-zx-add a64 b64 '  add:zx            degree 64   (n iter)' n)
  :(add p q r s)
::
++  bench-zx-mul
  |=  [a=zol b=zol label=@t count=@ud]
  ^-  @
  ~&  label
  ~>  %bout
  =|  acc=@
  =/  i=@ud  count
  |-  ^-  @
  ?:  =(0 i)  acc
  $(i (dec i), acc (add acc (lent (mul:zx a b))))
::
++  bench-zx-add
  |=  [a=zol b=zol label=@t count=@ud]
  ^-  @
  ~&  label
  ~>  %bout
  =|  acc=@
  =/  i=@ud  count
  |-  ^-  @
  ?:  =(0 i)  acc
  $(i (dec i), acc (add acc (lent (add:zx a b))))
--
