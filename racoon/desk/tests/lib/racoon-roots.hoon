  ::  /tests/lib/racoon
::::  Racoon test suite
::
::  Phase 0: scalars and elementary number theory (+nz, +qq).
::
::  Naming: ++test-p0-* for Phase 0.  Every crash row in SPEC S8 that names a
::  Phase 0 arm has a dedicated ++test-p0-crash-* arm.  Property tests drive
::  ++og from the pinned literal seeds recorded below.
::
/-  *racoon
/+  *test, racoon, vec=racoon-vectors, fmt=racoon-fmt, rs=racoon-rs
/+  fp=racoon-fp3
/+  zf=racoon-zfac
/+  rr=racoon-roots
/+  al=racoon-alg
=/  nz  nz:racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  mx  mx:racoon
=/  qx  qx:racoon
::  doors at primes, a composite, and the smallest modulus
=/  m7   ~(. mx 7)
=/  m6   ~(. mx 6)
=/  m3   ~(. mx 3)
=/  m2   ~(. mx 2)
::  and at the Goldilocks prime, for the extension field tests
=/  mgl  ~(. mx 18.446.744.069.414.584.321)
|%
::    +rng:  a bounded stream of naturals from a pinned seed
::
::  [seed=@ n=@ud hi=@ud] -> (list @ud), n values each in [0, hi).
::  Sizes stay small so the interpreted suite runs in tolerable time.
++  rng
  |=  [seed=@ n=@ud hi=@ud]
  ^-  (list @ud)
  =/  gen  ~(. og seed)
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  =(0 n)  (flop out)
  =^  r  gen  (rads:gen hi)
  $(n (dec n), out [r out])
::    +pairs:  zip a flat list into pairs
++  pairs
  |=  a=(list @ud)
  ^-  (list [@ud @ud])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.t.a)]
::    +divides:  does a divide b?
++  divides
  |=  [a=@ud b=@ud]
  ^-  ?
  ?:  =(0 a)  =(0 b)
  =(0 (mod b a))
::    +to-zol:  build a canonical zol from a list of naturals
::
::  The top coefficient is forced nonzero, so the result is canonical by
::  construction.  Deliberately does NOT call +canon:zx: property tests must
::  not depend on the arm they would otherwise be exercising.
++  to-zol
  |=  cs=(list @ud)
  ^-  zol
  =/  ss=zol
    %+  turn  cs
    |=(c=@ud ^-(@s (dif:si (sun:si (mod c 41)) --20)))
  =/  rs=zol  (flop ss)
  ?~  rs  ~
  (flop [?:(=(--0 i.rs) --1 i.rs) t.rs])
::    +to-mol:  reduce a zol into a canonical mol modulo n
::
::  Note that ++dul:si is NOT usable here: it computes (sub b +.c) for a
::  negative operand, which underflows whenever the magnitude exceeds n, and
::  the supply below reaches 20 against moduli as small as 2.  Reducing the
::  magnitude first is what makes this total.
::
::  Trailing zeros are dropped locally rather than through +canon:mx, so the
::  property tests do not depend on the arm they would be exercising.
++  to-mol
  |=  [a=zol n=@ud]
  ^-  mol
  =/  cs=(list @ud)
    %+  turn  a
    |=  c=@s
    ^-  @ud
    =/  m=@ud  (mod (abs:si c) n)
    ?:  (syn:si c)  m
    (mod (sub n m) n)
  =/  r=(list @ud)  (flop cs)
  |-  ^-  mol
  ?~  r  ~
  ?:  =(0 i.r)  $(r t.r)
  (flop r)
::    +tderiv:  formal derivative over Z, for the test suite
::
::  The library's +zderiv lives in the private +pv core and is not reachable
::  from here.  Recomputing it independently is the right thing anyway: a
::  squarefreeness check that borrowed the library's own derivative would be
::  checking less than it appears to.
++  tderiv
  |=  a=zol
  ^-  zol
  ?~  a  ~
  =/  cs=zol  t.a
  =/  k=@ud   1
  =|  out=zol
  |-  ^-  zol
  ?~  cs  (flop out)
  $(cs t.cs, k +(k), out [(pro:si (sun:si k) i.cs) out])
::    +ipow:  integer power, for checking the pseudo-division identity
::
::  The library's own +pows lives in the private +pv core, which is not
::  reachable from here -- correctly, since it is not public API.  Repeated
::  multiplication is the honest check anyway: it shares no code with the
::  square-and-multiply the library uses.
++  ipow
  |=  [b=@s e=@ud]
  ^-  @s
  ?:  =(0 e)  --1
  (pro:si b $(e (dec e)))
::    +to-qol:  embed a zol into Q[x] with varied denominators
::
::  Denominators are derived from the coefficient index, so the supply
::  exercises genuine fractions rather than integers-as-rationals.  Uses
::  +new:qq to canonicalize, which is a Phase 0 arm and so not under test
::  here; trailing zeros are dropped locally rather than via +canon:qx.
++  to-qol
  |=  a=zol
  ^-  qol
  =/  cs=(list frac)
    =/  xs=zol  a
    =/  i=@ud   1
    =|  out=(list frac)
    |-  ^-  (list frac)
    ?~  xs  (flop out)
    $(xs t.xs, i +(i), out [(new:qq i.xs (add 1 (mod i 5))) out])
  =/  r=(list frac)  (flop cs)
  |-  ^-  qol
  ?~  r  ~
  ?:  =(--0 p.i.r)  $(r t.r)
  (flop r)
::    +zols:  a deterministic supply of canonical polynomials
++  zols
  |=  [seed=@ count=@ud]
  ^-  (list zol)
  =/  ns=(list @ud)  (rng seed (mul count 6) 100)
  =|  out=(list zol)
  =/  i=@ud  0
  |-  ^-  (list zol)
  ?:  =(i count)  (flop out)
  $(i +(i), ns (slag 6 ns), out [(to-zol (scag +((mod i 5)) ns)) out])
::    +zpairs:  sliding window of consecutive pairs
++  zpairs
  |=  a=(list zol)
  ^-  (list [zol zol])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.a)]
::    +ztriples:  sliding window of consecutive triples
++  ztriples
  |=  a=(list zol)
  ^-  (list [zol zol zol])
  ?~  a  ~
  ?~  t.a  ~
  ?~  t.t.a  ~
  [[i.a i.t.a i.t.t.a] $(a t.a)]
::  Vector-driven arms below all follow one shape: +skip the cases whose
::  computed value matches the oracle's, then expect the empty list.  A
::  regression therefore names every failing case, rather than stopping at
::  the first one.
::
++  strictly-down
  |=  ks=(list @ud)
  ^-  ?
  ?~  ks  %.y
  =/  prev=@ud         i.ks
  =/  rest=(list @ud)  t.ks
  |-  ^-  ?
  ?~  rest  %.y
  ?.  (lth i.rest prev)  %.n
  $(rest t.rest, prev i.rest)
::  Real-root data from SymPy: the derivative, the Cauchy bound as
::  SPEC R3 pins it, and the count of DISTINCT real roots -- which is
::  what Poly.count_roots returns, confirmed against (x-1)^2(x+2)
::  giving 2 and not 3 before any of this was pinned (SPEC R7/11.3).
++  rrvecs
  ^-  (list [p=zol dv=zol bd=frac nr=@ud])
  :~
    :*  ~[--0 --1]
        ~[--1]
        [--1 1]
        1
    ==
    :*  ~[-3 --2]
        ~[--2]
        [--5 2]
        1
    ==
    :*  ~[-1 --0 --1]
        ~[--0 --2]
        [--2 1]
        2
    ==
    :*  ~[--1 --0 --1]
        ~[--0 --2]
        [--2 1]
        0
    ==
    :*  ~[-2 --0 --1]
        ~[--0 --2]
        [--3 1]
        2
    ==
    :*  ~[--0 -1 --0 --1]
        ~[-1 --0 --3]
        [--2 1]
        3
    ==
    :*  ~[-2 --0 --0 --1]
        ~[--0 --0 --3]
        [--3 1]
        1
    ==
    :*  ~[--0 -2 --1 --1]
        ~[-2 --2 --3]
        [--3 1]
        3
    ==
    :*  ~[--2 -3 --0 --1]
        ~[-3 --0 --3]
        [--4 1]
        2
    ==
    :*  ~[-1 --0 --0 --0 --1]
        ~[--0 --0 --0 --4]
        [--2 1]
        2
    ==
    :*  ~[--1 --0 --0 --0 --1]
        ~[--0 --0 --0 --4]
        [--2 1]
        0
    ==
    :*  ~[--24 -50 --35 -10 --1]
        ~[-50 --70 -30 --4]
        [--51 1]
        4
    ==
    :*  ~[--1 --0 -10 --0 --1]
        ~[--0 -20 --0 --4]
        [--11 1]
        4
    ==
    :*  ~[--576 --0 -960 --0 --352 --0 -40 --0 --1]
        ~[--0 -1.920 --0 --1.408 --0 -240 --0 --8]
        [--961 1]
        8
    ==
    :*  ~[--0 --5 --0 -20 --0 --16]
        ~[--5 --0 -60 --0 --80]
        [--9 4]
        5
    ==
    :*  ~[--1 --0 -32 --0 --160 --0 -256 --0 --128]
        ~[--0 -64 --0 --640 --0 -1.536 --0 --1.024]
        [--3 1]
        8
    ==
    :*  ~[--1 --1 --1 --1 --1]
        ~[--1 --2 --3 --4]
        [--2 1]
        0
    ==
    :*  ~[--1 --1 --1]
        ~[--1 --2]
        [--2 1]
        0
    ==
    :*  ~[--1 -3 --0 --0 --0 --1]
        ~[-3 --0 --0 --0 --5]
        [--4 1]
        3
    ==
    :*  ~[--3 -6 --3]
        ~[-6 --6]
        [--3 1]
        1
    ==
    :*  ~[--1 --1 --1]
        ~[--1 --2]
        [--2 1]
        0
    ==
    :*  ~[--0 --1 --0 -1]
        ~[--1 --0 -3]
        [--2 1]
        3
    ==
    :*  ~[--4 --0 -4 --0 --1]
        ~[--0 -8 --0 --4]
        [--5 1]
        2
    ==
    :*  ~[-1 --0 --0 --0 --0 --0 --1]
        ~[--0 --0 --0 --0 --0 --6]
        [--2 1]
        2
    ==
    :*  ~[-14 --7]
        ~[--7]
        [--3 1]
        1
    ==
    :*  ~[--5]
        ~
        [--1 1]
        0
    ==
    :*  ~[-3]
        ~
        [--1 1]
        0
    ==
  ==
::  Root counts on half-open ranges (a, b].  Endpoints are chosen off
::  the root set, so SymPy's INCLUSIVE count_roots agrees with the
::  half-open convention here -- a difference that would otherwise be
::  silent.  Squarefree inputs only, which is +count's precondition.
++  cntvecs
  ^-  (list [p=zol a=frac b=frac k=@ud])
  :~
    [~[--0 --1] [-5 1] [-3 2] 0]
    [~[--0 --1] [-3 2] [-1 2] 0]
    [~[--0 --1] [-1 2] [--1 3] 1]
    [~[--0 --1] [--1 3] [--3 2] 0]
    [~[--0 --1] [--3 2] [--5 2] 0]
    [~[--0 --1] [--5 2] [--7 1] 0]
    [~[-3 --2] [-5 1] [-3 2] 0]
    [~[-3 --2] [-3 2] [-1 2] 0]
    [~[-3 --2] [-1 2] [--1 3] 0]
    [~[-3 --2] [--5 2] [--7 1] 0]
    [~[-1 --0 --1] [-5 1] [-3 2] 0]
    [~[-1 --0 --1] [-3 2] [-1 2] 1]
    [~[-1 --0 --1] [-1 2] [--1 3] 0]
    [~[-1 --0 --1] [--1 3] [--3 2] 1]
    [~[-1 --0 --1] [--3 2] [--5 2] 0]
    [~[-1 --0 --1] [--5 2] [--7 1] 0]
    [~[--1 --0 --1] [-5 1] [-3 2] 0]
    [~[--1 --0 --1] [-3 2] [-1 2] 0]
    [~[--1 --0 --1] [-1 2] [--1 3] 0]
    [~[--1 --0 --1] [--1 3] [--3 2] 0]
    [~[--1 --0 --1] [--3 2] [--5 2] 0]
    [~[--1 --0 --1] [--5 2] [--7 1] 0]
    [~[-2 --0 --1] [-5 1] [-3 2] 0]
    [~[-2 --0 --1] [-3 2] [-1 2] 1]
    [~[-2 --0 --1] [-1 2] [--1 3] 0]
    [~[-2 --0 --1] [--1 3] [--3 2] 1]
    [~[-2 --0 --1] [--3 2] [--5 2] 0]
    [~[-2 --0 --1] [--5 2] [--7 1] 0]
    [~[--0 -1 --0 --1] [-5 1] [-3 2] 0]
    [~[--0 -1 --0 --1] [-3 2] [-1 2] 1]
    [~[--0 -1 --0 --1] [-1 2] [--1 3] 1]
    [~[--0 -1 --0 --1] [--1 3] [--3 2] 1]
    [~[--0 -1 --0 --1] [--3 2] [--5 2] 0]
    [~[--0 -1 --0 --1] [--5 2] [--7 1] 0]
    [~[-2 --0 --0 --1] [-5 1] [-3 2] 0]
    [~[-2 --0 --0 --1] [-3 2] [-1 2] 0]
    [~[-2 --0 --0 --1] [-1 2] [--1 3] 0]
    [~[-2 --0 --0 --1] [--1 3] [--3 2] 1]
    [~[-2 --0 --0 --1] [--3 2] [--5 2] 0]
    [~[-2 --0 --0 --1] [--5 2] [--7 1] 0]
    [~[--0 -2 --1 --1] [-5 1] [-3 2] 1]
    [~[--0 -2 --1 --1] [-3 2] [-1 2] 0]
    [~[--0 -2 --1 --1] [-1 2] [--1 3] 1]
    [~[--0 -2 --1 --1] [--1 3] [--3 2] 1]
    [~[--0 -2 --1 --1] [--3 2] [--5 2] 0]
    [~[--0 -2 --1 --1] [--5 2] [--7 1] 0]
    [~[-1 --0 --0 --0 --1] [-5 1] [-3 2] 0]
    [~[-1 --0 --0 --0 --1] [-3 2] [-1 2] 1]
    [~[-1 --0 --0 --0 --1] [-1 2] [--1 3] 0]
    [~[-1 --0 --0 --0 --1] [--1 3] [--3 2] 1]
    [~[-1 --0 --0 --0 --1] [--3 2] [--5 2] 0]
    [~[-1 --0 --0 --0 --1] [--5 2] [--7 1] 0]
    [~[--1 --0 --0 --0 --1] [-5 1] [-3 2] 0]
    [~[--1 --0 --0 --0 --1] [-3 2] [-1 2] 0]
    [~[--1 --0 --0 --0 --1] [-1 2] [--1 3] 0]
    [~[--1 --0 --0 --0 --1] [--1 3] [--3 2] 0]
    [~[--1 --0 --0 --0 --1] [--3 2] [--5 2] 0]
    [~[--1 --0 --0 --0 --1] [--5 2] [--7 1] 0]
    [~[--24 -50 --35 -10 --1] [-5 1] [-3 2] 0]
    [~[--24 -50 --35 -10 --1] [-3 2] [-1 2] 0]
    [~[--24 -50 --35 -10 --1] [-1 2] [--1 3] 0]
    [~[--24 -50 --35 -10 --1] [--1 3] [--3 2] 1]
    [~[--24 -50 --35 -10 --1] [--3 2] [--5 2] 1]
    [~[--24 -50 --35 -10 --1] [--5 2] [--7 1] 2]
    [~[--1 --0 -10 --0 --1] [-5 1] [-3 2] 1]
    [~[--1 --0 -10 --0 --1] [-3 2] [-1 2] 0]
    [~[--1 --0 -10 --0 --1] [-1 2] [--1 3] 2]
    [~[--1 --0 -10 --0 --1] [--1 3] [--3 2] 0]
    [~[--1 --0 -10 --0 --1] [--3 2] [--5 2] 0]
    [~[--1 --0 -10 --0 --1] [--5 2] [--7 1] 1]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] [-5 1] [-3 2] 2]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] [-3 2] [-1 2] 1]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] [-1 2] [--1 3] 0]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] [--1 3] [--3 2] 1]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] [--3 2] [--5 2] 1]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] [--5 2] [--7 1] 2]
    [~[--0 --5 --0 -20 --0 --16] [-5 1] [-3 2] 0]
    [~[--0 --5 --0 -20 --0 --16] [-3 2] [-1 2] 2]
    [~[--0 --5 --0 -20 --0 --16] [-1 2] [--1 3] 1]
    [~[--0 --5 --0 -20 --0 --16] [--1 3] [--3 2] 2]
    [~[--0 --5 --0 -20 --0 --16] [--3 2] [--5 2] 0]
    [~[--0 --5 --0 -20 --0 --16] [--5 2] [--7 1] 0]
    [~[--1 --0 -32 --0 --160 --0 -256 --0 --128] [-5 1] [-3 2] 0]
    [~[--1 --0 -32 --0 --160 --0 -256 --0 --128] [-3 2] [-1 2] 3]
    [~[--1 --0 -32 --0 --160 --0 -256 --0 --128] [-1 2] [--1 3] 2]
    [~[--1 --0 -32 --0 --160 --0 -256 --0 --128] [--1 3] [--3 2] 3]
    [~[--1 --0 -32 --0 --160 --0 -256 --0 --128] [--3 2] [--5 2] 0]
    [~[--1 --0 -32 --0 --160 --0 -256 --0 --128] [--5 2] [--7 1] 0]
    [~[--1 --1 --1 --1 --1] [-5 1] [-3 2] 0]
    [~[--1 --1 --1 --1 --1] [-3 2] [-1 2] 0]
    [~[--1 --1 --1 --1 --1] [-1 2] [--1 3] 0]
    [~[--1 --1 --1 --1 --1] [--1 3] [--3 2] 0]
    [~[--1 --1 --1 --1 --1] [--3 2] [--5 2] 0]
    [~[--1 --1 --1 --1 --1] [--5 2] [--7 1] 0]
    [~[--1 --1 --1] [-5 1] [-3 2] 0]
    [~[--1 --1 --1] [-3 2] [-1 2] 0]
    [~[--1 --1 --1] [-1 2] [--1 3] 0]
    [~[--1 --1 --1] [--1 3] [--3 2] 0]
    [~[--1 --1 --1] [--3 2] [--5 2] 0]
    [~[--1 --1 --1] [--5 2] [--7 1] 0]
    [~[--1 -3 --0 --0 --0 --1] [-5 1] [-3 2] 0]
    [~[--1 -3 --0 --0 --0 --1] [-3 2] [-1 2] 1]
    [~[--1 -3 --0 --0 --0 --1] [-1 2] [--1 3] 0]
    [~[--1 -3 --0 --0 --0 --1] [--1 3] [--3 2] 2]
    [~[--1 -3 --0 --0 --0 --1] [--3 2] [--5 2] 0]
    [~[--1 -3 --0 --0 --0 --1] [--5 2] [--7 1] 0]
    [~[--1 --1 --1] [-5 1] [-3 2] 0]
    [~[--1 --1 --1] [-3 2] [-1 2] 0]
    [~[--1 --1 --1] [-1 2] [--1 3] 0]
    [~[--1 --1 --1] [--1 3] [--3 2] 0]
    [~[--1 --1 --1] [--3 2] [--5 2] 0]
    [~[--1 --1 --1] [--5 2] [--7 1] 0]
    [~[--0 --1 --0 -1] [-5 1] [-3 2] 0]
    [~[--0 --1 --0 -1] [-3 2] [-1 2] 1]
    [~[--0 --1 --0 -1] [-1 2] [--1 3] 1]
    [~[--0 --1 --0 -1] [--1 3] [--3 2] 1]
    [~[--0 --1 --0 -1] [--3 2] [--5 2] 0]
    [~[--0 --1 --0 -1] [--5 2] [--7 1] 0]
    [~[-1 --0 --0 --0 --0 --0 --1] [-5 1] [-3 2] 0]
    [~[-1 --0 --0 --0 --0 --0 --1] [-3 2] [-1 2] 1]
    [~[-1 --0 --0 --0 --0 --0 --1] [-1 2] [--1 3] 0]
    [~[-1 --0 --0 --0 --0 --0 --1] [--1 3] [--3 2] 1]
    [~[-1 --0 --0 --0 --0 --0 --1] [--3 2] [--5 2] 0]
    [~[-1 --0 --0 --0 --0 --0 --1] [--5 2] [--7 1] 0]
    [~[-14 --7] [-5 1] [-3 2] 0]
    [~[-14 --7] [-3 2] [-1 2] 0]
    [~[-14 --7] [-1 2] [--1 3] 0]
    [~[-14 --7] [--1 3] [--3 2] 0]
    [~[-14 --7] [--3 2] [--5 2] 1]
    [~[-14 --7] [--5 2] [--7 1] 0]
  ==
::
::  Real-root isolation, phase R0 (/lib/racoon-roots).  The correctness
::  core: an EXACT count of the distinct real roots in a rational range.
::  Everything phase R2 will add is bookkeeping on a count already right,
::  so this is the layer worth over-testing.
::
::  The adversarial family here is different from Milestone A's.  SD_3 is
::  in the corpus for factorization because Zassenhaus recombination is
::  exponential on it; it is here because its eight real roots sit in a
::  narrow band, which is what defeats a careless isolator.  Chebyshev
::  polynomials have every root real in (-1, 1); cyclotomics have none.
::
++  test-r0-bound
  =/  vs  rrvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  expect-eq  !>(`frac`bd.i.vs)  !>((bound:rr p.i.vs))
  ==
++  test-r0-deriv
  =/  vs  rrvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq  !>(`zol`dv.i.vs)  !>((deriv:zx p.i.vs))
        ::  the derivative drops the degree by exactly one, or vanishes
        %-  expect
        !>  ?:  =(~ dv.i.vs)  =(0 (deg:zx p.i.vs))
            =(+((deg:zx dv.i.vs)) (deg:zx p.i.vs))
      ==
  ==
++  test-r0-nroots
  =/  vs  rrvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq  !>(`@ud`nr.i.vs)  !>((nroots:rr p.i.vs))
        ::  distinct real roots never exceed the degree
        %-  expect  !>((lte nr.i.vs (deg:zx p.i.vs)))
        ::  and are unchanged by taking the squarefree part, which is the
        ::  whole point of counting DISTINCT roots
        %+  expect-eq
          !>(`@ud`nr.i.vs)
        !>((nroots:rr (sqpart:rr p.i.vs)))
      ==
  ==
++  test-r0-count
  =/  vs  cntvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  expect-eq  !>(`@ud`k.i.vs)
      !>((count:rr p.i.vs a.i.vs b.i.vs))
  ==
++  test-r0-count-additive
  ::  counting is additive over adjacent ranges and empty on a point,
  ::  which no oracle is needed to check
  =/  ps=(list zol)
    :~  ~[--0 --1]
        ~[-1 --0 --1]
        ~[--0 -1 --0 --1]
        ~[--1 --0 -10 --0 --1]
        ~[--576 --0 -960 --0 --352 --0 -40 --0 --1]
    ==
  ::  +-10 and not +-5: SD_3's roots are +-(sqrt2 + sqrt3 + sqrt5), about
  ::  +-5.382, so a narrower range genuinely excludes one -- which +count
  ::  reported correctly and this test had wrong.  None of these
  ::  polynomials vanishes at -10, 1/3, or 10.
  =/  a=frac  [-10 1]
  =/  b=frac  [--1 3]
  =/  c=frac  [--10 1]
  =|  out=tang
  |-  ^-  tang
  ?~  ps  out
  =/  p=zol  i.ps
  %=  $
    ps  t.ps
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq
          !>((count:rr p a c))
        !>((add (count:rr p a b) (count:rr p b c)))
        ::  a degenerate range holds nothing, and does not crash
        %+  expect-eq  !>(`@ud`0)  !>((count:rr p b b))
        (expect-success |.((count:rr p b b)))
        ::  the whole line agrees with +nroots
        %+  expect-eq  !>((nroots:rr p))  !>((count:rr p a c))
      ==
  ==
++  test-r0-sturm
  =/  p=zol  ~[--0 -1 --0 --1]
  =/  ch     (sturm:rr p)
  ;:  weld
    ::  the chain opens with p and p'
    %+  expect-eq  !>(`zol`p)             !>((snag 0 ch))
    %+  expect-eq  !>((deriv:zx p))       !>((snag 1 ch))
    ::  x^3 - x: chain is p, 3x^2-1, then a positive multiple of 2x/3,
    ::  reduced to its primitive part, then a nonzero constant
    %+  expect-eq  !>(`@ud`4)             !>((lent ch))
    %+  expect-eq  !>(`zol`~[--0 --1])    !>((snag 2 ch))
    ::  degrees strictly decrease, which is what makes it terminate
    %-  expect  !>((strictly-down (turn ch |=(q=zol (deg:zx q)))))
    ::  and the last term is a nonzero constant, since p is squarefree
    %+  expect-eq  !>(`@ud`0)             !>((deg:zx (rear ch)))
    ::  a linear polynomial has the shortest possible chain
    %+  expect-eq  !>(`@ud`2)  !>((lent (sturm:rr ~[-3 --2])))
    ::  a constant has a chain of one, and no roots
    %+  expect-eq  !>(`@ud`1)  !>((lent (sturm:rr ~[--5])))
    %+  expect-eq  !>(`@ud`0)  !>((nroots:rr ~[--5]))
  ==
++  test-r0-sign-at
  =/  p=zol  ~[-2 --0 --1]
  ;:  weld
    ::  x^2 - 2 at 0, 2, -2, and at the rationals bracketing sqrt(2)
    %+  expect-eq  !>(`ord`%lt)  !>((sign-at:rr p [--0 1]))
    %+  expect-eq  !>(`ord`%gt)  !>((sign-at:rr p [--2 1]))
    %+  expect-eq  !>(`ord`%gt)  !>((sign-at:rr p [-2 1]))
    %+  expect-eq  !>(`ord`%lt)  !>((sign-at:rr p [--7 5]))
    %+  expect-eq  !>(`ord`%gt)  !>((sign-at:rr p [--3 2]))
    ::  %eq is exact, not a tolerance: 2x - 3 vanishes at 3/2 and nowhere
    ::  a floating-point test would confuse with it
    %+  expect-eq  !>(`ord`%eq)  !>((sign-at:rr ~[-3 --2] [--3 2]))
    %+  expect-eq  !>(`ord`%lt)
    !>((sign-at:rr ~[-3 --2] [--14.999 10.000]))
    %+  expect-eq  !>(`ord`%gt)
    !>((sign-at:rr ~[-3 --2] [--15.001 10.000]))
  ==
++  test-r0-crash
  ;:  weld
    ::  the zero polynomial: every real is a root, so there is no answer
    ::  to give and no sentinel that would not be a lie
    (expect-fail |.((bound:rr ~)))
    ::  +deriv MOVED to %zx (SPEC-QUESTIONS R1) and is TOTAL there:
    ::  the derivative of the zero polynomial is the zero polynomial.
    ::  R5's "any arm crashes on ~" covers the arms of THIS library,
    ::  and +deriv is no longer one of them.
    %+  expect-eq  !>(`zol`~)  !>((deriv:zx ~))
    (expect-fail |.((sign-at:rr ~ [--0 1])))
    (expect-fail |.((sturm:rr ~)))
    (expect-fail |.((nroots:rr ~)))
    (expect-fail |.((sqpart:rr ~)))
    (expect-fail |.((count:rr ~ [--0 1] [--1 1])))
    ::  +sturm and +count require a squarefree input: the chain's count is
    ::  valid only there, and a silently wrong count is worse than a crash
    (expect-fail |.((sturm:rr ~[--2 -3 --0 --1])))
    (expect-fail |.((count:rr ~[--2 -3 --0 --1] [--0 1] [--2 1])))
    %-  expect  !>(!(is-squarefree:rr ~[--2 -3 --0 --1]))
    ::  while +nroots takes the squarefree part itself and accepts it
    (expect-success |.((nroots:rr ~[--2 -3 --0 --1])))
    %+  expect-eq  !>(`@ud`2)  !>((nroots:rr ~[--2 -3 --0 --1]))
    ::  an inverted range
    (expect-fail |.((count:rr ~[--0 --1] [--1 1] [--0 1])))
    (expect-success |.((count:rr ~[--0 --1] [--0 1] [--1 1])))
    ::  a nonzero constant is squarefree and has no roots
    %-  expect  !>((is-squarefree:rr ~[--5]))
    (expect-success |.((bound:rr ~[--5])))
  ==
::    +ascending-q:  is this list of rationals strictly increasing?
++  ascending-q
  |=  fs=(list frac)
  ^-  ?
  ?~  fs  %.y
  =/  prev=frac         i.fs
  =/  rest=(list frac)  t.fs
  |-  ^-  ?
  ?~  rest  %.y
  ?.  =(%lt (cmp:qq prev i.rest))  %.n
  $(rest t.rest, prev i.rest)
::  Exact rational roots from SymPy's Poly.ground_roots, which
::  returns {root: multiplicity} over Q.  Ascending by value here,
::  which is the order SPEC R3 pins.
++  r1vecs
  ^-  (list [p=zol rs=(list [r=frac m=@ud])])
  :~
    [~[--0 --1] ~[[[--0 1] 1]]]
    [~[-3 --2] ~[[[--3 2] 1]]]
    [~[-1 --0 --1] ~[[[-1 1] 1] [[--1 1] 1]]]
    [~[--1 --0 --1] ~]
    [~[-2 --0 --1] ~]
    [~[--0 -1 --0 --1] ~[[[-1 1] 1] [[--0 1] 1] [[--1 1] 1]]]
    [~[-2 --0 --0 --1] ~]
    [~[--2 -3 --0 --1] ~[[[-2 1] 1] [[--1 1] 2]]]
    [~[-1 --3 -3 --1] ~[[[--1 1] 3]]]
    [~[--0 --0 -3 --1] ~[[[--0 1] 2] [[--3 1] 1]]]
    [~[--0 --0 --0 --4 --4 --1] ~[[[-2 1] 2] [[--0 1] 3]]]
    [~[--1 -5 --6] ~[[[--1 3] 1] [[--1 2] 1]]]
    [~[--1 -7 --12] ~[[[--1 4] 1] [[--1 3] 1]]]
    [~[-1 --0 --4] ~[[[-1 2] 1] [[--1 2] 1]]]
    [~[--1 -6 --9] ~[[[--1 3] 2]]]
    [~[--60 -7 -31 --6] ~[[[-4 3] 1] [[--3 2] 1] [[--5 1] 1]]]
    [~[--2 -2 -1 --1] ~[[[--1 1] 1]]]
    [~[-2 -8 -7 --4 --4] ~[[[-1 2] 2]]]
    [~[-1 --0 --0 --0 --1] ~[[[-1 1] 1] [[--1 1] 1]]]
    [~[--1 --0 --0 --0 --1] ~]
    :-  ~[--24 -50 --35 -10 --1]
    ~[[[--1 1] 1] [[--2 1] 1] [[--3 1] 1] [[--4 1] 1]]
    [~[--1 --0 -10 --0 --1] ~]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] ~]
    [~[--0 --5 --0 -20 --0 --16] ~[[[--0 1] 1]]]
    [~[--1 --1 --1 --1 --1] ~]
    [~[--1 --1 --1] ~]
    [~[--5] ~]
    [~[-3] ~]
    [~[-14 --7] ~[[[--2 1] 1]]]
    [~[--1 -3 --0 --0 --0 --1] ~]
    [~[-1 --0 --100] ~[[[-1 10] 1] [[--1 10] 1]]]
    [~[-1 --0 --0 --0 --0 --0 --1] ~[[[-1 1] 1] [[--1 1] 1]]]
    [~[-3 --8 --57 --8 --60] ~[[[-3 10] 1] [[--1 6] 1]]]
  ==
::
::  Phase R1: the exactly-rational roots.  These come back as EXACT
::  values, never as intervals -- which is the clause phase R2's canonical
::  isolation depends on, since dividing them out first removes the only
::  way a root could land on a subdivision boundary.
::
::  The candidate set is the divisors of the trailing and leading
::  coefficients, so this is where /lib/racoon-zfac earns its place: there
::  is no cheaper way to enumerate them.
::
++  test-r1-vectors
  =/  vs  r1vecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  expect-eq
        !>(`(list [r=frac m=@ud])`rs.i.vs)
      !>((rational-roots:rr p.i.vs))
  ==
++  test-r1-properties
  =/  vs  r1vecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  p=zol  p.i.vs
  =/  rs     (rational-roots:rr p)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  weld
        ;:  weld
          ::  ascending, strictly: a repeated candidate is folded into one
          ::  entry by its multiplicity rather than listed twice
          %-  expect  !>((ascending-q (turn rs |=([r=frac m=@ud] r))))
          ::  every multiplicity is at least one -- a root that divides
          ::  zero times is not reported at all
          %-  expect
          !>((levy (turn rs |=([r=frac m=@ud] m)) |=(m=@ud (gth m 0))))
          ::  the multiplicities sum to at most the degree
          %-  expect
          !>  %+  lte
                %+  roll  (turn rs |=([r=frac m=@ud] m))
                |=([x=@ud acc=@ud] (add x acc))
              (deg:zx p)
          ::  a rational root is a real root, so there are never more of
          ::  them than +nroots counts
          %-  expect  !>((lte (lent rs) (nroots:rr p)))
        ==
      ::  and each one really is a root -- exactly, by +sign-at
      =/  bs  rs
      |-  ^-  tang
      ?~  bs  ~
      %+  weld
        %+  expect-eq  !>(`ord`%eq)  !>((sign-at:rr p r.i.bs))
      $(bs t.bs)
  ==
++  test-r1-splits
  ::  when a polynomial splits completely over Q, every real root is
  ::  rational and the two counts must agree exactly
  =/  ps=(list zol)
    :~  ~[-1 --0 --1]
        ~[--2 -3 --0 --1]
        ~[--24 -50 --35 -10 --1]
        ~[--1 -5 --6]
        ~[--0 -3 --1]
        ~[--0 --0 --0 --1]
    ==
  =|  out=tang
  |-  ^-  tang
  ?~  ps  out
  =/  p=zol  i.ps
  %=  $
    ps  t.ps
    out
      %+  weld  out
      %+  expect-eq  !>((nroots:rr p))  !>((lent (rational-roots:rr p)))
  ==
++  test-r1-mixed
  ;:  weld
    ::  (x^2 - 2)(x - 1): three real roots, exactly one of them rational
    %+  expect-eq
      !>(`(list [r=frac m=@ud])`~[[[--1 1] 1]])
    !>((rational-roots:rr ~[--2 -2 -1 --1]))
    %+  expect-eq  !>(`@ud`3)  !>((nroots:rr ~[--2 -2 -1 --1]))
    ::  a fractional root with multiplicity, alongside irrational ones:
    ::  (x^2 - 2)(2x + 1)^2
    %+  expect-eq
      !>(`(list [r=frac m=@ud])`~[[[-1 2] 2]])
    !>((rational-roots:rr ~[-2 -8 -7 --4 --4]))
    ::  0 is found by the x^k split, not by the divisor search, since the
    ::  rational root theorem is vacuous when a_0 = 0
    %+  expect-eq
      !>(`(list [r=frac m=@ud])`~[[[-2 1] 2] [[--0 1] 3]])
    !>((rational-roots:rr ~[--0 --0 --0 --4 --4 --1]))
    ::  a root outside the +-1 range of the constant term, which only the
    ::  leading-coefficient divisors can reach: (6x - 1)(10x + 3)(x^2 + 1)
    %+  expect-eq
      !>(`(list [r=frac m=@ud])`~[[[-3 10] 1] [[--1 6] 1]])
    !>((rational-roots:rr ~[-3 --8 --57 --8 --60]))
  ==
++  test-r1-crash
  ;:  weld
    ::  the zero polynomial, as everywhere else here
    (expect-fail |.((rational-roots:rr ~)))
    ::  a constant has no roots, and does not crash -- note this reaches
    ::  neither +divisors nor the x^k split
    %+  expect-eq  !>(`(list [r=frac m=@ud])`~)  !>((rational-roots:rr ~[--5]))
    %+  expect-eq  !>(`(list [r=frac m=@ud])`~)  !>((rational-roots:rr ~[-3]))
    (expect-success |.((rational-roots:rr ~[--5])))
    ::  nor does a polynomial whose roots are all irrational
    %+  expect-eq  !>(`(list [r=frac m=@ud])`~)
    !>((rational-roots:rr ~[-2 --0 --1]))
    ::  or complex
    %+  expect-eq  !>(`(list [r=frac m=@ud])`~)
    !>((rational-roots:rr ~[--1 --0 --1]))
    ::  x^k alone: the only root is 0, found without any divisor search
    %+  expect-eq
      !>(`(list [r=frac m=@ud])`~[[[--0 1] 4]])
    !>((rational-roots:rr ~[--0 --0 --0 --0 --1]))
  ==
::  Real roots with multiplicities from SymPy's Poly.real_roots,
::  ascending.  .ms lists the multiplicity of each DISTINCT real root
::  in ascending order, so its length is +nroots and its sum is the
::  count of real roots with multiplicity.
++  r2vecs
  ^-  (list [p=zol ms=(list @ud)])
  :~
    [~[--0 --1] ~[1]]
    [~[-3 --2] ~[1]]
    [~[-1 --0 --1] ~[1 1]]
    [~[--1 --0 --1] ~]
    [~[-2 --0 --1] ~[1 1]]
    [~[--0 -1 --0 --1] ~[1 1 1]]
    [~[-2 --0 --0 --1] ~[1]]
    [~[--2 -3 --0 --1] ~[1 2]]
    [~[-1 --3 -3 --1] ~[3]]
    [~[--0 --0 -3 --1] ~[2 1]]
    [~[--0 --0 --0 --4 --4 --1] ~[2 3]]
    [~[--1 -5 --6] ~[1 1]]
    [~[--2 -2 -1 --1] ~[1 1 1]]
    [~[-2 -8 -7 --4 --4] ~[1 2 1]]
    [~[--4 --0 -4 --0 --1] ~[2 2]]
    [~[-1 --0 --0 --0 --1] ~[1 1]]
    [~[--1 --0 --0 --0 --1] ~]
    [~[--24 -50 --35 -10 --1] ~[1 1 1 1]]
    [~[--1 --0 -10 --0 --1] ~[1 1 1 1]]
    [~[--576 --0 -960 --0 --352 --0 -40 --0 --1] ~[1 1 1 1 1 1 1 1]]
    [~[--0 --5 --0 -20 --0 --16] ~[1 1 1 1 1]]
    [~[--1 --1 --1 --1 --1] ~]
    [~[--1 --1 --1] ~]
    [~[--5] ~]
    [~[--1 -3 --0 --0 --0 --1] ~[1 1 1]]
    [~[-1 --0 --0 --0 --0 --0 --1] ~[1 1]]
    [~[-1 --0 --100] ~[1 1]]
    [~[--6 --0 -5 --0 --1] ~[1 1 1 1]]
  ==
::
::  Phase R2: canonical isolation and refinement.
::
::  The strongest checks here need no oracle at all.  An interval isolates
::  a root exactly when +count says it holds one, and +count is R0, which
::  is already verified against SymPy -- so "does this interval bracket a
::  root" is answered exactly rather than by comparing floating-point
::  approximations, which is how this would be tested anywhere else.
::
::    +wid:  the width of an interval
++  wid  |=(iv=ivl:rr ^-(frac (sub:qq hi.iv lo.iv)))
::    +disjoint-asc:  are these intervals ascending and non-overlapping?
::
::  hi of each is at most lo of the next.  Touching at an endpoint is
::  allowed and unavoidable in a subdivision; what matters is that no two
::  intervals share an interior point.
++  disjoint-asc
  |=  ivs=(list ivl:rr)
  ^-  ?
  ?~  ivs  %.y
  =/  prev=ivl:rr         i.ivs
  =/  rest=(list ivl:rr)  t.ivs
  |-  ^-  ?
  ?~  rest  %.y
  ?.  ?!(=(%gt (cmp:qq hi.prev lo.i.rest)))  %.n
  $(rest t.rest, prev i.rest)
::
++  test-r2-isolate-values
  ;:  weld
    ::  x^2 - 2 has bound 3, so the tree of (-3, 3] splits once and each
    ::  half holds one root: the shallowest nodes are the halves
    %+  expect-eq
      !>(`(list ivl:rr)`~[[[-3 1] [--0 1]] [[--0 1] [--3 1]]])
    !>((isolate:rr ~[-2 --0 --1]))
    ::  x^3 - x has three rational roots, so all three come back EXACT
    %+  expect-eq
      !>(`(list ivl:rr)`~[[[-1 1] [-1 1]] [[--0 1] [--0 1]]])
    !>((scag 2 (isolate:rr ~[--0 -1 --0 --1])))
    %+  expect-eq  !>(`@ud`3)  !>((lent (isolate:rr ~[--0 -1 --0 --1])))
    ::  no real roots, and a constant: both ~ without crashing
    %+  expect-eq  !>(`(list ivl:rr)`~)  !>((isolate:rr ~[--1 --0 --1]))
    %+  expect-eq  !>(`(list ivl:rr)`~)  !>((isolate:rr ~[--5]))
    ::  a repeated factor is isolated once, not twice
    %+  expect-eq  !>(`@ud`2)  !>((lent (isolate:rr ~[--4 --0 -4 --0 --1])))
  ==
++  test-r2-isolate-properties
  =/  vs  r2vecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  p=zol           p.i.vs
  =/  ivs             (isolate:rr p)
  =/  q=zol           (sqpart:rr p)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  weld
        ;:  weld
          ::  one interval per distinct real root
          %+  expect-eq  !>((nroots:rr p))  !>((lent ivs))
          %+  expect-eq  !>((lent ms.i.vs))  !>((lent ivs))
          ::  ascending and pairwise non-overlapping
          %-  expect  !>((disjoint-asc ivs))
        ==
      ::  each interval holds EXACTLY ONE root -- checked by +count, not
      ::  by comparing approximations, and degenerate ones are exact hits
      =/  bs  ivs
      |-  ^-  tang
      ?~  bs  ~
      %+  weld
        ?:  =(%eq (cmp:qq lo.i.bs hi.i.bs))
          %+  expect-eq  !>(`ord`%eq)  !>((sign-at:rr q lo.i.bs))
        %+  expect-eq  !>(`@ud`1)
        !>((count:rr q lo.i.bs hi.i.bs))
      $(bs t.bs)
  ==
++  test-r2-isolate-rational
  ::  an interval is degenerate exactly when its root is rational -- the
  ::  two arms have to agree, and this is where they are checked against
  ::  each other rather than against an oracle
  =/  vs  r2vecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  p=zol   p.i.vs
  =/  ivs     (isolate:rr p)
  =/  rats    (rational-roots:rr p)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        ::  same count of degenerate intervals as rational roots
        %+  expect-eq
          !>((lent rats))
        !>((lent (skim ivs |=(iv=ivl:rr =(%eq (cmp:qq lo.iv hi.iv))))))
        ::  and the same values, in the same ascending order
        %+  expect-eq
          !>((turn rats |=([r=frac m=@ud] r)))
        !>  %+  turn
              (skim ivs |=(iv=ivl:rr =(%eq (cmp:qq lo.iv hi.iv))))
            |=(iv=ivl:rr lo.iv)
      ==
  ==
++  test-r2-refine
  =/  p=zol   ~[-2 --0 --1]
  =/  ivs     (isolate:rr p)
  =/  iv      (snag 1 ivs)
  ;:  weld
    ::  the starting interval is (0, 3], of width 3
    %+  expect-eq  !>(`frac`[--3 1])  !>((wid iv))
    ::  each bisection halves the width, exactly
    %+  expect-eq  !>(`frac`[--3 2])   !>((wid (refine:rr p iv 1)))
    %+  expect-eq  !>(`frac`[--3 8])   !>((wid (refine:rr p iv 3)))
    %+  expect-eq  !>(`frac`[--3 64])  !>((wid (refine:rr p iv 6)))
    ::  refining zero times is the identity
    %+  expect-eq  !>(`ivl:rr`iv)  !>((refine:rr p iv 0))
    ::  and refinement composes: 3 then 3 is 6
    %+  expect-eq
      !>((refine:rr p iv 6))
    !>((refine:rr p (refine:rr p iv 3) 3))
    ::  the root stays bracketed however far this goes
    %+  expect-eq  !>(`@ud`1)
    !>((count:rr p lo:(refine:rr p iv 10) hi:(refine:rr p iv 10)))
    ::  sqrt 2 to width 3/64: [45/32, 93/64], verified by bracketing
    %+  expect-eq
      !>(`ivl:rr`[[--45 32] [--93 64]])
    !>((refine:rr p iv 6))
    ::  a degenerate interval is already exact and does not move
    =/  z  (snag 0 (isolate:rr ~[--0 -1 --0 --1]))
    %+  expect-eq  !>(`ivl:rr`z)  !>((refine:rr ~[--0 -1 --0 --1] z 20))
  ==
++  test-r2-refine-properties
  ::  over the corpus: refining keeps exactly one root bracketed, and the
  ::  width falls by 2^k
  =/  vs  r2vecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  p=zol  p.i.vs
  =/  q=zol  (sqpart:rr p)
  =/  ivs    (isolate:rr p)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      =/  bs  ivs
      |-  ^-  tang
      ?~  bs  ~
      =/  rf  (refine:rr p i.bs 4)
      %+  weld
        ?:  =(%eq (cmp:qq lo.i.bs hi.i.bs))
          ::  degenerate: unchanged
          (expect-eq !>(`ivl:rr`i.bs) !>(`ivl:rr`rf))
        ;:  weld
          %+  expect-eq  !>(`@ud`1)  !>((count:rr q lo.rf hi.rf))
          %+  expect-eq  !>((mul:qq (wid i.bs) [--1 16]))  !>((wid rf))
          ::  and the narrowed interval sits inside the original
          %-  expect  !>(?!(=(%gt (cmp:qq lo.i.bs lo.rf))))
          %-  expect  !>(?!(=(%lt (cmp:qq hi.i.bs hi.rf))))
        ==
      $(bs t.bs)
  ==
++  test-r2-roots
  =/  vs  r2vecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  p=zol  p.i.vs
  =/  rts    (roots:rr p)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        ::  multiplicities match SymPy's, in ascending root order
        %+  expect-eq
          !>(`(list @ud)`ms.i.vs)
        !>((turn rts |=(r=rrt:rr m.r)))
        ::  the intervals are exactly +isolate's
        %+  expect-eq
          !>((isolate:rr p))
        !>((turn rts |=(r=rrt:rr iv.r)))
        ::  and counting with multiplicity never exceeds the degree
        %-  expect
        !>  %+  lte
              %+  roll  (turn rts |=(r=rrt:rr m.r))
              |=([x=@ud acc=@ud] (add x acc))
            (deg:zx p)
      ==
  ==
++  test-r2-crash
  ;:  weld
    (expect-fail |.((isolate:rr ~)))
    (expect-fail |.((roots:rr ~)))
    ::  a constant and a rootless polynomial both give ~, no crash
    %+  expect-eq  !>(`(list rrt:rr)`~)  !>((roots:rr ~[--5]))
    %+  expect-eq  !>(`(list rrt:rr)`~)  !>((roots:rr ~[--1 --0 --1]))
    (expect-success |.((isolate:rr ~[--5])))
    (expect-success |.((refine:rr ~[-2 --0 --1] [[--0 1] [--3 1]] 12)))
    ::  SD_3: eight real roots in a narrow band, all irrational, so none
    ::  of them collapses to a point
    %+  expect-eq  !>(`@ud`8)
    !>((lent (isolate:rr ~[--576 --0 -960 --0 --352 --0 -40 --0 --1])))
    %+  expect-eq  !>(`(list frac)`~)
    !>  %+  turn
          %+  skim  (isolate:rr ~[--576 --0 -960 --0 --352 --0 -40 --0 --1])
          |=(iv=ivl:rr =(%eq (cmp:qq lo.iv hi.iv)))
        |=(iv=ivl:rr lo.iv)
  ==
::
::  Milestone C phase A: real algebraic number arithmetic
::  (/lib/racoon-alg).
::
::  The oracle is SymPy's minimal_polynomial, which is exactly the
::  canonical form §A2 pins.  Verified before pinning, per §11.3:
::  minimal_polynomial(sqrt2 * sqrt3) is x^2 - 6, DEGREE 2 where the
::  resultant has degree 4.  A suite built only from degree-preserving
::  cases would pass with the factor-and-select step deleted, so the
::  collapsing cases below are the ones carrying the weight.
::
::  Kept to degrees 2 and 3 deliberately.  Two degree-4 numbers give a
::  degree-16 resultant, which is the SD_4 cliff §9 already fenced off
::  pending van Hoeij -- see SPEC A8.
::
::    +mkr:  the i-th real root of p, as an algebraic number
++  mkr
  |=  [p=zol i=@ud]
  ^-  anum:al
  (make:al p (snag i (isolate:rr p)))
::    +sq2:  the square root of 2
++  sq2  ^-(anum:al (mkr ~[-2 --0 --1] 1))
::    +sq3:  the square root of 3
++  sq3  ^-(anum:al (mkr ~[-3 --0 --1] 1))
::    +phi:  the golden ratio, (1 + sqrt 5) / 2
++  phi  ^-(anum:al (mkr ~[-1 -1 --1] 1))
::    +cb2:  the real cube root of 2
++  cb2  ^-(anum:al (mkr ~[-2 --0 --0 --1] 0))
::
--
