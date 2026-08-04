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
++  ascends
  |=  ks=(list @ud)
  ^-  ?
  ?~  ks  %.y
  =/  prev=@ud  i.ks
  =/  rest=(list @ud)  t.ks
  |-  ^-  ?
  ?~  rest  %.y
  ?.  (gth i.rest prev)  %.n
  $(rest t.rest, prev i.rest)
::  Integer factorizations from SymPy's factorint.  Unique, so these
::  are values and not a convention: any correct algorithm agrees.
++  zfvecs
  ^-  (list [n=@ud fs=(list [p=@ud m=@ud])])
  :~
    [1 ~]
    [2 ~[[2 1]]]
    [3 ~[[3 1]]]
    [4 ~[[2 2]]]
    [6 ~[[2 1] [3 1]]]
    [12 ~[[2 2] [3 1]]]
    [36 ~[[2 2] [3 2]]]
    [60 ~[[2 2] [3 1] [5 1]]]
    [97 ~[[97 1]]]
    [128 ~[[2 7]]]
    [243 ~[[3 5]]]
    [360 ~[[2 3] [3 2] [5 1]]]
    [561 ~[[3 1] [11 1] [17 1]]]
    [1.024 ~[[2 10]]]
    [1.105 ~[[5 1] [13 1] [17 1]]]
    [1.729 ~[[7 1] [13 1] [19 1]]]
    [2.465 ~[[5 1] [17 1] [29 1]]]
    [5.040 ~[[2 4] [3 2] [5 1] [7 1]]]
    [30.030 ~[[2 1] [3 1] [5 1] [7 1] [11 1] [13 1]]]
    [65.521 ~[[65.521 1]]]
    [65.536 ~[[2 16]]]
    [65.537 ~[[65.537 1]]]
    [999.983 ~[[999.983 1]]]
    [1.000.003 ~[[1.000.003 1]]]
    [2.147.483.647 ~[[2.147.483.647 1]]]
    [2.293.235.712 ~[[2 20] [3 7]]]
    [4.294.967.295 ~[[3 1] [5 1] [17 1] [257 1] [65.537 1]]]
    [10.967.535.067 ~[[104.723 1] [104.729 1]]]
    [12.884.901.873 ~[[3 1] [4.294.967.291 1]]]
    [13.000.000.091 ~[[13 1] [1.000.000.007 1]]]
    [68.718.821.377 ~[[131.071 1] [524.287 1]]]
    [99.999.999.977 ~[[99.999.999.977 1]]]
    [118.315.528.748 ~[[2 2] [19 1] [151 1] [10.309.823 1]]]
    [123.456.789.012 ~[[2 2] [3 1] [10.288.065.751 1]]]
    [202.119.580.278 ~[[2 1] [3 2] [7 1] [11 1] [83 1] [641 1] [2.741 1]]]
    [224.579.687.583 ~[[3 1] [19 1] [2.141 1] [1.840.259 1]]]
    [332.445.793.531 ~[[107 1] [541 1] [967 1] [5.939 1]]]
    [467.239.314.040 ~[[2 3] [5 1] [55.579 1] [210.169 1]]]
    [496.604.932.559 ~[[7.919 3]]]
    [557.971.263.438 ~[[2 1] [3 1] [19 1] [4.894.484.767 1]]]
    [600.851.475.143 ~[[71 1] [839 1] [1.471 1] [6.857 1]]]
    [649.146.163.835 ~[[5 1] [13 1] [757 1] [1.277 1] [10.331 1]]]
    [657.911.510.254 ~[[2 1] [282.703 1] [1.163.609 1]]]
    [999.999.999.989 ~[[999.999.999.989 1]]]
  ==
::  Totient, divisor count, radical, and the least primitive root,
::  for a spread of shapes: primes, prime powers, cyclic and not.
++  ntvecs
  ^-  (list [n=@ud phi=@ud nd=@ud rad=@ud pr=(unit @ud)])
  :~
    [2 1 2 2 [~ 1]]
    [3 2 2 3 [~ 2]]
    [4 2 3 2 [~ 3]]
    [5 4 2 5 [~ 2]]
    [6 2 4 6 [~ 5]]
    [7 6 2 7 [~ 3]]
    [8 4 4 2 ~]
    [9 6 3 3 [~ 2]]
    [10 4 4 10 [~ 3]]
    [11 10 2 11 [~ 2]]
    [12 4 6 6 ~]
    [14 6 4 14 [~ 3]]
    [15 8 4 15 ~]
    [16 8 5 2 ~]
    [18 6 6 6 [~ 5]]
    [20 8 6 10 ~]
    [22 10 4 22 [~ 7]]
    [25 20 3 5 [~ 2]]
    [26 12 4 26 [~ 7]]
    [27 18 4 3 [~ 2]]
    [36 12 9 6 ~]
    [49 42 3 7 [~ 3]]
    [50 20 6 10 [~ 3]]
    [60 16 12 30 ~]
    [81 54 5 3 [~ 2]]
    [98 42 6 14 [~ 3]]
    [121 110 3 11 [~ 2]]
    [125 100 4 5 [~ 2]]
    [128 64 8 2 ~]
    [169 156 3 13 [~ 2]]
    [242 110 6 22 [~ 7]]
    [250 100 8 10 [~ 3]]
    [360 96 24 30 ~]
    [361 342 3 19 [~ 2]]
    [1.000 400 16 10 ~]
    [1.024 512 11 2 ~]
    [2.048 1.024 12 2 ~]
    [5.040 1.152 60 210 ~]
    [9.973 9.972 2 9.973 [~ 11]]
    [65.537 65.536 2 65.537 [~ 3]]
  ==
::  Multiplicative orders: a, n, and the least e with a^e = 1.
++  ordvecs
  ^-  (list [a=@ud n=@ud e=@ud])
  :~
    [2 7 3]
    [3 7 6]
    [4 7 3]
    [5 7 6]
    [6 7 2]
    [3 8 2]
    [5 8 2]
    [7 8 2]
    [2 9 6]
    [4 9 3]
    [5 9 6]
    [7 9 3]
    [8 9 2]
    [2 11 10]
    [3 11 5]
    [4 11 5]
    [5 11 5]
    [6 11 10]
    [7 11 10]
    [8 11 10]
    [9 11 5]
    [10 11 2]
    [2 13 12]
    [3 13 3]
    [4 13 6]
    [5 13 4]
    [6 13 12]
    [7 13 12]
    [8 13 4]
    [9 13 3]
    [10 13 6]
    [11 13 12]
    [3 16 4]
    [5 16 4]
    [7 16 2]
    [9 16 2]
    [11 16 4]
    [2 17 8]
    [3 17 16]
    [4 17 4]
    [5 17 16]
    [6 17 16]
    [7 17 16]
    [8 17 8]
    [9 17 8]
    [10 17 16]
    [11 17 16]
    [2 25 20]
    [3 25 20]
    [4 25 10]
    [6 25 5]
    [7 25 4]
    [8 25 20]
    [9 25 10]
    [11 25 5]
    [2 27 18]
    [4 27 9]
    [5 27 18]
    [7 27 9]
    [8 27 6]
  ==
::
::  Integer factorization (/lib/racoon-zfac).  A consumer of the library:
::  +nz froze at six arms, and this is the seventh that could not go in.
::
::  A factorization into primes is UNIQUE, so the transcribed SymPy values
::  below are values and not a convention -- any correct algorithm agrees
::  with them, which is exactly what makes every arm here `free`.  The
::  identities are checked alongside, since they catch classes of error a
::  fixed table cannot.
::
++  test-zfac-vectors
  =/  vs  zfvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  expect-eq
        !>(`(list [p=@ud m=@ud])`fs.i.vs)
      !>((factor:zf n.i.vs))
  ==
++  test-zfac-identities
  =/  vs  zfvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  n=@ud  n.i.vs
  =/  fs     (factor:zf n)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        ::  the factors multiply back to n -- the one identity that makes
        ::  every other check meaningful
        ::  +roll seeds its accumulator from the gate sample's BUNT, which
        ::  is 0 for +mul and would make every product 0; hence _1
        %+  expect-eq  !>(`@ud`n)
        !>  %+  roll  (turn fs |=([p=@ud m=@ud] (pow p m)))
            |=([x=@ud acc=_1] (mul x acc))
        ::  every listed factor is prime, and no multiplicity is zero
        %-  expect  !>((levy (turn fs |=([p=@ud m=@ud] p)) is-prime:nz))
        %-  expect  !>((levy (turn fs |=([p=@ud m=@ud] m)) |=(m=@ud (gth m 0))))
        ::  primes strictly ascending, which is what makes it canonical
        %-  expect  !>((ascends (turn fs |=([p=@ud m=@ud] p))))
        ::  the radical divides n and has the same prime support
        %-  expect  !>(=(0 (mod n (radical:zf n))))
        %+  expect-eq  !>((lent fs))  !>((lent (factor:zf (radical:zf n))))
        ::  the divisor count is prod (m + 1), and every divisor divides
        %+  expect-eq
          !>  %+  roll  (turn fs |=([p=@ud m=@ud] +(m)))
              |=([x=@ud acc=_1] (mul x acc))
        !>((lent (divisors:zf n)))
        %-  expect
        !>((levy (divisors:zf n) |=(k=@ud =(0 (mod n k)))))
        %-  expect  !>((ascends (divisors:zf n)))
        ::  n itself and 1 are always divisors
        %-  expect  !>((lien (divisors:zf n) |=(k=@ud =(k n))))
        %-  expect  !>((lien (divisors:zf n) |=(k=@ud =(k 1))))
      ==
  ==
++  test-zfac-numbertheory
  =/  vs  ntvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  n=@ud  n.i.vs
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq  !>(`@ud`phi.i.vs)  !>((totient:zf n))
        %+  expect-eq  !>(`@ud`nd.i.vs)   !>((lent (divisors:zf n)))
        %+  expect-eq  !>(`@ud`rad.i.vs)  !>((radical:zf n))
        ::  ~ exactly when the unit group is not cyclic, which is most n
        %+  expect-eq  !>(`(unit @ud)`pr.i.vs)  !>((primitive-root:zf n))
        ::  phi counts the units, checked by counting them directly --
        ::  only for small n, since this is O(n) gcds against a formula
        ?:  (gth n 2.048)  ~
        %+  expect-eq
          !>(`@ud`phi.i.vs)
        !>((lent (skim (gulf 1 n) |=(a=@ud =(1 (gcd:nz a n))))))
      ==
  ==
++  test-zfac-order
  =/  vs  ordvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  a=@ud  a.i.vs
  =/  n=@ud  n.i.vs
  =/  e=@ud  (order:zf a n)
  =/  dr     ~(. mx n)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq  !>(`@ud`e.i.vs)  !>(`@ud`e)
        ::  a^e = 1, and e divides phi(n) by Lagrange
        %+  expect-eq  !>(`@ud`1)  !>((cpow:dr (mod a n) e))
        %-  expect  !>(=(0 (mod (totient:zf n) e)))
        ::  and e is LEAST: no proper divisor of e works
        %-  expect
        !>  %+  levy  (divisors:zf e)
            |=(k=@ud ?:(=(k e) %.y !=(1 (cpow:dr (mod a n) k))))
      ==
  ==
++  test-zfac-primroot
  ::  bound with an explicit (list @ud): a ~[...] literal infers as a
  ::  fixed-length tuple, and +levy is wet, so it would fail to nest on
  ::  the final cdr
  =/  cyc=(list @ud)  ~[3 5 7 9 11 13 14 18 22 25 27 121 169]
  =/  acyc=(list @ud)  ~[8 12 15 16 20 21 24 32 35 40 48 105]
  ;:  weld
    ::  a primitive root generates every unit, which is the definition
    ::  and not a restatement of the order test
    %-  expect
    !>  %+  levy  cyc
        |=  n=@ud
        ^-  ?
        =/  g  (primitive-root:zf n)
        ?~  g  %.n
        =/  dr  ~(. mx n)
        =/  ps=(list @ud)
          (turn (gulf 1 (totient:zf n)) |=(k=@ud (cpow:dr u.g k)))
        =/  us=(list @ud)
          (skim (gulf 1 n) |=(a=@ud =(1 (gcd:nz a n))))
        =((sort (skim ps |=(x=@ud !=(0 x))) lth) (sort us lth))
    ::  the non-cyclic cases, where ~ is the right answer
    %-  expect
    !>((levy acyc |=(n=@ud =(~ (primitive-root:zf n)))))
  ==
++  test-zfac-crash
  ;:  weld
    ::  zero has no factorization: every prime divides it, and there is
    ::  no sentinel that would not be a lie
    (expect-fail |.((factor:zf 0)))
    (expect-fail |.((totient:zf 0)))
    (expect-fail |.((divisors:zf 0)))
    (expect-fail |.((radical:zf 0)))
    ::  one is the empty product, not an error
    (expect-success |.((factor:zf 1)))
    %+  expect-eq  !>(`(list [p=@ud m=@ud])`~)  !>((factor:zf 1))
    %+  expect-eq  !>(`@ud`1)  !>((totient:zf 1))
    %+  expect-eq  !>(`@ud`1)  !>((radical:zf 1))
    %+  expect-eq  !>(`(list @ud)`~[1])  !>((divisors:zf 1))
    ::  a non-unit has no multiplicative order at all
    (expect-fail |.((order:zf 2 4)))
    (expect-fail |.((order:zf 6 9)))
    (expect-fail |.((order:zf 0 7)))
    ::  and there is no group to speak of below 2
    (expect-fail |.((order:zf 1 1)))
    (expect-fail |.((primitive-root:zf 1)))
    (expect-success |.((order:zf 3 7)))
    (expect-success |.((primitive-root:zf 2)))
    ::  1 is a prime power only by a definition nobody uses
    %-  expect  !>((is-prime-power:zf 128))
    %-  expect  !>((is-prime-power:zf 9.973))
    %-  expect  !>(!(is-prime-power:zf 1))
    %-  expect  !>(!(is-prime-power:zf 0))
    %-  expect  !>(!(is-prime-power:zf 12))
  ==
::    +strictly-down:  is this list strictly decreasing?
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
