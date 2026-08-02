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
/+  *test, racoon, vec=racoon-vectors
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
|%
+|  %seeds
::    +seed-nz:  pinned PRNG seed for the +nz property tests
++  seed-nz  0xdead.beef.1234.5678
::    +seed-qq:  pinned PRNG seed for the +qq property tests
++  seed-qq  0xfeed.face.8765.4321
::    +seed-zx:  pinned PRNG seed for the +zx property tests
++  seed-zx  0xc0ff.ee00.1234.abcd
::
+|  %helpers
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
+|  %p0-nz-gcd
++  test-p0-gcd-small
  ;:  weld
    %+  expect-eq  !>(`@ud`6)   !>((gcd:nz 12 18))
    %+  expect-eq  !>(`@ud`6)   !>((gcd:nz 18 12))
    %+  expect-eq  !>(`@ud`1)   !>((gcd:nz 35 64))
    %+  expect-eq  !>(`@ud`17)  !>((gcd:nz 17 34))
    %+  expect-eq  !>(`@ud`5)   !>((gcd:nz 1.000.000 5))
  ==
::  S7: gcd(0, 0) = 0, and 0 is the identity.
++  test-p0-gcd-zero
  ;:  weld
    %+  expect-eq  !>(`@ud`0)   !>((gcd:nz 0 0))
    %+  expect-eq  !>(`@ud`17)  !>((gcd:nz 17 0))
    %+  expect-eq  !>(`@ud`17)  !>((gcd:nz 0 17))
    %+  expect-eq  !>(`@ud`1)   !>((gcd:nz 1 0))
  ==
::  Property: gcd divides both arguments, and is symmetric.
++  test-p0-gcd-divides
  =/  ps  (pairs (rng seed-nz 64 4.096))
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [a=@ud b=@ud]
  =/  g  (gcd:nz a b)
  ?!  ?&  (divides g a)
          (divides g b)
          =(g (gcd:nz b a))
      ==
::
+|  %p0-nz-egcd
::  S7/S9: Bezout identity d = u*a + v*b, with d = gcd(a, b).
++  test-p0-egcd-bezout
  =/  ps  (pairs (rng seed-nz 64 4.096))
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [a=@ud b=@ud]
  =/  e  (egcd:nz a b)
  =/  lhs=@s  (sun:si d.e)
  =/  rhs=@s
    (sum:si (pro:si u.e (sun:si a)) (pro:si v.e (sun:si b)))
  ?!  ?&  =(lhs rhs)
          =(d.e (gcd:nz a b))
      ==
::  S7: pinned base case egcd(a, 0) = [a --1 --0].
++  test-p0-egcd-base
  ;:  weld
    %+  expect-eq  !>([d=`@ud`17 u=`@s`--1 v=`@s`--0])  !>((egcd:nz 17 0))
    %+  expect-eq  !>([d=`@ud`0 u=`@s`--1 v=`@s`--0])   !>((egcd:nz 0 0))
  ==
::  Known vector: 2 = -9*240 + 47*46.
++  test-p0-egcd-known
  %+  expect-eq  !>([d=`@ud`2 u=`@s`-9 v=`@s`--47])  !>((egcd:nz 240 46))
::  S7: the EEA cofactors satisfy |u| <= b/(2d) and |v| <= a/(2d) for a,b > 0.
::  Tested as a property, not asserted in the library.
++  test-p0-egcd-cofactor-bounds
  =/  ps  (pairs (rng seed-nz 64 4.096))
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [a=@ud b=@ud]
  ?:  |(=(0 a) =(0 b))  %.n
  =/  e  (egcd:nz a b)
  ?!  ?&  (lte (abs:si u.e) (div b (mul 2 d.e)))
          (lte (abs:si v.e) (div a (mul 2 d.e)))
      ==
::
+|  %p0-nz-isqrt
::  S9: the unique r with r^2 <= a < (r+1)^2.
++  test-p0-isqrt-small
  ;:  weld
    %+  expect-eq  !>(`@ud`0)   !>((isqrt:nz 0))
    %+  expect-eq  !>(`@ud`1)   !>((isqrt:nz 1))
    %+  expect-eq  !>(`@ud`1)   !>((isqrt:nz 2))
    %+  expect-eq  !>(`@ud`1)   !>((isqrt:nz 3))
    %+  expect-eq  !>(`@ud`2)   !>((isqrt:nz 4))
    %+  expect-eq  !>(`@ud`2)   !>((isqrt:nz 8))
    %+  expect-eq  !>(`@ud`3)   !>((isqrt:nz 15))
    %+  expect-eq  !>(`@ud`4)   !>((isqrt:nz 16))
    %+  expect-eq  !>(`@ud`9)   !>((isqrt:nz 99))
    %+  expect-eq  !>(`@ud`10)  !>((isqrt:nz 100))
  ==
++  test-p0-isqrt-large
  ;:  weld
    %+  expect-eq  !>(`@ud`3.162.277)   !>((isqrt:nz 10.000.000.000.000))
    %+  expect-eq  !>(`@ud`1.000.000)   !>((isqrt:nz 1.000.000.000.000))
    ::  a perfect square, and the value one below it: 65.535^2 is
    ::  4.294.836.225, so its predecessor must round down to 65.534
    %+  expect-eq  !>(`@ud`65.535)      !>((isqrt:nz 4.294.836.225))
    %+  expect-eq  !>(`@ud`65.534)      !>((isqrt:nz 4.294.836.224))
    ::  exact powers of two, on both sides of the 32-bit boundary
    %+  expect-eq  !>(`@ud`65.536)      !>((isqrt:nz 4.294.967.296))
    %+  expect-eq  !>(`@ud`65.535)      !>((isqrt:nz 4.294.967.295))
    %+  expect-eq  !>(`@ud`4.294.967.296)
      !>((isqrt:nz 18.446.744.073.709.551.616))
  ==
::  Property: the defining inequality, over a wide range.
++  test-p0-isqrt-bracket
  =/  as  (rng seed-nz 96 1.000.000.000.000)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skim  as
  |=  a=@ud
  =/  r  (isqrt:nz a)
  ?!  ?&  (lte (mul r r) a)
          (gth (mul +(r) +(r)) a)
      ==
::
+|  %p0-nz-is-prime
++  test-p0-is-prime-small
  =/  ps=(list @ud)  ~[2 3 5 7 11 13 17 19 23 29 31 37 41 43 97 101]
  =/  cs=(list @ud)  ~[0 1 4 6 8 9 15 21 25 27 33 35 49 51 91 100]
  ;:  weld
    %+  expect-eq  !>(~)  !>((skip ps is-prime:nz))
    %+  expect-eq  !>(~)  !>((skim cs is-prime:nz))
  ==
::  Carmichael numbers: Fermat-fools, so they exercise the strong test.
++  test-p0-is-prime-carmichael
  =/  cs=(list @ud)  ~[561 1.105 1.729 2.465 2.821 6.601 8.911 62.745]
  %+  expect-eq  !>(~)  !>((skim cs is-prime:nz))
::  Strong pseudoprimes to the first few bases; each must still be composite.
++  test-p0-is-prime-spsp
  =/  cs=(list @ud)
    ~[2.047 1.373.653 25.326.001 3.215.031.751 2.152.302.898.747]
  %+  expect-eq  !>(~)  !>((skim cs is-prime:nz))
::  Large primes, including the 61-bit Mersenne prime used by the vectors.
++  test-p0-is-prime-large
  ;:  weld
    %+  expect-eq  !>(%.y)  !>((is-prime:nz 2.305.843.009.213.693.951))
    %+  expect-eq  !>(%.n)  !>((is-prime:nz 2.305.843.009.213.693.953))
    %+  expect-eq  !>(%.y)  !>((is-prime:nz 1.000.000.007))
    %+  expect-eq  !>(%.n)  !>((is-prime:nz 1.000.000.009.000.000.021))
  ==
::  Every witness in the pinned schedule is itself prime.
++  test-p0-is-prime-witnesses
  =/  ws=(list @ud)  ~[2 3 5 7 11 13 17 19 23 29 31 37]
  %+  expect-eq  !>(~)  !>((skip ws is-prime:nz))
::
+|  %p0-nz-crt
++  test-p0-crt-known
  ;:  weld
    %+  expect-eq
      !>([r=`@ud`23 m=`@ud`105])
    !>((crt:nz ~[[2 3] [3 5] [2 7]]))
    %+  expect-eq
      !>([r=`@ud`1 m=`@ud`36])
    !>((crt:nz ~[[1 4] [1 9]]))
    ::  singleton: reduces its residue into [0, m)
    %+  expect-eq  !>([r=`@ud`3 m=`@ud`5])  !>((crt:nz ~[[3 5]]))
    %+  expect-eq  !>([r=`@ud`3 m=`@ud`5])  !>((crt:nz ~[[13 5]]))
  ==
::  Property: the product satisfies every congruence and lies in [0, m).
++  test-p0-crt-congruent
  =/  ms=(list [r=@ud m=@ud])  ~[[2 7] [4 11] [9 13] [1 17]]
  =/  c  (crt:nz ms)
  ;:  weld
    %+  expect-eq  !>(`@ud`17.017)  !>(m.c)
    (expect !>((lth r.c m.c)))
    %+  expect-eq  !>(~)
    !>  ^-  (list [r=@ud m=@ud])
    %+  skim  ms
    |=  [r=@ud m=@ud]
    ?!  =(r (mod r.c m))
  ==
::
+|  %p0-nz-ratrec
::  S9: recovers p/q with q*u = p mod m, |p| <= nb, 0 < q <= db.
++  test-p0-ratrec-known
  ;:  weld
    ::  65 is the inverse of 3 mod 97, so 65 reconstructs as 1/3
    %+  expect-eq  !>(`(unit frac)`[~ --1 3])  !>((ratrec:nz 65 97 6 6))
    ::  zero reconstructs as the canonical zero
    %+  expect-eq  !>(`(unit frac)`[~ --0 1])  !>((ratrec:nz 0 97 6 6))
    ::  one reconstructs as itself
    %+  expect-eq  !>(`(unit frac)`[~ --1 1])  !>((ratrec:nz 1 97 6 6))
    ::  m - 1 is -1
    %+  expect-eq  !>(`(unit frac)`[~ -1 1])   !>((ratrec:nz 96 97 6 6))
  ==
::  S8: failure is ~, never a crash.
++  test-p0-ratrec-fail
  ;:  weld
    %+  expect-eq  !>(`(unit frac)`~)  !>((ratrec:nz 5 97 2 2))
    %+  expect-eq  !>(`(unit frac)`~)  !>((ratrec:nz 44 97 3 3))
  ==
::  Property: round-trip small rationals through their residue mod a prime.
::  For each p/q, u = p * inv(q) mod m must reconstruct to exactly p/q.
++  test-p0-ratrec-roundtrip
  =/  m=@ud   10.007
  =/  bd=@ud  (isqrt:nz (div (dec m) 2))
  =/  ps  (pairs (rng seed-nz 48 70))
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [a=@ud b=@ud]
  ?:  |(=(0 b) (gth a bd) (gth b bd))  %.n
  ?.  =(1 (gcd:nz a b))  %.n
  ::  u = a * b^-1 mod m, via the EEA cofactor of b
  =/  e   (egcd:nz b m)
  ?.  =(1 d.e)  %.n
  =/  bi  (dul:si u.e m)
  =/  u   (mod (mul a bi) m)
  ?!  =(`[(sun:si a) b] (ratrec:nz u m bd bd))
::
+|  %p0-qq
++  test-p0-qq-constants
  ;:  weld
    %+  expect-eq  !>(`frac`[--0 1])  !>(zero:qq)
    %+  expect-eq  !>(`frac`[--1 1])  !>(one:qq)
  ==
::  S7: +new reduces to lowest terms with q > 0.
++  test-p0-qq-new
  ;:  weld
    %+  expect-eq  !>(`frac`[-3 2])   !>((new:qq -6 4))
    %+  expect-eq  !>(`frac`[--3 2])  !>((new:qq --6 4))
    %+  expect-eq  !>(`frac`[--0 1])  !>((new:qq --0 7))
    %+  expect-eq  !>(`frac`[--1 1])  !>((new:qq --5 5))
    %+  expect-eq  !>(`frac`[--2 1])  !>((new:qq --4 2))
  ==
++  test-p0-qq-arith
  ;:  weld
    %+  expect-eq  !>(`frac`[--5 6])   !>((add:qq [--1 2] [--1 3]))
    %+  expect-eq  !>(`frac`[--1 6])   !>((sub:qq [--1 2] [--1 3]))
    %+  expect-eq  !>(`frac`[--1 2])   !>((mul:qq [--2 3] [--3 4]))
    %+  expect-eq  !>(`frac`[--2 3])   !>((div:qq [--1 2] [--3 4]))
    %+  expect-eq  !>(`frac`[-1 2])    !>((neg:qq [--1 2]))
    %+  expect-eq  !>(`frac`[-4 3])    !>((inv:qq [-3 4]))
    ::  results are canonical even when the arithmetic is not reduced
    %+  expect-eq  !>(`frac`[--0 1])   !>((add:qq [--1 2] [-1 2]))
    %+  expect-eq  !>(`frac`[--1 1])   !>((add:qq [--1 2] [--2 4]))
  ==
++  test-p0-qq-cmp
  ;:  weld
    %+  expect-eq  !>(`ord`%gt)  !>((cmp:qq [--1 2] [--1 3]))
    %+  expect-eq  !>(`ord`%lt)  !>((cmp:qq [--1 3] [--1 2]))
    %+  expect-eq  !>(`ord`%eq)  !>((cmp:qq [--1 2] [--1 2]))
    %+  expect-eq  !>(`ord`%lt)  !>((cmp:qq [-1 2] [--1 3]))
    %+  expect-eq  !>(`ord`%gt)  !>((cmp:qq [--0 1] [-1 3]))
    %+  expect-eq  !>(`ord`%eq)  !>((cmp:qq [--0 1] zero:qq))
  ==
::  Property: field axioms, sampled.  Associativity and commutativity of + and
::  *, distributivity, and the two inverse laws.
++  test-p0-qq-axioms
  =/  ns  (rng seed-qq 72 40)
  =/  ps  (pairs ns)
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [x=@ud y=@ud]
  ::  build three rationals deterministically from the pair
  =/  a  (new:qq (sun:si x) +(y))
  =/  b  (new:qq (dif:si --0 (sun:si y)) +(x))
  =/  c  (new:qq (sun:si +(x)) +((add x y)))
  ?!  ?&  =((add:qq a b) (add:qq b a))
          =((mul:qq a b) (mul:qq b a))
          =((add:qq a (add:qq b c)) (add:qq (add:qq a b) c))
          =((mul:qq a (mul:qq b c)) (mul:qq (mul:qq a b) c))
          =((mul:qq a (add:qq b c)) (add:qq (mul:qq a b) (mul:qq a c)))
          =(zero:qq (add:qq a (neg:qq a)))
          =(a (add:qq a zero:qq))
          =(a (mul:qq a one:qq))
      ==
::  Property: every +qq product is canonical -- q > 0 and gcd(|p|, q) = 1.
++  test-p0-qq-canonical
  =/  ps  (pairs (rng seed-qq 64 200))
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [x=@ud y=@ud]
  =/  a  (new:qq (sun:si x) +(y))
  =/  b  (new:qq (dif:si --0 (sun:si +(y))) +(x))
  =/  rs=(list frac)
    :~  (add:qq a b)  (sub:qq a b)  (mul:qq a b)
        (div:qq a b)  (neg:qq a)    (inv:qq b)
    ==
  ?!  %+  levy  rs
      |=  f=frac
      ?&  (gth q.f 0)
          =(1 (gcd:nz (abs:si p.f) q.f))
      ==
::  Property: inverse and division agree, and inv is an involution.
++  test-p0-qq-inverse
  =/  ps  (pairs (rng seed-qq 48 200))
  %+  expect-eq  !>(~)
  !>  ^-  (list [@ud @ud])
  %+  skim  ps
  |=  [x=@ud y=@ud]
  =/  a  (new:qq (sun:si +(x)) +(y))
  =/  b  (new:qq (dif:si --0 (sun:si +(y))) +(x))
  ?!  ?&  =(one:qq (mul:qq a (inv:qq a)))
          =(a (inv:qq (inv:qq a)))
          =((div:qq a b) (mul:qq a (inv:qq b)))
      ==
::
+|  %p0-crashes
::  Every SPEC S8 row naming a Phase 0 arm.
::
::  S8: +div (qq), divisor zero.
++  test-p0-crash-qq-div-zero
  ;:  weld
    (expect-fail |.((div:qq one:qq zero:qq)))
    (expect-fail |.((div:qq zero:qq zero:qq)))
    (expect-fail |.((div:qq [--3 4] [--0 1])))
  ==
::  S8: +inv (qq), operand zero.
++  test-p0-crash-qq-inv-zero
  (expect-fail |.((inv:qq zero:qq)))
::  S8 (added, Q3): +new (qq), q = 0.
++  test-p0-crash-qq-new-zero-denominator
  ;:  weld
    (expect-fail |.((new:qq --1 0)))
    (expect-fail |.((new:qq --0 0)))
  ==
::  S8: +crt (nz), empty list.
++  test-p0-crash-crt-empty
  (expect-fail |.((crt:nz ~)))
::  S8: +crt (nz), any modulus < 2.
++  test-p0-crash-crt-small-modulus
  ;:  weld
    (expect-fail |.((crt:nz ~[[0 1]])))
    (expect-fail |.((crt:nz ~[[0 0]])))
    (expect-fail |.((crt:nz ~[[1 5] [0 1]])))
  ==
::  S8: +crt (nz), moduli not pairwise coprime.
++  test-p0-crash-crt-not-coprime
  ;:  weld
    (expect-fail |.((crt:nz ~[[1 4] [1 6]])))
    (expect-fail |.((crt:nz ~[[1 9] [1 3]])))
    (expect-fail |.((crt:nz ~[[1 5] [1 7] [1 35]])))
  ==
::
+|  %p0-non-crashes
::  The arms that must NOT crash on their edge inputs.
::
::  S9: gcd is total.
++  test-p0-nocrash-gcd
  ;:  weld
    (expect-success |.((gcd:nz 0 0)))
    (expect-success |.((egcd:nz 0 0)))
    (expect-success |.((isqrt:nz 0)))
    (expect-success |.((is-prime:nz 0)))
    (expect-success |.((is-prime:nz 1)))
  ==
::  S8: +ratrec reports failure as ~, it does not crash.
++  test-p0-nocrash-ratrec
  ;:  weld
    (expect-success |.((ratrec:nz 5 97 2 2)))
    (expect-success |.((ratrec:nz 0 2 0 0)))
  ==
::
+|  %p1-zx
::  Phase 1: Z[x] arithmetic.  All arms are `free` -- outputs are canonical,
::  so a jet may use any algorithm.
::
::  S7: +canon strips every trailing zero, and only trailing zeros.
++  test-p1-zx-canon
  ;:  weld
    %+  expect-eq  !>(`zol`~)          !>((canon:zx ~))
    %+  expect-eq  !>(`zol`~)          !>((canon:zx ~[--0]))
    %+  expect-eq  !>(`zol`~)          !>((canon:zx ~[--0 --0 --0]))
    %+  expect-eq  !>(`zol`~[--1])     !>((canon:zx ~[--1 --0]))
    %+  expect-eq  !>(`zol`~[--1])     !>((canon:zx ~[--1 --0 --0]))
    ::  interior zeros survive; only the tail is stripped
    %+  expect-eq
      !>(`zol`~[--0 --1])
    !>((canon:zx ~[--0 --1]))
    %+  expect-eq
      !>(`zol`~[--0 --0 --1])
    !>((canon:zx ~[--0 --0 --1 --0 --0]))
  ==
++  test-p1-zx-deg-lc
  ;:  weld
    %+  expect-eq  !>(`@ud`0)   !>((deg:zx ~[--5]))
    %+  expect-eq  !>(`@ud`2)   !>((deg:zx ~[--1 --2 --3]))
    %+  expect-eq  !>(`@ud`3)   !>((deg:zx ~[--0 --0 --0 --1]))
    %+  expect-eq  !>(`@s`--5)  !>((lc:zx ~[--5]))
    %+  expect-eq  !>(`@s`-3)   !>((lc:zx ~[--1 --2 -3]))
    %+  expect-eq  !>(%.y)      !>((is-zero:zx ~))
    %+  expect-eq  !>(%.n)      !>((is-zero:zx ~[--1]))
  ==
::  S7: shorter first (~ least); at equal length, high index down.
++  test-p1-zx-pcmp
  ;:  weld
    %+  expect-eq  !>(`ord`%lt)  !>((pcmp:zx ~ ~[--1]))
    %+  expect-eq  !>(`ord`%gt)  !>((pcmp:zx ~[--1] ~))
    %+  expect-eq  !>(`ord`%eq)  !>((pcmp:zx ~ ~))
    %+  expect-eq  !>(`ord`%eq)  !>((pcmp:zx ~[--1] ~[--1]))
    ::  degree dominates coefficient magnitude
    %+  expect-eq  !>(`ord`%gt)  !>((pcmp:zx ~[--1 --1] ~[--9]))
    %+  expect-eq  !>(`ord`%lt)  !>((pcmp:zx ~[--1 --2] ~[--1 --3]))
    ::  equal top coefficient, decided lower down
    %+  expect-eq  !>(`ord`%lt)  !>((pcmp:zx ~[-1 --2] ~[--1 --2]))
  ==
++  test-p1-zx-arith
  ;:  weld
    %+  expect-eq  !>(`zol`~[--4 --6])  !>((add:zx ~[--1 --2] ~[--3 --4]))
    ::  leading terms cancel: the sum must be canonicalized
    %+  expect-eq  !>(`zol`~)           !>((add:zx ~[--1 --2] ~[-1 -2]))
    %+  expect-eq  !>(`zol`~[--0 --1])  !>((add:zx ~[--1 --1] ~[-1]))
    %+  expect-eq  !>(`zol`~)           !>((sub:zx ~[--1 --2] ~[--1 --2]))
    %+  expect-eq  !>(`zol`~[-1 --2])   !>((neg:zx ~[--1 -2]))
    ::  (1 + x)^2 and (x - 1)(x + 1)
    %+  expect-eq
      !>(`zol`~[--1 --2 --1])
    !>((mul:zx ~[--1 --1] ~[--1 --1]))
    %+  expect-eq
      !>(`zol`~[-1 --0 --1])
    !>((mul:zx ~[--1 --1] ~[-1 --1]))
    %+  expect-eq  !>(`zol`~)           !>((mul:zx ~ ~[--1]))
    %+  expect-eq  !>(`zol`~)           !>((mul:zx ~[--1] ~))
    %+  expect-eq  !>(`zol`~[--6])      !>((mul:zx ~[--2] ~[--3]))
  ==
++  test-p1-zx-shift-scale-eval
  ;:  weld
    %+  expect-eq
      !>(`zol`~[--0 --0 --0 --1 --2])
    !>((shift:zx ~[--1 --2] 3))
    %+  expect-eq  !>(`zol`~[--1])      !>((shift:zx ~[--1] 0))
    %+  expect-eq  !>(`zol`~)           !>((shift:zx ~ 5))
    %+  expect-eq  !>(`zol`~[--3 --6])  !>((scale:zx ~[--1 --2] --3))
    ::  scaling by zero collapses to the zero polynomial
    %+  expect-eq  !>(`zol`~)           !>((scale:zx ~[--1 --2] --0))
    %+  expect-eq  !>(`zol`~[-1 -2])    !>((scale:zx ~[--1 --2] -1))
    %+  expect-eq  !>(`@s`--7)          !>((eval:zx ~[--1 --2] --3))
    %+  expect-eq  !>(`@s`--0)          !>((eval:zx ~ -5))
    %+  expect-eq  !>(`@s`--5)          !>((eval:zx ~[--1 --0 --1] -2))
    %+  expect-eq  !>(`@s`--5)          !>((eval:zx ~[--5] --9))
  ==
::  Property: the commutative ring axioms of Z[x], sampled.
++  test-p1-zx-axioms
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol zol])
  %+  skip  (ztriples (zols seed-zx 40))
  |=  [a=zol b=zol c=zol]
  ?&  =((add:zx a b) (add:zx b a))
      =((mul:zx a b) (mul:zx b a))
      =((add:zx a (add:zx b c)) (add:zx (add:zx a b) c))
      =((mul:zx a (mul:zx b c)) (mul:zx (mul:zx a b) c))
      =((mul:zx a (add:zx b c)) (add:zx (mul:zx a b) (mul:zx a c)))
      =(~ (add:zx a (neg:zx a)))
      =(a (add:zx a ~))
      =(a (mul:zx a ~[--1]))
      =(~ (mul:zx a ~))
      =((sub:zx a b) (add:zx a (neg:zx b)))
  ==
::  Property: +eval is a ring homomorphism Z[x] -> Z at every point.
++  test-p1-zx-eval-homomorphism
  =/  xs=(list @s)  ~[--0 --1 -1 --2 -3 --7]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 40))
  |=  [a=zol b=zol]
  %+  levy  xs
  |=  x=@s
  ?&  =((eval:zx (add:zx a b) x) (sum:si (eval:zx a x) (eval:zx b x)))
      =((eval:zx (mul:zx a b) x) (pro:si (eval:zx a x) (eval:zx b x)))
  ==
::  Property: Z is an integral domain, so degrees add and leading
::  coefficients multiply under +mul.
++  test-p1-zx-degree-additive
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 40))
  |=  [a=zol b=zol]
  ?:  |(=(~ a) =(~ b))  %.y
  =/  p  (mul:zx a b)
  ?&  =(p (canon:zx p))
      =((deg:zx p) (add (deg:zx a) (deg:zx b)))
      =((lc:zx p) (pro:si (lc:zx a) (lc:zx b)))
  ==
::  Property: +shift and +scale agree with the multiplications they abbreviate.
++  test-p1-zx-shift-scale-consistent
  =/  ks=(list @ud)  ~[0 1 2 5]
  =/  cs=(list @s)   ~[--0 --1 -1 --4 -7]
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 40)
  |=  a=zol
  ?&  %+  levy  ks
      |=(k=@ud =((shift:zx a k) (mul:zx a (shift:zx ~[--1] k))))
      %+  levy  cs
      |=(c=@s =((scale:zx a c) (mul:zx a (canon:zx ~[c]))))
  ==
::  Property: every +zx product is canonical, and +canon is idempotent.
++  test-p1-zx-canonical
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 40))
  |=  [a=zol b=zol]
  =/  rs=(list zol)
    :~  (add:zx a b)  (sub:zx a b)  (mul:zx a b)  (neg:zx a)
        (shift:zx a 3)  (scale:zx a -2)  (canon:zx a)
    ==
  ?&  =(a (canon:zx a))
      %+  levy  rs
      |=(r=zol =(r (canon:zx r)))
  ==
::
+|  %p1-mx
::  Phase 1: (Z/n)[x] and Z/n scalars.
::
::  Z/n is not an integral domain for composite n, so the tests that matter
::  most here are the ones at n = 6 where a product of nonzero values is zero.
::
++  test-p1-mx-scalars
  ;:  weld
    %+  expect-eq  !>(`@ud`1)  !>((cadd:m7 3 5))
    %+  expect-eq  !>(`@ud`4)  !>((csub:m7 2 5))
    %+  expect-eq  !>(`@ud`1)  !>((cmul:m7 3 5))
    %+  expect-eq  !>(`@ud`0)  !>((cneg:m7 0))
    %+  expect-eq  !>(`@ud`4)  !>((cneg:m7 3))
    %+  expect-eq  !>(`@ud`5)  !>((cinv:m7 3))
    %+  expect-eq  !>(`@ud`1)  !>((cinv:m7 1))
    %+  expect-eq  !>(`@ud`6)  !>((cinv:m7 6))
    ::  5 is a unit mod 6 and is its own inverse
    %+  expect-eq  !>(`@ud`5)  !>((cinv:m6 5))
    ::  the smallest modulus
    %+  expect-eq  !>(`@ud`1)  !>((cadd:m2 1 0))
    %+  expect-eq  !>(`@ud`0)  !>((cadd:m2 1 1))
    %+  expect-eq  !>(`@ud`1)  !>((cneg:m2 1))
  ==
::  S8: cpow(0, 0) = 1, pinned, no crash.
++  test-p1-mx-cpow
  ;:  weld
    %+  expect-eq  !>(`@ud`1)  !>((cpow:m7 0 0))
    %+  expect-eq  !>(`@ud`1)  !>((cpow:m7 3 0))
    %+  expect-eq  !>(`@ud`0)  !>((cpow:m7 0 5))
    %+  expect-eq  !>(`@ud`4)  !>((cpow:m7 3 4))
    %+  expect-eq  !>(`@ud`2)  !>((cpow:m7 2 10))
    %+  expect-eq  !>(`@ud`1)  !>((cpow:m6 0 0))
    %+  expect-eq  !>(`@ud`1)  !>((cpow:m2 0 0))
    ::  Fermat: a^(p-1) = 1 for a nonzero mod a prime
    %+  expect-eq  !>(`@ud`1)  !>((cpow:m7 3 6))
    %+  expect-eq  !>(`@ud`1)  !>((cpow:m7 5 6))
  ==
++  test-p1-mx-poly
  ;:  weld
    %+  expect-eq  !>(`mol`~[1])   !>((canon:m7 ~[1 0]))
    %+  expect-eq  !>(`mol`~)      !>((canon:m7 ~[0 0]))
    %+  expect-eq  !>(`@ud`2)      !>((deg:m7 ~[1 2 3]))
    %+  expect-eq  !>(`@ud`3)      !>((lc:m7 ~[1 2 3]))
    ::  3 + 4 = 0 mod 7: the sum vanishes entirely
    %+  expect-eq  !>(`mol`~)      !>((add:m7 ~[3] ~[4]))
    ::  and here only the leading term cancels
    %+  expect-eq  !>(`mol`~[2])   !>((add:m7 ~[1 3] ~[1 4]))
    %+  expect-eq  !>(`mol`~)      !>((sub:m7 ~[1 2] ~[1 2]))
    %+  expect-eq
      !>(`mol`~[6 5])
    !>((neg:m7 ~[1 2]))
    %+  expect-eq
      !>(`mol`~[0 0 0 1 2])
    !>((shift:m7 ~[1 2] 3))
    %+  expect-eq  !>(`mol`~)      !>((shift:m7 ~ 4))
    %+  expect-eq
      !>(`mol`~[3 6])
    !>((scale:m7 ~[1 2] 3))
    %+  expect-eq  !>(`mol`~)      !>((scale:m7 ~[1 2] 0))
    ::  1 + 2*3 = 7 = 0 mod 7
    %+  expect-eq  !>(`@ud`0)      !>((eval:m7 ~[1 2] 3))
    %+  expect-eq  !>(`@ud`0)      !>((eval:m7 ~ 5))
    %+  expect-eq  !>(`ord`%lt)    !>((pcmp:m7 ~ ~[1]))
    %+  expect-eq  !>(`ord`%lt)    !>((pcmp:m7 ~[1 2] ~[1 3]))
  ==
::  The zero-divisor cases.  Z/6 is not an integral domain, so a product of
::  nonzero polynomials can be zero and +mul must canonicalize -- unlike
::  +mul:zx, which cannot hit this.
++  test-p1-mx-zero-divisors
  ;:  weld
    ::  (2x)(3x) = 6x^2 = 0 mod 6
    %+  expect-eq  !>(`mol`~)       !>((mul:m6 ~[0 2] ~[0 3]))
    ::  2 * 3 = 0 mod 6, so scaling annihilates
    %+  expect-eq  !>(`mol`~)       !>((scale:m6 ~[3] 2))
    ::  (1 + 2x)(1 + 3x) = 1 + 5x + 6x^2 = 1 + 5x mod 6: degree drops
    %+  expect-eq  !>(`mol`~[1 5])  !>((mul:m6 ~[1 2] ~[1 3]))
    ::  (3x)(4x) = 12x^2 = 0 mod 12
    %+  expect-eq  !>(`mol`~)       !>((mul:~(. mx 12) ~[0 3] ~[0 4]))
    ::  16^2 = 256 = 0 mod 256
    %+  expect-eq  !>(`mol`~)       !>((mul:~(. mx 256) ~[0 16] ~[0 16]))
    ::  over a prime this cannot happen: the degree always adds
    %+  expect-eq
      !>(`mol`~[1 2 1])
    !>((mul:m7 ~[1 1] ~[1 1]))
  ==
::  Property: the commutative ring axioms of (Z/n)[x], sampled at a prime and
::  at a composite modulus.
++  test-p1-mx-axioms
  =/  ns=(list @ud)  ~[2 3 6 7 97 100]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol zol])
  %+  skip  (ztriples (zols seed-zx 30))
  |=  [x=zol y=zol z=zol]
  %+  levy  ns
  |=  n=@ud
  =/  d  ~(. mx n)
  =/  a  (to-mol x n)
  =/  b  (to-mol y n)
  =/  c  (to-mol z n)
  ?&  =((add:d a b) (add:d b a))
      =((mul:d a b) (mul:d b a))
      =((add:d a (add:d b c)) (add:d (add:d a b) c))
      =((mul:d a (mul:d b c)) (mul:d (mul:d a b) c))
      =((mul:d a (add:d b c)) (add:d (mul:d a b) (mul:d a c)))
      =(~ (add:d a (neg:d a)))
      =(a (add:d a ~))
      =(a (mul:d a ~[1]))
      =(~ (mul:d a ~))
      =((sub:d a b) (add:d a (neg:d b)))
  ==
::  Property: every +mx product is canonical, and coefficients stay in [0, n).
++  test-p1-mx-canonical
  =/  ns=(list @ud)  ~[2 3 6 7 12 97]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [x=zol y=zol]
  %+  levy  ns
  |=  n=@ud
  =/  d  ~(. mx n)
  =/  a  (to-mol x n)
  =/  b  (to-mol y n)
  =/  rs=(list mol)
    :~  (add:d a b)  (sub:d a b)  (mul:d a b)  (neg:d a)
        (shift:d a 3)  (scale:d a 2)  (canon:d a)
    ==
  ?&  =(a (canon:d a))
      %+  levy  rs
      |=  r=mol
      ?&  =(r (canon:d r))
          (levy r |=(c=@ud (lth c n)))
      ==
  ==
::  Property: +cinv inverts every unit, and +cpow agrees with repeated +cmul.
++  test-p1-mx-scalar-laws
  =/  ns=(list @ud)  ~[2 3 5 6 7 12 97 100]
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (rng seed-zx 60 1.000)
  |=  r=@ud
  %+  levy  ns
  |=  n=@ud
  =/  d  ~(. mx n)
  =/  a  (mod r n)
  =/  e  (mod r 12)
  ?&  ::  cpow by repeated multiplication
      =((cpow:d a e) |-(?:(=(0 e) (mod 1 n) (cmul:d a $(e (dec e))))))
      ::  additive inverse
      =(0 (cadd:d a (cneg:d a)))
      ::  multiplicative inverse, where one exists
      ?|  ?!(=(1 (gcd:nz a n)))
          =(1 (cmul:d a (cinv:d a)))
      ==
  ==
::  Property: +eval is a ring homomorphism (Z/n)[x] -> Z/n.
++  test-p1-mx-eval-homomorphism
  =/  ns=(list @ud)   ~[2 3 6 7 97]
  ::  the point list needs its (list @ud) face: +levy recurses through
  ::  $(a t.a), which will not nest against a fixed-length tuple type
  =/  pts=(list @ud)  ~[0 1 2]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [x=zol y=zol]
  %+  levy  ns
  |=  n=@ud
  =/  d  ~(. mx n)
  =/  a  (to-mol x n)
  =/  b  (to-mol y n)
  %+  levy  pts
  |=  pt=@ud
  =/  p  (mod pt n)
  ?&  =((eval:d (add:d a b) p) (cadd:d (eval:d a p) (eval:d b p)))
      =((eval:d (mul:d a b) p) (cmul:d (eval:d a p) (eval:d b p)))
  ==
::
+|  %p1-crashes
::  S8: +deg and +lc crash on the zero polynomial.
++  test-p1-crash-zx-deg-zero
  (expect-fail |.((deg:zx ~)))
++  test-p1-crash-zx-lc-zero
  (expect-fail |.((lc:zx ~)))
::  S8: +deg and +lc crash on ~ in every ring.
++  test-p1-crash-mx-deg-zero
  (expect-fail |.((deg:m7 ~)))
++  test-p1-crash-mx-lc-zero
  (expect-fail |.((lc:m7 ~)))
::  S8: +cinv crashes on a non-unit, which includes 0.
++  test-p1-crash-mx-cinv-non-unit
  ;:  weld
    (expect-fail |.((cinv:m7 0)))
    (expect-fail |.((cinv:m6 0)))
    ::  2, 3, and 4 all share a factor with 6
    (expect-fail |.((cinv:m6 2)))
    (expect-fail |.((cinv:m6 3)))
    (expect-fail |.((cinv:m6 4)))
    (expect-fail |.((cinv:m2 0)))
  ==
::  The +mx arms that must NOT crash.
++  test-p1-nocrash-mx
  ;:  weld
    ::  S8: cpow(0, 0) returns 1 rather than crashing
    (expect-success |.((cpow:m7 0 0)))
    (expect-success |.((cpow:m6 0 0)))
    ::  the units of Z/6 are exactly 1 and 5
    (expect-success |.((cinv:m6 1)))
    (expect-success |.((cinv:m6 5)))
    (expect-success |.((canon:m7 ~)))
    (expect-success |.((add:m7 ~ ~)))
    (expect-success |.((mul:m7 ~ ~)))
    (expect-success |.((neg:m7 ~)))
    (expect-success |.((eval:m7 ~ 3)))
    (expect-success |.((cneg:m7 0)))
  ==
::  The arms that must NOT crash on the zero polynomial.
++  test-p1-nocrash-zx-zero
  ;:  weld
    (expect-success |.((canon:zx ~)))
    (expect-success |.((is-zero:zx ~)))
    (expect-success |.((add:zx ~ ~)))
    (expect-success |.((mul:zx ~ ~)))
    (expect-success |.((neg:zx ~)))
    (expect-success |.((shift:zx ~ 3)))
    (expect-success |.((scale:zx ~ --2)))
    (expect-success |.((eval:zx ~ --2)))
    (expect-success |.((pcmp:zx ~ ~)))
  ==
::
+|  %p2-mx
::  Phase 2: division, GCD, and modular exponentiation over a field.
::
++  test-p2-mx-divmod
  ;:  weld
    ::  (x^2 - 1) / (x - 1) = x + 1, exactly
    %+  expect-eq
      !>([q=`mol`~[1 1] r=`mol`~])
    !>((divmod:m7 ~[6 0 1] ~[6 1]))
    ::  deg a < deg b: the quotient is empty and a is the remainder
    %+  expect-eq
      !>([q=`mol`~ r=`mol`~[1]])
    !>((divmod:m7 ~[1] ~[1 1]))
    %+  expect-eq
      !>([q=`mol`~ r=`mol`~])
    !>((divmod:m7 ~ ~[1 1]))
    ::  non-monic divisor: x^2 + 1 = (4x)(2x) + 1 over F_7, since 8 = 1
    %+  expect-eq
      !>([q=`mol`~[0 4] r=`mol`~[1]])
    !>((divmod:m7 ~[1 0 1] ~[0 2]))
  ==
++  test-p2-mx-gcd
  ;:  weld
    %+  expect-eq  !>(`mol`~[6 1])  !>((gcd:m7 ~[6 0 1] ~[6 1]))
    ::  x^2 + 1 has no root at -1 over F_7, so the two are coprime
    %+  expect-eq  !>(`mol`~[1])    !>((gcd:m7 ~[1 0 1] ~[1 1]))
    ::  S7: gcd(~, ~) = ~ and gcd(a, ~) = monic(a)
    %+  expect-eq  !>(`mol`~)       !>((gcd:m7 ~ ~))
    %+  expect-eq  !>(`mol`~[4 1])  !>((gcd:m7 ~[2 4] ~))
  ==
++  test-p2-mx-powmod
  ;:  weld
    ::  x^3 = -x = 6x modulo x^2 + 1
    %+  expect-eq  !>(`mol`~[0 6])  !>((powmod:m7 ~[0 1] 3 ~[1 0 1]))
    %+  expect-eq  !>(`mol`~[1])    !>((powmod:m7 ~[0 1] 0 ~[1 0 1]))
    %+  expect-eq  !>(`mol`~[0 1])  !>((powmod:m7 ~[0 1] 1 ~[1 0 1]))
  ==
++  test-p2-mx-egcd
  ::  0 * (x^2 - 1) + 1 * (x - 1) = x - 1, monic
  %+  expect-eq
    !>([g=`mol`~[6 1] u=`mol`~ v=`mol`~[1]])
  !>((egcd:m7 ~[6 0 1] ~[6 1]))
::  Property: a = q*b + r with deg r < deg b, over several primes.
++  test-p2-mx-divmod-reconstructs
  =/  ps=(list @ud)  ~[2 3 5 7 97]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [x=zol y=zol]
  %+  levy  ps
  |=  p=@ud
  =/  d  ~(. mx p)
  =/  a  (to-mol x p)
  =/  b  (to-mol y p)
  ?~  b  %.y
  =/  dm  (divmod:d a b)
  ?&  =(a (add:d (mul:d q.dm b) r.dm))
      ?|(=(~ r.dm) (lth (deg:d r.dm) (deg:d b)))
  ==
::  Property: the Bezout identity for +egcd, and that g is monic.
++  test-p2-mx-egcd-bezout
  =/  ps=(list @ud)  ~[2 3 5 7 97]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [x=zol y=zol]
  %+  levy  ps
  |=  p=@ud
  =/  d  ~(. mx p)
  =/  a  (to-mol x p)
  =/  b  (to-mol y p)
  =/  e  (egcd:d a b)
  ?&  =(g.e (add:d (mul:d u.e a) (mul:d v.e b)))
      ?|(=(~ g.e) =(1 (lc:d g.e)))
  ==
::  Property: gcd is monic and divides both arguments.
++  test-p2-mx-gcd-divides
  =/  ps=(list @ud)  ~[2 3 5 7 97]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [x=zol y=zol]
  %+  levy  ps
  |=  p=@ud
  =/  d  ~(. mx p)
  =/  a  (to-mol x p)
  =/  b  (to-mol y p)
  =/  g  (gcd:d a b)
  ?~  g  ?&(=(~ a) =(~ b))
  ?&  =(1 (lc:d g))
      ?|(=(~ a) =(~ r:(divmod:d a g)))
      ?|(=(~ b) =(~ r:(divmod:d b g)))
  ==
::  Property: powmod agrees with repeated multiplication modulo f.
++  test-p2-mx-powmod-repeated
  =/  ps=(list @ud)  ~[2 3 7]
  =/  es=(list @ud)  ~[0 1 2 5]
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 24))
  |=  [x=zol y=zol]
  %+  levy  ps
  |=  p=@ud
  =/  d  ~(. mx p)
  =/  a  (to-mol x p)
  =/  f  (to-mol y p)
  ?:  (lth (lent f) 2)  %.y
  %+  levy  es
  |=  e=@ud
  =/  want=mol
    =/  i=@ud    e
    =/  acc=mol  r:(divmod:d ~[1] f)
    |-  ^-  mol
    ?:  =(0 i)  acc
    $(i (dec i), acc r:(divmod:d (mul:d acc a) f))
  =((powmod:d a e f) want)
::
+|  %p2-zx
++  test-p2-zx-pdiv
  ;:  weld
    %+  expect-eq
      !>([q=`zol`~[--1 --1] r=`zol`~])
    !>((pdiv:zx ~[-1 --0 --1] ~[-1 --1]))
    ::  deg a < deg b: exponent 0, so the identity reads a = r
    %+  expect-eq
      !>([q=`zol`~ r=`zol`~[--1]])
    !>((pdiv:zx ~[--1] ~[--1 --1]))
    ::  2^2 * (x^2 + 1) = (2x)(2x) + 4
    %+  expect-eq
      !>([q=`zol`~[--0 --2] r=`zol`~[--4]])
    !>((pdiv:zx ~[--1 --0 --1] ~[--0 --2]))
  ==
++  test-p2-zx-content-pp
  ;:  weld
    ::  S7: content(~) = 0
    %+  expect-eq  !>(`@ud`0)  !>((content:zx ~))
    %+  expect-eq  !>(`@ud`2)  !>((content:zx ~[--2 --4 --6]))
    ::  content is always non-negative
    %+  expect-eq  !>(`@ud`2)  !>((content:zx ~[-2 --4]))
    %+  expect-eq  !>(`zol`~)  !>((pp:zx ~))
    %+  expect-eq  !>(`zol`~[--1 --2])  !>((pp:zx ~[--2 --4]))
    ::  pp carries the input's sign, since content * pp = input exactly
    %+  expect-eq  !>(`zol`~[-1 --2])   !>((pp:zx ~[-2 --4]))
  ==
++  test-p2-zx-gcd
  ;:  weld
    %+  expect-eq  !>(`zol`~[-1 --1])  !>((gcd:zx ~[-1 --0 --1] ~[-1 --1]))
    %+  expect-eq  !>(`zol`~[--1])     !>((gcd:zx ~[--1 --0 --1] ~[--1 --1]))
    ::  content is carried through: gcd(2,4) * (1 + 2x)
    %+  expect-eq
      !>(`zol`~[--2 --4])
    !>((gcd:zx ~[--2 --4] ~[--4 --8]))
    %+  expect-eq  !>(`zol`~[--1])  !>((gcd:zx ~[--6 --0 --0 --2] ~[--3 --3]))
  ==
::  S7: gcd(~, ~) = ~, and gcd(a, ~) is the WHOLE polynomial normalized to
::  positive lc -- content included, not just the primitive part.
++  test-p2-zx-gcd-zero
  ;:  weld
    %+  expect-eq  !>(`zol`~)           !>((gcd:zx ~ ~))
    %+  expect-eq  !>(`zol`~[-2 --4])   !>((gcd:zx ~[-2 --4] ~))
    %+  expect-eq  !>(`zol`~[-2 --4])   !>((gcd:zx ~ ~[-2 --4]))
    ::  negative lc is negated, which flips the sign of the content too
    %+  expect-eq  !>(`zol`~[-2 --4])   !>((gcd:zx ~[--2 -4] ~))
  ==
++  test-p2-zx-res
  ;:  weld
    %+  expect-eq  !>(`@s`--0)  !>((res:zx ~[-1 --0 --1] ~[-1 --1]))
    %+  expect-eq  !>(`@s`--2)  !>((res:zx ~[--1 --0 --1] ~[--1 --1]))
    %+  expect-eq  !>(`@s`-2)   !>((res:zx ~[-2 --0 --1] ~[--0 --1]))
    ::  S9: either argument ~ gives --0
    %+  expect-eq  !>(`@s`--0)  !>((res:zx ~ ~[--1]))
    %+  expect-eq  !>(`@s`--0)  !>((res:zx ~[--1] ~))
    ::  S9 pinned degree-0 conventions: lc(a)^(deg b), and symmetrically
    %+  expect-eq  !>(`@s`--5)  !>((res:zx ~[--5] ~[--1 --1]))
    %+  expect-eq  !>(`@s`--3)  !>((res:zx ~[--1 --1] ~[--3]))
    ::  higher degree, where the subresultant PRS actually iterates
    %+  expect-eq
      !>(`@s`--162.000)
    !>((res:zx ~[--1 --2 --3 --4 --5] ~[--5 --4 --3 --2 --1]))
    %+  expect-eq
      !>(`@s`-196.975)
    !>((res:zx ~[--1 --0 -1 --0 --1 --0 --0 --1] ~[--2 --3 --0 --5 --1]))
  ==
++  test-p2-zx-disc
  ;:  weld
    %+  expect-eq  !>(`@s`--4)  !>((disc:zx ~[-1 --0 --1]))
    %+  expect-eq  !>(`@s`-4)   !>((disc:zx ~[--1 --0 --1]))
    ::  a repeated root gives discriminant zero
    %+  expect-eq  !>(`@s`--0)  !>((disc:zx ~[--1 --2 --1]))
    %+  expect-eq  !>(`@s`--1)  !>((disc:zx ~[--2 --3 --1]))
    %+  expect-eq  !>(`@s`--4)  !>((disc:zx ~[--6 --11 --6 --1]))
    %+  expect-eq  !>(`@s`--8)  !>((disc:zx ~[-2 --0 --1]))
  ==
++  test-p2-zx-mig
  ;:  weld
    %+  expect-eq  !>(`@ud`0)   !>((mig:zx ~))
    ::  2^1 * (isqrt(2) + 1) * 1
    %+  expect-eq  !>(`@ud`4)   !>((mig:zx ~[--1 --1]))
    ::  2^2 * (isqrt(3) + 1) * 5
    %+  expect-eq  !>(`@ud`40)  !>((mig:zx ~[--3 --0 -5]))
    ::  2^3 * (isqrt(4) + 1) * 2
    %+  expect-eq  !>(`@ud`48)  !>((mig:zx ~[--1 --0 --0 --2]))
  ==
::  Property: the pinned pseudo-division identity, which is what fixes q and r.
++  test-p2-zx-pdiv-identity
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 40))
  |=  [a=zol b=zol]
  ?~  b  %.y
  =/  dm  (pdiv:zx a b)
  =/  e=@ud
    ?:  |(=(~ a) (lth (deg:zx a) (deg:zx b)))  0
    +((sub (deg:zx a) (deg:zx b)))
  =/  lhs=zol  (scale:zx a (ipow (lc:zx b) e))
  ?&  =(lhs (add:zx (mul:zx q.dm b) r.dm))
      ?|(=(~ r.dm) (lth (deg:zx r.dm) (deg:zx b)))
  ==
::  Property: content * pp = input, exactly, and pp is primitive.
++  test-p2-zx-content-identity
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 40)
  |=  a=zol
  ?~  a  =(0 (content:zx a))
  =/  c=@ud  (content:zx a)
  ?&  (gth c 0)
      =(a (scale:zx (pp:zx a) (sun:si c)))
      =(1 (content:zx (pp:zx a)))
  ==
::  Property: the gcd divides both arguments and has positive lc.  This is
::  the certification the modular algorithm performs internally, checked
::  here from the outside.
++  test-p2-zx-gcd-divides
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [a=zol b=zol]
  =/  g  (gcd:zx a b)
  ?:  ?&(=(~ a) =(~ b))  =(~ g)
  ?~  g  %.n
  ?&  (syn:si (lc:zx g))
      ?|(=(~ a) =(~ r:(pdiv:zx a g)))
      ?|(=(~ b) =(~ r:(pdiv:zx b g)))
  ==
::  Property: a constructed common factor divides the computed gcd.
++  test-p2-zx-gcd-constructed
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol zol])
  %+  skip  (ztriples (zols seed-zx 24))
  |=  [g=zol a=zol b=zol]
  ?:  ?|(=(~ g) =(~ a) =(~ b))  %.y
  =/  x  (mul:zx g a)
  =/  y  (mul:zx g b)
  =/  d  (gcd:zx x y)
  ?~  d  %.n
  ::  g divides the gcd, up to content and sign
  =(~ r:(pdiv:zx d (pp:zx g)))
::  Property: res(a, b) = 0 exactly when the gcd is nonconstant (S11.3).
++  test-p2-zx-res-gcd
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [a=zol b=zol]
  ?:  |(=(~ a) =(~ b))  %.y
  =/  r  (res:zx a b)
  =/  g  (gcd:zx a b)
  =/  nonconstant=?  ?&(?!(=(~ g)) (gth (lent g) 1))
  =(=(--0 r) nonconstant)
::
+|  %p2-qx
++  test-p2-qx-arith
  ;:  weld
    %+  expect-eq
      !>(`qol`~[[--5 6]])
    !>((add:qx ~[[--1 2]] ~[[--1 3]]))
    %+  expect-eq
      !>(`qol`~[[--1 3]])
    !>((mul:qx ~[[--1 2]] ~[[--2 3]]))
    %+  expect-eq  !>(`qol`~)  !>((sub:qx ~[[--1 2]] ~[[--1 2]]))
    ::  (1/2 + x) at x = 2 is 5/2
    %+  expect-eq
      !>(`frac`[--5 2])
    !>((eval:qx ~[[--1 2] [--1 1]] [--2 1]))
    %+  expect-eq  !>(`frac`[--3 4])  !>((lc:qx ~[[--1 2] [--3 4]]))
    %+  expect-eq  !>(`ord`%gt)  !>((pcmp:qx ~[[--1 2]] ~[[--1 3]]))
  ==
++  test-p2-qx-divmod
  ;:  weld
    %+  expect-eq
      !>([q=`qol`~[[--1 1] [--1 1]] r=`qol`~])
    !>((divmod:qx ~[[-1 1] [--0 1] [--1 1]] ~[[-1 1] [--1 1]]))
    ::  1 divided by 2/3 is 3/2, exactly -- Q is a field
    %+  expect-eq
      !>([q=`qol`~[[--3 2]] r=`qol`~])
    !>((divmod:qx ~[[--1 1]] ~[[--2 3]]))
  ==
++  test-p2-qx-gcd
  ;:  weld
    ::  monic
    %+  expect-eq
      !>(`qol`~[[-1 1] [--1 1]])
    !>((gcd:qx ~[[-1 1] [--0 1] [--1 1]] ~[[-1 1] [--1 1]]))
    ::  denominators are cleared before delegating to +gcd:zx
    %+  expect-eq
      !>(`qol`~[[-1 1] [--1 1]])
    !>((gcd:qx ~[[-1 2] [--0 1] [--1 2]] ~[[-1 3] [--1 3]]))
    %+  expect-eq  !>(`qol`~)  !>((gcd:qx ~ ~))
  ==
::  Property: a = q*b + r with deg r < deg b, over Q.
++  test-p2-qx-divmod-reconstructs
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 30))
  |=  [x=zol y=zol]
  =/  a  (to-qol x)
  =/  b  (to-qol y)
  ?~  b  %.y
  =/  dm  (divmod:qx a b)
  ?&  =(a (add:qx (mul:qx q.dm b) r.dm))
      ?|(=(~ r.dm) (lth (deg:qx r.dm) (deg:qx b)))
  ==
::  Property: the gcd is monic and divides both arguments exactly.
++  test-p2-qx-gcd-divides
  %+  expect-eq  !>(~)
  !>  ^-  (list [zol zol])
  %+  skip  (zpairs (zols seed-zx 24))
  |=  [x=zol y=zol]
  =/  a  (to-qol x)
  =/  b  (to-qol y)
  =/  g  (gcd:qx a b)
  ?:  ?&(=(~ a) =(~ b))  =(~ g)
  ?~  g  %.n
  ?&  =([--1 1] (lc:qx g))
      ?|(=(~ a) =(~ r:(divmod:qx a g)))
      ?|(=(~ b) =(~ r:(divmod:qx b g)))
  ==
::
+|  %p2-crashes
::  S8: +divmod (mx) crashes on b = ~, and on a non-unit leading coefficient.
++  test-p2-crash-mx-divmod-zero
  (expect-fail |.((divmod:m7 ~[1] ~)))
++  test-p2-crash-mx-divmod-non-unit
  ;:  weld
    ::  2 is a zero divisor mod 6, so it has no inverse
    (expect-fail |.((divmod:m6 ~[1 1] ~[0 2])))
    (expect-fail |.((divmod:m6 ~[1 1] ~[0 3])))
  ==
::  S8: +powmod (mx) crashes on f = ~ and on deg f < 1.
++  test-p2-crash-mx-powmod-modulus
  ;:  weld
    (expect-fail |.((powmod:m7 ~[1] 2 ~)))
    (expect-fail |.((powmod:m7 ~[1] 2 ~[3])))
  ==
::  S8: +pdiv (zx) crashes on b = ~.
++  test-p2-crash-zx-pdiv-zero
  ;:  weld
    (expect-fail |.((pdiv:zx ~[--1] ~)))
    (expect-fail |.((pdiv:zx ~ ~)))
  ==
::  S9: +disc (zx) crashes on deg a < 1, which includes the zero polynomial.
++  test-p2-crash-zx-disc-degree
  ;:  weld
    (expect-fail |.((disc:zx ~[--5])))
    (expect-fail |.((disc:zx ~)))
  ==
::  S8: +divmod (qx) crashes on b = ~.
++  test-p2-crash-qx-divmod-zero
  (expect-fail |.((divmod:qx ~[[--1 1]] ~)))
++  test-p2-crash-qx-deg-lc-zero
  ;:  weld
    (expect-fail |.((deg:qx ~)))
    (expect-fail |.((lc:qx ~)))
  ==
::  The Phase 2 arms that must NOT crash.
++  test-p2-nocrash
  ;:  weld
    ::  gcd is total in every ring
    (expect-success |.((gcd:m7 ~ ~)))
    (expect-success |.((gcd:zx ~ ~)))
    (expect-success |.((gcd:qx ~ ~)))
    (expect-success |.((res:zx ~ ~)))
    (expect-success |.((content:zx ~)))
    (expect-success |.((pp:zx ~)))
    (expect-success |.((mig:zx ~)))
    (expect-success |.((egcd:m7 ~ ~)))
    ::  a degree-0 modulus is fine for divmod, unlike for powmod
    (expect-success |.((divmod:m7 ~[1 1] ~[3])))
  ==
::
+|  %p3-mx
::  Phase 3: factorization over F_p.
::
++  test-p3-mx-factor-char2
  ;:  weld
    ::  (1 + x)^3
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 3]]])
    !>((factor:m2 ~[1 1 1 1]))
    ::  1 + x^2 = (1 + x)^2 in characteristic 2
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 2]]])
    !>((factor:m2 ~[1 0 1]))
    ::  x^3 + x + 1 is irreducible over F_2
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1 0 1] 1]]])
    !>((factor:m2 ~[1 1 0 1]))
    ::  x + x^3 = x(1 + x)^2
    %+  expect-eq
      !>(`mfac`[1 ~[[~[0 1] 1] [~[1 1] 2]]])
    !>((factor:m2 ~[0 1 0 1]))
  ==
++  test-p3-mx-factor-odd
  ;:  weld
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 1] [~[2 1] 1]]])
    !>((factor:m3 ~[2 0 1]))
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 1] [~[6 1] 1]]])
    !>((factor:m7 ~[6 0 1]))
    ::  x^2 + 1 has no root mod 7, so it is irreducible there
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 0 1] 1]]])
    !>((factor:m7 ~[1 0 1]))
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 2]]])
    !>((factor:m7 ~[1 2 1]))
  ==
::  The f' = 0 path: every exponent divisible by p, so f = g(x^p) and the
::  p-th root has to be taken.  A char-0 algorithm has no such case.
++  test-p3-mx-factor-pth-root
  ;:  weld
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 3]]])
    !>((factor:m3 ~[1 0 0 1]))
    %+  expect-eq
      !>(`mfac`[1 ~[[~[2 1] 3]]])
    !>((factor:m3 ~[2 0 0 1]))
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 6]]])
    !>((factor:m2 ~[1 0 1 0 1 0 1]))
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 5]]])
    !>((factor:~(. mx 5) ~[1 0 0 0 0 1]))
    ::  (x - 1)^8 over F_3, which needs the root taken twice
    %+  expect-eq
      !>(`mfac`[1 ~[[~[2 1] 8]]])
    !>((factor:m3 ~[1 1 1 1 1 1 1 1 1]))
  ==
++  test-p3-mx-sqfree
  ;:  weld
    ::  the parts are squarefree, not necessarily irreducible
    %+  expect-eq
      !>(`mfac`[1 ~[[~[1 1] 2]]])
    !>((sqfree:m7 ~[1 2 1]))
    %+  expect-eq
      !>(`mfac`[1 ~[[~[6 0 1] 1]]])
    !>((sqfree:m7 ~[6 0 1]))
  ==
::  Property: exact reconstruction over F_p.  SPEC S11.3 makes this the
::  load-bearing factorization test -- the reassembled product must equal
::  the input noun-for-noun.
++  test-p3-mx-reconstructs
  =/  ps=(list @ud)  ~[2 3 5 7]
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 24)
  |=  x=zol
  %+  levy  ps
  |=  p=@ud
  =/  d  ~(. mx p)
  =/  a  (to-mol x p)
  ?~  a  %.y
  =/  fc  (factor:d a)
  =/  re=mol
    =/  acc=mol  ~[c.fc]
    =/  fs=(list [p=mol m=@ud])  fs.fc
    |-  ^-  mol
    ?~  fs  acc
    =/  pw=mol
      =/  i=@ud    m.i.fs
      =/  z=mol    ~[1]
      |-  ^-  mol
      ?:  =(0 i)  z
      $(i (dec i), z (mul:d z p.i.fs))
    $(fs t.fs, acc (mul:d acc pw))
  =(a re)
::  Property: every factor is monic, multiplicities are positive, and the
::  factors are strictly ascending -- hence sorted and pairwise distinct.
++  test-p3-mx-canonical
  =/  ps=(list @ud)  ~[2 3 5 7]
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 24)
  |=  x=zol
  %+  levy  ps
  |=  p=@ud
  =/  d  ~(. mx p)
  =/  a  (to-mol x p)
  ?~  a  %.y
  =/  fc  (factor:d a)
  ?&  %+  levy  fs.fc
      |=([q=mol m=@ud] ?&(?!(=(~ q)) =(1 (lc:d q)) (gth m 0)))
      =/  fs=(list [p=mol m=@ud])  fs.fc
      |-  ^-  ?
      ?~  fs  %.y
      ?~  t.fs  %.y
      ?&(=(%lt (pcmp:d p.i.fs p.i.t.fs)) $(fs t.fs))
  ==
::
+|  %p3-zx
++  test-p3-zx-sqfree
  ;:  weld
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[-1 --0 --1] 1]]])
    !>((sqfree:zx ~[-1 --0 --1]))
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --1] 2]]])
    !>((sqfree:zx ~[--1 --2 --1]))
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--0 --1] 2] [~[--1 --1] 1]]])
    !>((sqfree:zx ~[--0 --0 --1 --1]))
    ::  content and sign are stripped into c
    %+  expect-eq
      !>(`zfac`[--2 ~[[~[--1 --2] 1]]])
    !>((sqfree:zx ~[--2 --4]))
    %+  expect-eq
      !>(`zfac`[-2 ~[[~[--1 --2] 1]]])
    !>((sqfree:zx ~[-2 -4]))
    %+  expect-eq
      !>(`zfac`[--8 ~[[~[--0 --1] 3]]])
    !>((sqfree:zx ~[--0 --0 --0 --8]))
  ==
++  test-p3-zx-factor
  ;:  weld
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[-1 --1] 1] [~[--1 --1] 1]]])
    !>((factor:zx ~[-1 --0 --1]))
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --1] 2]]])
    !>((factor:zx ~[--1 --2 --1]))
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --1] 1] [~[--2 --1] 1]]])
    !>((factor:zx ~[--2 --3 --1]))
    ::  three linear factors
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --1] 1] [~[--2 --1] 1] [~[--3 --1] 1]]])
    !>((factor:zx ~[--6 --11 --6 --1]))
    ::  x^4 - 1: two linear and one quadratic, so +pcmp must order by
    ::  degree before coefficients
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[-1 --1] 1] [~[--1 --1] 1] [~[--1 --0 --1] 1]]])
    !>((factor:zx ~[-1 --0 --0 --0 --1]))
  ==
++  test-p3-zx-factor-irreducible
  ;:  weld
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --0 --1] 1]]])
    !>((factor:zx ~[--1 --0 --1]))
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[-2 --0 --1] 1]]])
    !>((factor:zx ~[-2 --0 --1]))
    ::  the fifth cyclotomic: factors mod every prime, irreducible over Z
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --1 --1 --1 --1] 1]]])
    !>((factor:zx ~[--1 --1 --1 --1 --1]))
  ==
::  Swinnerton-Dyer.  These are irreducible over Z yet split into linear or
::  quadratic factors modulo EVERY prime, so recombination must reject every
::  proper subset before concluding.  SPEC S13 requires SD_3 to pass; SD_4
::  and beyond are out of scope until a van Hoeij milestone.
++  test-p3-zx-swinnerton-dyer
  ;:  weld
    %+  expect-eq
      !>(`zfac`[--1 ~[[~[--1 --0 -10 --0 --1] 1]]])
    !>((factor:zx ~[--1 --0 -10 --0 --1]))
    %+  expect-eq
      !>  ^-  zfac
      :-  --1
      ~[[~[--576 --0 -960 --0 --352 --0 -40 --0 --1] 1]]
    !>((factor:zx ~[--576 --0 -960 --0 --352 --0 -40 --0 --1]))
  ==
++  test-p3-zx-factor-content
  ;:  weld
    %+  expect-eq
      !>(`zfac`[--2 ~[[~[--1 --2] 1]]])
    !>((factor:zx ~[--2 --4]))
    %+  expect-eq
      !>(`zfac`[--2 ~[[~[-3 --0 --0 --1] 1]]])
    !>((factor:zx ~[-6 --0 --0 --2]))
    ::  S8: a degree-0 input factors as [c ~], with no crash
    %+  expect-eq  !>(`zfac`[--5 ~])  !>((factor:zx ~[--5]))
    %+  expect-eq  !>(`zfac`[-5 ~])   !>((factor:zx ~[-5]))
  ==
::  Property: exact reconstruction over Z -- the load-bearing test (S11.3).
++  test-p3-zx-reconstructs
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 24)
  |=  a=zol
  ?~  a  %.y
  =/  fc  (factor:zx a)
  =/  re=zol
    =/  acc=zol  ~[c.fc]
    =/  fs=(list [p=zol m=@ud])  fs.fc
    |-  ^-  zol
    ?~  fs  acc
    =/  pw=zol
      =/  i=@ud    m.i.fs
      =/  z=zol    ~[--1]
      |-  ^-  zol
      ?:  =(0 i)  z
      $(i (dec i), z (mul:zx z p.i.fs))
    $(fs t.fs, acc (mul:zx acc pw))
  =(a re)
::  Property: factors are primitive with positive lc, multiplicities are
::  positive, and the list is strictly ascending.
++  test-p3-zx-canonical
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 24)
  |=  a=zol
  ?~  a  %.y
  =/  fc  (factor:zx a)
  ?&  %+  levy  fs.fc
      |=  [q=zol m=@ud]
      ?&  ?!(=(~ q))
          (syn:si (lc:zx q))
          =(1 (content:zx q))
          (gth m 0)
      ==
      =/  fs=(list [p=zol m=@ud])  fs.fc
      |-  ^-  ?
      ?~  fs  %.y
      ?~  t.fs  %.y
      ?&(=(%lt (pcmp:zx p.i.fs p.i.t.fs)) $(fs t.fs))
  ==
::  Property: +sqfree parts are pairwise coprime and squarefree, and
::  reassemble to the input exactly.
++  test-p3-zx-sqfree-reconstructs
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  (zols seed-zx 32)
  |=  a=zol
  ?~  a  %.y
  =/  fc  (sqfree:zx a)
  =/  re=zol
    =/  acc=zol  ~[c.fc]
    =/  fs=(list [p=zol m=@ud])  fs.fc
    |-  ^-  zol
    ?~  fs  acc
    =/  pw=zol
      =/  i=@ud    m.i.fs
      =/  z=zol    ~[--1]
      |-  ^-  zol
      ?:  =(0 i)  z
      $(i (dec i), z (mul:zx z p.i.fs))
    $(fs t.fs, acc (mul:zx acc pw))
  ?&  =(a re)
      ::  each part is squarefree: its gcd with its own derivative is a
      ::  constant, i.e. has no repeated root
      %+  levy  fs.fc
      |=  [q=zol m=@ud]
      ?|  (lth (lent q) 2)
          =(1 (lent (gcd:zx q (tderiv q))))
      ==
  ==
::
+|  %p3-crashes
::  S8: factoring the zero polynomial is undefined in every ring.
++  test-p3-crash-factor-zero
  ;:  weld
    (expect-fail |.((factor:zx ~)))
    (expect-fail |.((factor:m7 ~)))
    (expect-fail |.((sqfree:zx ~)))
    (expect-fail |.((sqfree:m7 ~)))
  ==
::  S8: the field-only arms assert primality.
++  test-p3-crash-mx-composite
  ;:  weld
    (expect-fail |.((factor:m6 ~[1 1])))
    (expect-fail |.((sqfree:m6 ~[1 1])))
    (expect-fail |.((ddf:m6 ~[1 1])))
    (expect-fail |.((edf:m6 ~[1 1] 1)))
  ==
++  test-p3-nocrash
  ;:  weld
    ::  S8: a degree-0 input factors as [c ~] rather than crashing
    (expect-success |.((factor:zx ~[--5])))
    (expect-success |.((factor:m7 ~[5])))
    (expect-success |.((sqfree:zx ~[--5])))
    (expect-success |.((ddf:m7 ~[1])))
  ==
::
+|  %p0-vectors
::  Generated reference vectors (SPEC deliverable 3).  The oracle is SymPy and
::  the Python standard library; see tools/genvec.py.  These are the arms that
::  would have caught a wrong hand-written expectation.
::
++  test-p0-vec-gcd
  %+  expect-eq  !>(~)
  !>  %+  skip  gcd-vectors:vec
      |=  [a=@ud b=@ud g=@ud]
      =(g (gcd:nz a b))
::
++  test-p0-vec-egcd
  %+  expect-eq  !>(~)
  !>  %+  skip  egcd-vectors:vec
      |=  [a=@ud b=@ud d=@ud u=@s v=@s]
      =([d u v] (egcd:nz a b))
::
++  test-p0-vec-isqrt
  %+  expect-eq  !>(~)
  !>  %+  skip  isqrt-vectors:vec
      |=  [a=@ud r=@ud]
      =(r (isqrt:nz a))
::
++  test-p0-vec-is-prime
  %+  expect-eq  !>(~)
  !>  %+  skip  is-prime-vectors:vec
      |=  [n=@ud p=?]
      =(p (is-prime:nz n))
::
++  test-p0-vec-crt
  %+  expect-eq  !>(~)
  !>  %+  skip  crt-vectors:vec
      |=  [in=(list [r=@ud m=@ud]) r=@ud m=@ud]
      =([r m] (crt:nz in))
::
++  test-p0-vec-ratrec
  %+  expect-eq  !>(~)
  !>  %+  skip  ratrec-vectors:vec
      |=  [u=@ud m=@ud nb=@ud db=@ud out=(unit frac)]
      =(out (ratrec:nz u m nb db))
::
++  test-p0-vec-qq-add
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-add-vectors:vec
      |=  [a=frac b=frac c=frac]
      =(c (add:qq a b))
::
++  test-p0-vec-qq-sub
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-sub-vectors:vec
      |=  [a=frac b=frac c=frac]
      =(c (sub:qq a b))
::
++  test-p0-vec-qq-mul
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-mul-vectors:vec
      |=  [a=frac b=frac c=frac]
      =(c (mul:qq a b))
::
++  test-p0-vec-qq-div
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-div-vectors:vec
      |=  [a=frac b=frac c=frac]
      =(c (div:qq a b))
::
++  test-p0-vec-qq-cmp
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-cmp-vectors:vec
      |=  [a=frac b=frac o=ord]
      =(o (cmp:qq a b))
::
++  test-p0-vec-qq-new
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-new-vectors:vec
      |=  [p=@s q=@ud c=frac]
      =(c (new:qq p q))
::
++  test-p0-vec-qq-neg
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-neg-vectors:vec
      |=  [a=frac c=frac]
      =(c (neg:qq a))
::
++  test-p0-vec-qq-inv
  %+  expect-eq  !>(~)
  !>  %+  skip  qq-inv-vectors:vec
      |=  [a=frac c=frac]
      =(c (inv:qq a))
::
+|  %p1-vectors
::  Oracle is sympy.Poly over ZZ; see tools/genvec.py.
::
++  test-p1-vec-zx-canon
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-canon-vectors:vec
      |=  [in=zol out=zol]
      =(out (canon:zx in))
::
++  test-p1-vec-zx-deg
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-deg-vectors:vec
      |=  [a=zol d=@ud]
      =(d (deg:zx a))
::
++  test-p1-vec-zx-lc
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-lc-vectors:vec
      |=  [a=zol c=@s]
      =(c (lc:zx a))
::
++  test-p1-vec-zx-pcmp
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-pcmp-vectors:vec
      |=  [a=zol b=zol o=ord]
      =(o (pcmp:zx a b))
::
++  test-p1-vec-zx-add
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-add-vectors:vec
      |=  [a=zol b=zol c=zol]
      =(c (add:zx a b))
::
++  test-p1-vec-zx-sub
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-sub-vectors:vec
      |=  [a=zol b=zol c=zol]
      =(c (sub:zx a b))
::
++  test-p1-vec-zx-mul
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-mul-vectors:vec
      |=  [a=zol b=zol c=zol]
      =(c (mul:zx a b))
::
++  test-p1-vec-zx-neg
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-neg-vectors:vec
      |=  [a=zol c=zol]
      =(c (neg:zx a))
::
++  test-p1-vec-zx-shift
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-shift-vectors:vec
      |=  [a=zol k=@ud c=zol]
      =(c (shift:zx a k))
::
++  test-p1-vec-zx-scale
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-scale-vectors:vec
      |=  [a=zol c=@s out=zol]
      =(out (scale:zx a c))
::
++  test-p1-vec-zx-eval
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-eval-vectors:vec
      |=  [a=zol x=@s y=@s]
      =(y (eval:zx a x))
::
::  +mx families.  Each case carries its own modulus, so the door is built
::  per case.  The oracle computes over ZZ and reduces afterwards, which is
::  independent of the Hoon's reduce-at-every-step convolution.
::
++  test-p1-vec-mx-cadd
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-cadd-vectors:vec
      |=  [n=@ud a=@ud b=@ud c=@ud]
      =(c (cadd:~(. mx n) a b))
::
++  test-p1-vec-mx-csub
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-csub-vectors:vec
      |=  [n=@ud a=@ud b=@ud c=@ud]
      =(c (csub:~(. mx n) a b))
::
++  test-p1-vec-mx-cmul
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-cmul-vectors:vec
      |=  [n=@ud a=@ud b=@ud c=@ud]
      =(c (cmul:~(. mx n) a b))
::
++  test-p1-vec-mx-cneg
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-cneg-vectors:vec
      |=  [n=@ud a=@ud c=@ud]
      =(c (cneg:~(. mx n) a))
::
++  test-p1-vec-mx-cinv
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-cinv-vectors:vec
      |=  [n=@ud a=@ud c=@ud]
      =(c (cinv:~(. mx n) a))
::
++  test-p1-vec-mx-cpow
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-cpow-vectors:vec
      |=  [n=@ud a=@ud e=@ud c=@ud]
      =(c (cpow:~(. mx n) a e))
::
++  test-p1-vec-mx-canon
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-canon-vectors:vec
      |=  [n=@ud in=mol out=mol]
      =(out (canon:~(. mx n) in))
::
++  test-p1-vec-mx-deg
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-deg-vectors:vec
      |=  [n=@ud a=mol d=@ud]
      =(d (deg:~(. mx n) a))
::
++  test-p1-vec-mx-lc
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-lc-vectors:vec
      |=  [n=@ud a=mol c=@ud]
      =(c (lc:~(. mx n) a))
::
++  test-p1-vec-mx-pcmp
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-pcmp-vectors:vec
      |=  [n=@ud a=mol b=mol o=ord]
      =(o (pcmp:~(. mx n) a b))
::
++  test-p1-vec-mx-add
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-add-vectors:vec
      |=  [n=@ud a=mol b=mol c=mol]
      =(c (add:~(. mx n) a b))
::
++  test-p1-vec-mx-sub
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-sub-vectors:vec
      |=  [n=@ud a=mol b=mol c=mol]
      =(c (sub:~(. mx n) a b))
::
++  test-p1-vec-mx-mul
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-mul-vectors:vec
      |=  [n=@ud a=mol b=mol c=mol]
      =(c (mul:~(. mx n) a b))
::
++  test-p1-vec-mx-neg
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-neg-vectors:vec
      |=  [n=@ud a=mol c=mol]
      =(c (neg:~(. mx n) a))
::
++  test-p1-vec-mx-shift
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-shift-vectors:vec
      |=  [n=@ud a=mol k=@ud c=mol]
      =(c (shift:~(. mx n) a k))
::
++  test-p1-vec-mx-scale
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-scale-vectors:vec
      |=  [n=@ud a=mol c=@ud out=mol]
      =(out (scale:~(. mx n) a c))
::
++  test-p1-vec-mx-eval
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-eval-vectors:vec
      |=  [n=@ud a=mol x=@ud y=@ud]
      =(y (eval:~(. mx n) a x))
::
+|  %p2-vectors
::  Oracles: sympy over ZZ / GF(p) / QQ.  The identity-defined arms (+pdiv,
::  +divmod, +pp) are checked in genvec.py against their defining identity
::  rather than against a reimplementation of the loop.
::
++  test-p2-vec-zx-pdiv
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-pdiv-vectors:vec
      |=  [a=zol b=zol q=zol r=zol]
      =([q r] (pdiv:zx a b))
::
++  test-p2-vec-zx-content
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-content-vectors:vec
      |=  [a=zol c=@ud]
      =(c (content:zx a))
::
++  test-p2-vec-zx-pp
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-pp-vectors:vec
      |=  [a=zol c=zol]
      =(c (pp:zx a))
::
++  test-p2-vec-zx-gcd
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-gcd-vectors:vec
      |=  [a=zol b=zol g=zol]
      =(g (gcd:zx a b))
::
++  test-p2-vec-zx-res
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-res-vectors:vec
      |=  [a=zol b=zol r=@s]
      =(r (res:zx a b))
::
++  test-p2-vec-zx-disc
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-disc-vectors:vec
      |=  [a=zol d=@s]
      =(d (disc:zx a))
::
++  test-p2-vec-zx-mig
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-mig-vectors:vec
      |=  [a=zol b=@ud]
      =(b (mig:zx a))
::
++  test-p2-vec-mx-divmod
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-divmod-vectors:vec
      |=  [n=@ud a=mol b=mol q=mol r=mol]
      =([q r] (divmod:~(. mx n) a b))
::
++  test-p2-vec-mx-gcd
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-gcd-vectors:vec
      |=  [n=@ud a=mol b=mol g=mol]
      =(g (gcd:~(. mx n) a b))
::
++  test-p2-vec-mx-powmod
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-powmod-vectors:vec
      |=  [n=@ud a=mol e=@ud f=mol c=mol]
      =(c (powmod:~(. mx n) a e f))
::
++  test-p2-vec-qx-add
  %+  expect-eq  !>(~)
  !>  %+  skip  qx-add-vectors:vec
      |=  [a=qol b=qol c=qol]
      =(c (add:qx a b))
::
++  test-p2-vec-qx-sub
  %+  expect-eq  !>(~)
  !>  %+  skip  qx-sub-vectors:vec
      |=  [a=qol b=qol c=qol]
      =(c (sub:qx a b))
::
++  test-p2-vec-qx-mul
  %+  expect-eq  !>(~)
  !>  %+  skip  qx-mul-vectors:vec
      |=  [a=qol b=qol c=qol]
      =(c (mul:qx a b))
::
++  test-p2-vec-qx-divmod
  %+  expect-eq  !>(~)
  !>  %+  skip  qx-divmod-vectors:vec
      |=  [a=qol b=qol q=qol r=qol]
      =([q r] (divmod:qx a b))
::
++  test-p2-vec-qx-gcd
  %+  expect-eq  !>(~)
  !>  %+  skip  qx-gcd-vectors:vec
      |=  [a=qol b=qol g=qol]
      =(g (gcd:qx a b))
::
++  test-p2-vec-qx-eval
  %+  expect-eq  !>(~)
  !>  %+  skip  qx-eval-vectors:vec
      |=  [a=qol x=frac y=frac]
      =(y (eval:qx a x))
::
+|  %p3-vectors
++  test-p3-vec-zx-sqfree
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-sqfree-vectors:vec
      |=  [a=zol c=@s fs=(list [p=zol m=@ud])]
      =([c fs] (sqfree:zx a))
::
++  test-p3-vec-zx-factor
  %+  expect-eq  !>(~)
  !>  %+  skip  zx-factor-vectors:vec
      |=  [a=zol c=@s fs=(list [p=zol m=@ud])]
      =([c fs] (factor:zx a))
::
++  test-p3-vec-mx-factor
  %+  expect-eq  !>(~)
  !>  %+  skip  mx-factor-vectors:vec
      |=  [n=@ud a=mol c=@ud fs=(list [p=mol m=@ud])]
      =([c fs] (factor:~(. mx n) a))
--
