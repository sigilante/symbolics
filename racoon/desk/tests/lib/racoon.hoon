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
+|  %seeds
::    +seed-nz:  pinned PRNG seed for the +nz property tests
++  seed-nz  0xdead.beef.1234.5678
::    +seed-qq:  pinned PRNG seed for the +qq property tests
++  seed-qq  0xfeed.face.8765.4321
::    +seed-zx:  pinned PRNG seed for the +zx property tests
++  seed-zx  0xc0ff.ee00.1234.abcd
::    +seed-rs:  pinned PRNG seed for the Reed-Solomon property tests
++  seed-rs  0x5eed.5010.0000.0001
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
::
+|  %fmt
::  Rendering and parsing (/lib/racoon-fmt).  The parser makes print o parse
::  a free property test over the whole generated vector corpus: every
::  polynomial the oracle produced must survive a round trip unchanged.
::
++  test-fmt-show-zol
  ;:  weld
    %+  expect-eq  !>("0")        !>((shoz:fmt ~))
    %+  expect-eq  !>("x^2 - 1")  !>((shoz:fmt ~[-1 --0 --1]))
    %+  expect-eq  !>("x + 1")    !>((shoz:fmt ~[--1 --1]))
    ::  coefficient 1 is elided, exponent 1 is elided, zero terms dropped
    %+  expect-eq
      !>("-3x^2 + 2x - 1")
    !>((shoz:fmt ~[-1 --2 -3]))
    %+  expect-eq  !>("5")        !>((shoz:fmt ~[--5]))
    %+  expect-eq  !>("-5")       !>((shoz:fmt ~[-5]))
    %+  expect-eq  !>("x")        !>((shoz:fmt ~[--0 --1]))
    ::  a negative leading term takes a bare minus, never "+ -"
    %+  expect-eq
      !>("-x^2 + 1")
    !>((shoz:fmt ~[--1 --0 -1]))
    ::  SD_3, rendered as it is conventionally written
    %+  expect-eq
      !>("x^8 - 40x^6 + 352x^4 - 960x^2 + 576")
    !>((shoz:fmt ~[--576 --0 -960 --0 --352 --0 -40 --0 --1]))
  ==
++  test-fmt-show-frac
  ;:  weld
    %+  expect-eq  !>("3/4")   !>((shof:fmt [--3 4]))
    %+  expect-eq  !>("-3/4")  !>((shof:fmt [-3 4]))
    ::  an integral rational drops its denominator
    %+  expect-eq  !>("3")     !>((shof:fmt [--3 1]))
    %+  expect-eq  !>("0")     !>((shof:fmt [--0 1]))
  ==
++  test-fmt-show-qol
  ;:  weld
    ::  a fractional coefficient is parenthesized when it carries an x, so
    ::  (1/2)x cannot be misread as 1/(2x)
    %+  expect-eq
      !>("(1/2)x + 3/4")
    !>((shoq:fmt ~[[--3 4] [--1 2]]))
    %+  expect-eq  !>("x^2")  !>((shoq:fmt ~[[--0 1] [--0 1] [--1 1]]))
    %+  expect-eq  !>("0")    !>((shoq:fmt ~))
  ==
++  test-fmt-show-factorization
  ;:  weld
    %+  expect-eq
      !>("(x - 1) * (x + 1)")
    !>((shozf:fmt [--1 ~[[~[-1 --1] 1] [~[--1 --1] 1]]]))
    ::  multiplicities and a leading constant
    %+  expect-eq
      !>("2 * (x + 1)^2")
    !>((shozf:fmt [--2 ~[[~[--1 --1] 2]]]))
    ::  a factorization with no factors is just its constant
    %+  expect-eq  !>("-5")  !>((shozf:fmt [-5 ~]))
  ==
++  test-fmt-parse
  ;:  weld
    %+  expect-eq
      !>(`(unit zol)`[~ ~[-1 --0 --1]])
    !>((redz:fmt 'x^2 - 1'))
    %+  expect-eq
      !>(`(unit zol)`[~ ~[--2 --3]])
    !>((redz:fmt '3x + 2'))
    ::  whitespace is optional
    %+  expect-eq
      !>(`(unit zol)`[~ ~[-5 --2 --0 -1]])
    !>((redz:fmt '-x^3+2x-5'))
    %+  expect-eq  !>(`(unit zol)`[~ ~[--7]])  !>((redz:fmt '7'))
    %+  expect-eq  !>(`(unit zol)`[~ ~])       !>((redz:fmt '0'))
    ::  repeated and out-of-order terms combine, since parsing sums through
    ::  +add:zx rather than placing by index
    %+  expect-eq
      !>(`(unit zol)`[~ ~[--0 --2]])
    !>((redz:fmt 'x + x'))
    %+  expect-eq
      !>((redz:fmt 'x^2 + x + 1'))
    !>((redz:fmt '1 + x + x^2'))
    ::  a bad parse produces ~ rather than crashing
    %+  expect-eq  !>(`(unit zol)`~)  !>((redz:fmt 'x^'))
    %+  expect-eq  !>(`(unit zol)`~)  !>((redz:fmt 'y + 1'))
  ==
++  test-fmt-parse-qol
  ;:  weld
    %+  expect-eq
      !>(`(unit qol)`[~ ~[[--3 4] [--1 2]]])
    !>((redq:fmt '1/2x + 3/4'))
    ::  coefficients are canonicalized on the way in
    %+  expect-eq
      !>(`(unit qol)`[~ ~[[--1 2]]])
    !>((redq:fmt '2/4'))
  ==
::  Property: print o parse is the identity on every Z[x] polynomial the
::  oracle generated -- across the arithmetic, gcd, resultant, and factor
::  families, several hundred distinct polynomials.
++  test-fmt-roundtrip-vectors
  =/  ps=(list zol)
    ;:  weld
      (turn zx-add-vectors:vec |=([a=zol b=zol c=zol] a))
      (turn zx-mul-vectors:vec |=([a=zol b=zol c=zol] c))
      (turn zx-gcd-vectors:vec |=([a=zol b=zol g=zol] g))
      (turn zx-pdiv-vectors:vec |=([a=zol b=zol q=zol r=zol] q))
      (turn zx-factor-vectors:vec |=([a=zol c=@s fs=(list [p=zol m=@ud])] a))
      (turn zx-eval-vectors:vec |=([a=zol x=@s y=@s] a))
    ==
  %+  expect-eq  !>(~)
  !>  ^-  (list zol)
  %+  skip  ps
  |=  a=zol
  =([~ a] (redz:fmt (crip (shoz:fmt a))))
::  Property: the same round trip over Q[x].
++  test-fmt-roundtrip-qol
  =/  ps=(list qol)
    ;:  weld
      (turn qx-add-vectors:vec |=([a=qol b=qol c=qol] a))
      (turn qx-mul-vectors:vec |=([a=qol b=qol c=qol] c))
      (turn qx-gcd-vectors:vec |=([a=qol b=qol g=qol] g))
    ==
  %+  expect-eq  !>(~)
  !>  ^-  (list qol)
  %+  skip  ps
  |=  a=qol
  =([~ a] (redq:fmt (crip (shoq:fmt a))))
::
+|  %rs
::  Reed-Solomon coding (/lib/racoon-rs).  This is the live-utilization
::  workload: an error-correcting code either round-trips data through
::  deliberate corruption or it does not, so its correctness criterion is
::  self-evident and does not depend on matching another implementation.
::
::  All cases use p = 257 with primitive element 3.  Every byte 0-255 is a
::  distinct element of F_257, which is what makes byte data representable
::  without an extension field -- Racoon has none.
::
++  rs4  ~(. rs [257 3 4])
++  rs2  ~(. rs [257 3 2])
++  rs6  ~(. rs [257 3 6])
::
++  test-rs-generator
  ;:  weld
    ::  g(x) = prod (x - 3^i) for i in 1..4
    %+  expect-eq  !>(`mol`~[196 138 169 137 1])  !>(gpoly:rs4)
    ::  degree is exactly nsym, so the coefficient list has nsym + 1 entries
    %+  expect-eq  !>(`@ud`3)  !>((lent gpoly:rs2))
    %+  expect-eq  !>(`@ud`5)  !>((lent gpoly:rs4))
    %+  expect-eq  !>(`@ud`7)  !>((lent gpoly:rs6))
    ::  and it is monic
    %+  expect-eq  !>(`@ud`1)  !>((rear gpoly:rs4))
  ==
++  test-rs-encode
  ;:  weld
    %+  expect-eq
      !>(`(list @ud)`~[1 2 3 122 50 19 138])
    !>((encode:rs4 ~[1 2 3]))
    %+  expect-eq  !>(`(list @ud)`~[5 197 135])  !>((encode:rs2 ~[5]))
    ::  systematic: the message occupies the leading positions untouched
    %+  expect-eq
      !>(`(list @ud)`~[1 2 3])
    !>((unencode:rs4 (encode:rs4 ~[1 2 3])))
    ::  an all-zero message encodes to all zeros
    %+  expect-eq
      !>(`(list @ud)`~[0 0 0 0 0])
    !>((encode:rs2 ~[0 0 0]))
  ==
::  A codeword is a multiple of the generator, which is exactly the
::  statement that every syndrome vanishes.
++  test-rs-syndromes
  ;:  weld
    %+  expect-eq
      !>(`(list @ud)`~[0 0 0 0])
    !>((syndromes:rs4 (encode:rs4 ~[1 2 3])))
    %+  expect-eq
      !>(`(list @ud)`~[0 0])
    !>((syndromes:rs2 (encode:rs2 ~[9 8 7])))
    ::  a corrupted word has at least one nonzero syndrome
    %+  expect-eq
      !>(%.n)
    !>((levy (syndromes:rs4 ~[8 2 3 122 50 19 138]) |=(s=@ud =(0 s))))
  ==
++  test-rs-decode-known
  =/  cw=(list @ud)  ~[1 2 3 122 50 19 138]
  ;:  weld
    ::  a clean word passes through unchanged
    %+  expect-eq  !>(`(unit (list @ud))`[~ cw])  !>((decode:rs4 cw))
    ::  one error, in the message part
    %+  expect-eq
      !>(`(unit (list @ud))`[~ cw])
    !>((decode:rs4 ~[1 7 3 122 50 19 138]))
    ::  two errors, one in the message and one in the parity -- at the
    ::  full correction capacity for nsym = 4
    %+  expect-eq
      !>(`(unit (list @ud))`[~ cw])
    !>((decode:rs4 ~[8 2 3 222 50 19 138]))
  ==
::  THE load-bearing test: encode, corrupt up to cap symbols at arbitrary
::  positions, decode, and require the original codeword back exactly.
::  Nothing here compares against a reference implementation; the property
::  is the specification.
++  test-rs-roundtrip
  =/  ns=(list @ud)  (rng seed-rs 600 257)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 0 39)
  |=  trial=@ud
  =/  base=@ud  (mul trial 15)
  =/  k=@ud     +((mod trial 6))
  =/  msg=(list @ud)
    %+  turn  (gulf 0 (dec k))
    |=(i=@ud (mod (snag (mod (add base i) 600) ns) 257))
  =/  code  (encode:rs4 msg)
  =/  n=@ud  (lent code)
  ::  corrupt 0, 1, or 2 symbols -- at most cap = 2 for nsym = 4
  =/  nerr=@ud  (mod trial 3)
  =/  recv=(list @ud)
    =/  i=@ud           0
    =/  acc=(list @ud)  code
    |-  ^-  (list @ud)
    ?:  (gte i nerr)  acc
    =/  pos=@ud    (mod (add (mul trial 7) (mul i 3)) n)
    =/  bump=@ud   +((mod (snag (mod (add base i) 600) ns) 256))
    =/  was=@ud    (snag pos `(list @ud)`acc)
    $(i +(i), acc (sput:rs4 acc pos (mod (add was bump) 257)))
  =/  got  (decode:rs4 recv)
  ?&  ?!(=(~ got))
      =(code +:got)
      ::  and the message itself comes back
      =(msg (unencode:rs4 +:got))
  ==
::  The same property at nsym = 6, correcting up to three errors.
++  test-rs-roundtrip-6
  =/  ns=(list @ud)  (rng seed-rs 400 257)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 0 23)
  |=  trial=@ud
  =/  base=@ud  (mul trial 13)
  =/  k=@ud     +((mod trial 5))
  =/  msg=(list @ud)
    %+  turn  (gulf 0 (dec k))
    |=(i=@ud (mod (snag (mod (add base i) 400) ns) 257))
  =/  code   (encode:rs6 msg)
  =/  n=@ud  (lent code)
  =/  nerr=@ud  (mod trial 4)
  =/  recv=(list @ud)
    =/  i=@ud           0
    =/  acc=(list @ud)  code
    |-  ^-  (list @ud)
    ?:  (gte i nerr)  acc
    =/  pos=@ud   (mod (add (mul trial 5) (mul i 2)) n)
    =/  bump=@ud  +((mod (snag (mod (add base i) 400) ns) 256))
    =/  was=@ud   (snag pos `(list @ud)`acc)
    $(i +(i), acc (sput:rs6 acc pos (mod (add was bump) 257)))
  =/  got  (decode:rs6 recv)
  ?&(?!(=(~ got)) =(code +:got))
::  Property: corruption in EVERY position is correctable, one at a time.
::  A decoder can be subtly wrong only at the ends -- position 0 or n-1 --
::  because of an off-by-one in the Chien search, so every position is
::  swept rather than sampled.
++  test-rs-every-position
  =/  msg=(list @ud)  ~[11 22 33 44]
  =/  code  (encode:rs4 msg)
  =/  n=@ud  (lent code)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 0 (dec n))
  |=  pos=@ud
  =/  was=@ud  (snag pos `(list @ud)`code)
  =/  recv  (sput:rs4 code pos (mod (add was 137) 257))
  =/  got  (decode:rs4 recv)
  ?&(?!(=(~ got)) =(code +:got))
::  Property: every PAIR of positions is correctable at nsym = 4, which is
::  the capacity.  This is the case a decoder that only ever handled a
::  single error would pass the previous test and fail here.
++  test-rs-every-pair
  =/  msg=(list @ud)  ~[11 22 33]
  =/  code  (encode:rs4 msg)
  =/  n=@ud  (lent code)
  ::  every ordered pair, as a single indexed pass -- a nested +turn under
  ::  +zing does not infer here, both being wet
  =/  pairs=(list [a=@ud b=@ud])
    %+  turn  (gulf 0 (dec (mul n n)))
    |=  k=@ud
    ^-  [a=@ud b=@ud]
    [(div k n) (mod k n)]
  %+  expect-eq  !>(~)
  !>  ^-  (list [a=@ud b=@ud])
  %+  skip  pairs
  |=  [a=@ud b=@ud]
  ?:  =(a b)  %.y
  =/  w1=@ud  (snag a `(list @ud)`code)
  =/  r1  (sput:rs4 code a (mod (add w1 91) 257))
  =/  w2=@ud  (snag b `(list @ud)`r1)
  =/  r2  (sput:rs4 r1 b (mod (add w2 173) 257))
  =/  got  (decode:rs4 r2)
  ?&(?!(=(~ got)) =(code +:got))
::  Crash rows.
++  test-rs-crashes
  ;:  weld
    ::  an empty message has nothing to encode
    (expect-fail |.((encode:rs4 ~)))
    ::  a symbol outside the field
    (expect-fail |.((encode:rs4 ~[257])))
    (expect-fail |.((encode:rs4 ~[300 1])))
    (expect-fail |.((decode:rs4 ~[1 2 3 4 5 6 999])))
    ::  a block longer than p - 1 would repeat evaluation points
    (expect-fail |.((encode:rs4 (reap 260 1))))
  ==
::  +decode-upto trades correction power for detection reliability.  This
::  is the only lever that reduces miscorrection without adding parity --
::  the consistency checks one would reach for provably do not help, since
::  a miscorrection is a genuine valid codeword.
++  test-rs-decode-upto
  =/  cw=(list @ud)  ~[1 2 3 122 50 19 138]
  =/  one=(list @ud)  ~[1 7 3 122 50 19 138]
  =/  two=(list @ud)  ~[8 2 3 222 50 19 138]
  ;:  weld
    ::  at maxerr = cap it agrees with +decode exactly
    %+  expect-eq  !>((decode:rs4 two))  !>((decode-upto:rs4 two 2))
    %+  expect-eq  !>((decode:rs4 one))  !>((decode-upto:rs4 one 2))
    ::  capped below the weight of the correction, it refuses
    %+  expect-eq  !>(`(unit (list @ud))`~)  !>((decode-upto:rs4 two 1))
    ::  but still accepts a lighter one
    %+  expect-eq
      !>(`(unit (list @ud))`[~ cw])
    !>((decode-upto:rs4 one 1))
    ::  maxerr = 0 is a pure integrity check: clean words only
    %+  expect-eq  !>(`(unit (list @ud))`[~ cw])  !>((decode-upto:rs4 cw 0))
    %+  expect-eq  !>(`(unit (list @ud))`~)  !>((decode-upto:rs4 one 0))
  ==
++  test-rs-nocrash
  ;:  weld
    ::  a single-symbol message is fine
    (expect-success |.((encode:rs4 ~[0])))
    (expect-success |.((encode:rs4 ~[256])))
    ::  an uncorrectable word produces ~ rather than crashing
    (expect-success |.((decode:rs2 ~[9 9 9 9 9])))
    (expect-success |.((syndromes:rs4 ~[1 2 3 4 5 6 7])))
  ==
::
::  Extension fields (/lib/racoon-fp3).  The second live-utilization
::  client: F_p[x]/(m) built entirely out of +mx polynomial arithmetic,
::  with the Nockchain Goldilocks cubic as the motivating instance.
::
::  Goldilocks vectors were computed independently in Python and are
::  transcribed here, exactly as the Reed-Solomon vectors were.  The small
::  fields F_27 and F_49 are checked EXHAUSTIVELY instead -- 27 and 49
::  elements are few enough that sampling would be a worse test than
::  simply trying everything.
::
::    +gl3:  F_p[x]/(x^3 - x - 1) at the Goldilocks prime, Nockchain's field
++  gl3  ~(. fp [18.446.744.069.414.584.321 ~[18.446.744.069.414.584.320 18.446.744.069.414.584.320 0 1]])
::    +f27:  F_3[x]/(x^3 - x - 1), the same cubic over the smallest prime
::  where it stays irreducible
++  f27  ~(. fp [3 ~[2 2 0 1]])
::    +f49:  F_7[x]/(x^2 + 1), a QUADRATIC -- the door is not cubic-only
++  f49  ~(. fp [7 ~[1 0 1]])
::    +f7x:  the same cubic over F_7, where it is REDUCIBLE (5 is a root).
::  Present only so that +irreducible has a negative case.
++  f7x  ~(. fp [7 ~[6 6 0 1]])
::    +els:  every element of an extension of degree k over F_pr
::
::  Index i in [0, pr^k) written in base pr, little-endian.  Trailing zero
::  coefficients make these non-canonical, so callers reduce them through
::  the field's own +canon -- which also exercises that arm 27 or 49 times.
++  els
  |=  [pr=@ud k=@ud]
  ^-  (list mol)
  =/  tot=@ud  (pow pr k)
  =/  i=@ud    0
  =|  out=(list mol)
  |-  ^-  (list mol)
  ?:  =(i tot)  (flop out)
  =/  e=mol
    =/  j=@ud  0
    =/  v=@ud  i
    =|  cs=mol
    |-  ^-  mol
    ?:  =(j k)  (flop cs)
    $(j +(j), v (div v pr), cs [(mod v pr) cs])
  $(i +(i), out [e out])
::
::    +vecs-fp3:  the Goldilocks operand pairs, for the structural tests
::
::  Same six pairs the vector tests use, so a structural law and a
::  transcribed value are always checked against the same inputs.
++  vecs-fp3
  ^-  (list [mol mol])
  :~
    [~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] ~[15.149.836.622.520.594.227 1.736.392.818.365.009.963 10.750.541.312.280.087.032]]
    [~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] ~[7.713.914.763.314.685.786 4.439.448.776.366.754.703 10.165.027.665.383.847.897]]
    [~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] ~[11.632.994.891.556.335.705 10.754.394.637.803.157.173 1.141.153.371.300.629.929]]
    [~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] ~[10.268.654.918.125.279.152 2.456.641.775.679.608.523 7.731.750.658.069.747.094]]
    [~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] ~[12.580.729.232.405.932.079 1.901.042.282.212.365.707 10.536.861.175.493.410.705]]
    [~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] ~[10.410.757.471.710.933.047 11.418.711.589.407.294.900 9.157.231.070.389.319.135]]
  ==
::
++  test-fp3-goldilocks-mul
  ;:  weld
    %+  expect-eq  !>(`mol`~[10.592.939.488.128.544.169 11.937.663.410.871.179.763 2.369.382.593.281.921.793])  !>((mul:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] ~[15.149.836.622.520.594.227 1.736.392.818.365.009.963 10.750.541.312.280.087.032]))
    %+  expect-eq  !>(`mol`~[11.849.668.667.596.254.297 5.699.062.322.470.157.694 4.460.854.052.477.668.897])  !>((mul:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] ~[7.713.914.763.314.685.786 4.439.448.776.366.754.703 10.165.027.665.383.847.897]))
    %+  expect-eq  !>(`mol`~[15.875.625.163.121.047.325 7.555.602.628.186.295.849 14.454.697.153.828.416.498])  !>((mul:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] ~[11.632.994.891.556.335.705 10.754.394.637.803.157.173 1.141.153.371.300.629.929]))
    %+  expect-eq  !>(`mol`~[3.367.972.451.319.380.774 16.710.018.798.525.813.693 8.696.113.652.008.925.291])  !>((mul:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] ~[10.268.654.918.125.279.152 2.456.641.775.679.608.523 7.731.750.658.069.747.094]))
    %+  expect-eq  !>(`mol`~[15.481.959.137.259.292.424 3.295.097.563.200.132.596 3.276.036.955.049.487.529])  !>((mul:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] ~[12.580.729.232.405.932.079 1.901.042.282.212.365.707 10.536.861.175.493.410.705]))
    %+  expect-eq  !>(`mol`~[17.068.172.796.397.988.111 2.750.331.618.037.449.294 18.251.154.154.780.879.620])  !>((mul:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] ~[10.410.757.471.710.933.047 11.418.711.589.407.294.900 9.157.231.070.389.319.135]))
  ==
++  test-fp3-goldilocks-inv
  ;:  weld
    %+  expect-eq  !>(`mol`~[12.723.468.023.368.378.352 702.075.037.308.433.792 14.408.387.085.894.643.388])  !>((inv:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992]))
    %+  expect-eq  !>(`mol`~[6.808.717.314.311.538.116 18.200.304.465.036.626.763 9.664.175.183.922.223.429])  !>((inv:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368]))
    %+  expect-eq  !>(`mol`~[17.949.377.739.245.621.234 15.047.477.832.519.149.683 5.108.731.974.324.903.550])  !>((inv:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643]))
    %+  expect-eq  !>(`mol`~[2.363.253.709.304.878.555 8.022.684.551.571.270.240 6.448.780.702.247.989.519])  !>((inv:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692]))
    %+  expect-eq  !>(`mol`~[2.957.515.314.407.620.444 16.794.988.912.772.997.060 14.692.297.148.276.400.677])  !>((inv:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632]))
    %+  expect-eq  !>(`mol`~[7.775.676.696.869.884.935 11.311.092.619.121.807.154 10.972.962.206.138.794.958])  !>((inv:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753]))
  ==
++  test-fp3-goldilocks-frob
  ;:  weld
    %+  expect-eq  !>(`mol`~[16.649.451.722.258.662.587 54.953.028.421.272.613 11.367.466.393.749.441.420])  !>((frob:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992]))
    %+  expect-eq  !>(`mol`~[8.791.301.720.535.786.212 12.336.450.217.959.254.623 4.346.739.138.459.173.681])  !>((frob:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368]))
    %+  expect-eq  !>(`mol`~[4.168.264.876.168.382.243 11.770.119.229.225.023.433 3.637.187.437.674.094.759])  !>((frob:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643]))
    %+  expect-eq  !>(`mol`~[3.681.891.593.578.633.383 3.925.650.661.787.884.683 14.757.401.702.049.438.984])  !>((frob:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692]))
    %+  expect-eq  !>(`mol`~[5.163.916.486.540.301.698 9.882.919.573.921.710.380 17.549.889.152.887.464.939])  !>((frob:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632]))
    %+  expect-eq  !>(`mol`~[14.365.609.717.408.355.583 12.242.141.900.291.252.510 15.232.867.628.034.243.478])  !>((frob:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753]))
  ==
++  test-fp3-goldilocks-norm
  ;:  weld
    %+  expect-eq  !>(`@ud`11.241.016.387.895.453.009)  !>((norm:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992]))
    %+  expect-eq  !>(`@ud`11.633.700.033.010.161.688)  !>((norm:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368]))
    %+  expect-eq  !>(`@ud`12.453.535.689.658.829.251)  !>((norm:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643]))
    %+  expect-eq  !>(`@ud`1.243.425.802.586.706.278)  !>((norm:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692]))
    %+  expect-eq  !>(`@ud`9.928.025.544.317.356.374)  !>((norm:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632]))
    %+  expect-eq  !>(`@ud`13.562.233.187.987.041.780)  !>((norm:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753]))
  ==
++  test-fp3-goldilocks-pow
  ;:  weld
    %+  expect-eq  !>(`mol`~[15.505.590.388.589.805.653 16.515.675.872.690.305.082 16.290.383.523.311.901.322])  !>((pow:gl3 ~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] 7))
    %+  expect-eq  !>(`mol`~[5.962.807.838.841.906.076 9.737.786.156.774.950.341 9.246.234.658.943.802.996])  !>((pow:gl3 ~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] 7))
    %+  expect-eq  !>(`mol`~[3.538.916.642.228.569.644 4.251.654.170.301.896.480 17.583.953.274.526.272.507])  !>((pow:gl3 ~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] 7))
    %+  expect-eq  !>(`mol`~[15.051.117.417.199.140.143 2.891.585.061.584.434.944 1.508.287.365.661.100.857])  !>((pow:gl3 ~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] 7))
    %+  expect-eq  !>(`mol`~[11.969.937.174.133.119.552 4.740.750.696.092.204.648 5.029.723.345.589.179.696])  !>((pow:gl3 ~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] 7))
    %+  expect-eq  !>(`mol`~[12.731.444.577.297.748.616 4.203.591.886.033.547.102 6.027.953.068.008.595.039])  !>((pow:gl3 ~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] 7))
  ==
++  test-fp3-shape
  ;:  weld
    %+  expect-eq  !>(`mol`~)     !>(zero:gl3)
    %+  expect-eq  !>(`mol`~[1])  !>(one:gl3)
    %+  expect-eq  !>(`@ud`3)     !>(rank:gl3)
    %+  expect-eq  !>(`@ud`3)     !>(rank:f27)
    %+  expect-eq  !>(`@ud`2)     !>(rank:f49)
    ::  the base field embeds as constant polynomials, reduced mod p
    %+  expect-eq  !>(`mol`~)     !>((emb:gl3 0))
    %+  expect-eq  !>(`mol`~[1])  !>((emb:gl3 1))
    %+  expect-eq  !>(`mol`~[2])  !>((emb:f27 5))
    %+  expect-eq  !>(`mol`~)     !>((emb:f27 3))
    %-  expect      !>((is-zero:gl3 ~))
    %-  expect-fail  |.(?>((is-zero:gl3 ~[1]) ~))
  ==
++  test-fp3-canon
  ;:  weld
    ::  x^3 = x + 1 is the whole content of the modulus
    %+  expect-eq  !>(`mol`~[1 1])  !>((canon:gl3 ~[0 0 0 1]))
    %+  expect-eq  !>(`mol`~[1 1])  !>((canon:f27 ~[0 0 0 1]))
    ::  x^3 + x^2 + x + 1  ->  x^2 + 2x + 2
    %+  expect-eq  !>(`mol`~[2 2 1])  !>((canon:f27 ~[1 1 1 1]))
    ::  the modulus itself is zero in the quotient
    %+  expect-eq  !>(`mol`~)  !>((canon:f27 ~[2 2 0 1]))
    ::  coefficients are folded into [0, p), unlike +canon:mx
    %+  expect-eq  !>(`mol`~[1 2])  !>((canon:f27 ~[7 5]))
    %+  expect-eq  !>(`mol`~[1])    !>((canon:f27 ~[4 3 9]))
    ::  in F_49, x^2 = -1, so a degree-2 input is NOT already reduced
    %+  expect-eq  !>(`mol`~[6])    !>((canon:f49 ~[0 0 1]))
    %+  expect-eq  !>(`mol`~[3 1])  !>((canon:f49 ~[4 1 1]))
  ==
++  test-fp3-irreducible
  ;:  weld
    ::  verified independently before this library was written
    %-  expect  !>(irreducible:gl3)
    %-  expect  !>(irreducible:f27)
    %-  expect  !>(irreducible:f49)
    ::  the same cubic over F_7, where 5 is a root
    %+  expect-eq  !>(`@ud`0)  !>((eval:m7 ~[6 6 0 1] 5))
    %-  expect-fail  |.(?>(irreducible:f7x ~))
  ==
++  test-fp3-crash
  ;:  weld
    ::  zero has no inverse
    (expect-fail |.((inv:gl3 ~)))
    (expect-fail |.((inv:f27 ~)))
    (expect-fail |.((div:gl3 ~[1] ~)))
    ::  and over a REDUCIBLE modulus, neither does a zero divisor: x + 2 is
    ::  x - 5, and 5 is a root of that cubic over F_7
    (expect-fail |.((inv:f7x ~[2 1])))
    ::  while units there still invert, so the crash is discriminating
    (expect-success |.((inv:f7x ~[0 1])))
  ==
++  test-fp3-goldilocks-structure
  =/  as=(list mol)  (turn vecs-fp3 |=([a=mol b=mol] a))
  =/  bs=(list mol)  (turn vecs-fp3 |=([a=mol b=mol] b))
  =/  ord=@ud
    6.277.101.731.002.175.853.884.774.869.567.645.561.244.584.131.361.410.908.160
  =|  out=tang
  |-  ^-  tang
  ?~  as  out
  ?~  bs  out
  %=  $
    as  t.as
    bs  t.bs
    out
      %+  weld  out
      ;:  weld
        ::  inversion round-trips
        %+  expect-eq  !>(`mol`~[1])  !>((mul:gl3 i.as (inv:gl3 i.as)))
        %+  expect-eq  !>(`mol`i.as)  !>((div:gl3 (mul:gl3 i.as i.bs) i.bs))
        ::  every nonzero element satisfies a^(p^3 - 1) = 1
        %+  expect-eq  !>(`mol`~[1])  !>((pow:gl3 i.as ord))
        ::  Frobenius has order equal to the rank
        %+  expect-eq
          !>(`mol`i.as)
        !>((frob:gl3 (frob:gl3 (frob:gl3 i.as))))
        ::  and it is a ring homomorphism
        %+  expect-eq
          !>((frob:gl3 (mul:gl3 i.as i.bs)))
        !>((mul:gl3 (frob:gl3 i.as) (frob:gl3 i.bs)))
        %+  expect-eq
          !>((frob:gl3 (add:gl3 i.as i.bs)))
        !>((add:gl3 (frob:gl3 i.as) (frob:gl3 i.bs)))
        ::  the norm is multiplicative into the base field
        %+  expect-eq
          !>((norm:gl3 (mul:gl3 i.as i.bs)))
        !>((cmul:mgl (norm:gl3 i.as) (norm:gl3 i.bs)))
      ==
  ==
++  test-fp3-goldilocks-base
  ;:  weld
    ::  a base field element's norm is its rank-th power
    %+  expect-eq  !>(`@ud`125)  !>((norm:gl3 (emb:gl3 5)))
    %+  expect-eq  !>(`@ud`0)    !>((norm:gl3 ~))
    %+  expect-eq  !>(`@ud`1)    !>((norm:gl3 ~[1]))
    ::  Frobenius fixes exactly the base field
    %+  expect-eq  !>(`mol`~[5])  !>((frob:gl3 (emb:gl3 5)))
    ::  scaling agrees with multiplying by an embedded scalar
    %+  expect-eq
      !>((scal:gl3 ~[3 4 5] 6))
    !>((mul:gl3 ~[3 4 5] (emb:gl3 6)))
    ::  a^0 is one for every a, including zero
    %+  expect-eq  !>(`mol`~[1])  !>((pow:gl3 ~ 0))
    %+  expect-eq  !>(`mol`~)     !>((pow:gl3 ~ 5))
    %+  expect-eq  !>(`mol`~[3 4 5])  !>((pow:gl3 ~[3 4 5] 1))
  ==
++  test-f27-exhaustive-ring
  =/  es=(list mol)  (turn (els 3 3) |=(e=mol (canon:f27 e)))
  =/  as=(list mol)  es
  =|  out=tang
  |-  ^-  tang
  ?~  as  out
  =/  acc=tang
    =/  bs=(list mol)  es
    |-  ^-  tang
    ?~  bs  ~
    %+  weld
      ;:  weld
        ::  commutative ring laws over all 729 pairs
        %+  expect-eq  !>((mul:f27 i.as i.bs))  !>((mul:f27 i.bs i.as))
        %+  expect-eq  !>((add:f27 i.as i.bs))  !>((add:f27 i.bs i.as))
        %+  expect-eq  !>(`mol`i.as)  !>((sub:f27 (add:f27 i.as i.bs) i.bs))
        %+  expect-eq  !>(`mol`~)     !>((add:f27 i.as (neg:f27 i.as)))
        ::  associativity and distributivity against x
        %+  expect-eq
          !>((mul:f27 (mul:f27 i.as i.bs) ~[0 1]))
        !>((mul:f27 i.as (mul:f27 i.bs ~[0 1])))
        %+  expect-eq
          !>((mul:f27 i.as (add:f27 i.bs ~[0 1])))
        !>((add:f27 (mul:f27 i.as i.bs) (mul:f27 i.as ~[0 1])))
        ::  products stay reduced: at most rank coefficients.  Counted with
        ::  +lent rather than +deg:mx, since +deg crashes on zero (S8) and
        ::  zero is a perfectly ordinary product here.
        %-  expect  !>((lte (lent (mul:f27 i.as i.bs)) 3))
        ::  the norm is multiplicative here too
        %+  expect-eq
          !>((norm:f27 (mul:f27 i.as i.bs)))
        !>((mod (mul (norm:f27 i.as) (norm:f27 i.bs)) 3))
      ==
    $(bs t.bs)
  $(as t.as, out (weld out acc))
++  test-f27-exhaustive-units
  =/  es=(list mol)  (turn (els 3 3) |=(e=mol (canon:f27 e)))
  =|  out=tang
  |-  ^-  tang
  ?~  es  out
  ?:  =(~ i.es)
    ::  zero is the one element with no inverse and zero norm
    %=  $
      es   t.es
      out  (weld out (expect-fail |.((inv:f27 i.es))))
    ==
  =/  e=mol  i.es
  %=  $
    es  t.es
    out
      %+  weld  out
      ;:  weld
        %+  expect-eq  !>(`mol`~[1])  !>((mul:f27 e (inv:f27 e)))
        %+  expect-eq  !>(`mol`~[1])  !>((div:f27 e e))
        ::  the multiplicative group has order 26
        %+  expect-eq  !>(`mol`~[1])  !>((pow:f27 e 26))
        %+  expect-eq  !>(`mol`e)     !>((pow:f27 e 27))
        ::  Frobenius has order 3 and fixes only what it should
        %+  expect-eq  !>(`mol`e)  !>((frob:f27 (frob:f27 (frob:f27 e))))
        ::  a nonzero element has nonzero norm
        %-  expect  !>(!=(0 (norm:f27 e)))
        ::  and +pow agrees with repeated multiplication
        %+  expect-eq  !>((pow:f27 e 3))  !>((mul:f27 (mul:f27 e e) e))
      ==
  ==
++  test-f49-exhaustive
  =/  es=(list mol)  (turn (els 7 2) |=(e=mol (canon:f49 e)))
  =|  out=tang
  |-  ^-  tang
  ?~  es  out
  ?:  =(~ i.es)  $(es t.es)
  =/  e=mol  i.es
  %=  $
    es  t.es
    out
      %+  weld  out
      ;:  weld
        ::  a degree-2 extension: 48 units, Frobenius of order 2
        %+  expect-eq  !>(`mol`~[1])  !>((mul:f49 e (inv:f49 e)))
        %+  expect-eq  !>(`mol`~[1])  !>((pow:f49 e 48))
        %+  expect-eq  !>(`mol`e)     !>((frob:f49 (frob:f49 e)))
        %-  expect  !>((lte (lent e) 2))
        ::  x^2 = -1 = 6, which is the entire modulus
        %+  expect-eq  !>(`mol`~[6])  !>((mul:f49 ~[0 1] ~[0 1]))
      ==
  ==
::    +ascends:  is this list strictly increasing?
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
        %+  expect-eq  !>(`zol`dv.i.vs)  !>((deriv:rr p.i.vs))
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
    %+  expect-eq  !>((deriv:rr p))       !>((snag 1 ch))
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
    (expect-fail |.((deriv:rr ~)))
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
++  test-a0-rationals
  =/  h  (of-q:al [--3 2])
  ;:  weld
    ::  a rational embeds as q*x - p, primitive with positive lc
    %+  expect-eq  !>(`zol`~[-3 --2])  !>(m.h)
    %+  expect-eq  !>(`(unit frac)`[~ [--3 2]])  !>((to-q:al h))
    %+  expect-eq  !>(`@ud`1)  !>((deg:al h))
    %-  expect  !>((is-rational:al h))
    ::  and round-trips
    %+  expect-eq  !>(`(unit frac)`[~ [-7 3]])
    !>((to-q:al (of-q:al [-7 3])))
    %+  expect-eq  !>(`(unit frac)`[~ [--0 1]])  !>((to-q:al zero:al))
    %+  expect-eq  !>(`(unit frac)`[~ [--1 1]])  !>((to-q:al one:al))
    ::  an irrational has no rational value, and degree above 1
    %+  expect-eq  !>(`(unit frac)`~)  !>((to-q:al sq2))
    %+  expect-eq  !>(`@ud`2)  !>((deg:al sq2))
    %-  expect  !>(!(is-rational:al sq2))
    ::  zero is recognized structurally, with no refinement
    %-  expect  !>((is-zero:al zero:al))
    %-  expect  !>(!(is-zero:al sq2))
    %-  expect  !>(!(is-zero:al one:al))
  ==
++  test-a0-make
  ;:  weld
    ::  the minimal polynomial and the canonical interval
    %+  expect-eq  !>(`zol`~[-2 --0 --1])  !>(m:sq2)
    %+  expect-eq  !>(`ivl:rr`[[--0 1] [--3 1]])  !>(iv:sq2)
    %+  expect-eq  !>(`zol`~[-1 -1 --1])  !>(m:phi)
    %+  expect-eq  !>(`zol`~[-2 --0 --0 --1])  !>(m:cb2)
    %+  expect-eq  !>(`@ud`3)  !>((deg:al cb2))
    ::  +make REDUCES to the minimal polynomial: (x^2 - 2)(x^2 - 3) has
    ::  sqrt 2 among its roots, and must come back as x^2 - 2
    %+  expect-eq
      !>(`anum:al`sq2)
    !>((mkr ~[--6 --0 -5 --0 --1] 2))
    ::  a rational root of a bigger polynomial reduces to the rational
    %+  expect-eq
      !>(`(unit frac)`[~ [--1 1]])
    !>((to-q:al (mkr ~[--2 -3 --0 --1] 1)))
    (expect-fail |.((make:al ~ [[--0 1] [--1 1]])))
  ==
++  test-a0-order
  ;:  weld
    ::  equality is STRUCTURAL, so this needs no refinement at all
    %+  expect-eq  !>(`ord`%eq)  !>((cmp:al sq2 sq2))
    %+  expect-eq  !>(`ord`%lt)  !>((cmp:al sq2 sq3))
    %+  expect-eq  !>(`ord`%gt)  !>((cmp:al sq3 sq2))
    ::  against rationals on both sides of the value
    %+  expect-eq  !>(`ord`%gt)  !>((cmp:al sq2 (of-q:al [--1 1])))
    %+  expect-eq  !>(`ord`%lt)  !>((cmp:al sq2 (of-q:al [--2 1])))
    %+  expect-eq  !>(`ord`%gt)  !>((cmp:al sq2 (of-q:al [--7 5])))
    %+  expect-eq  !>(`ord`%lt)  !>((cmp:al sq2 (of-q:al [--3 2])))
    ::  signs
    %+  expect-eq  !>(`ord`%gt)  !>((sign:al sq2))
    %+  expect-eq  !>(`ord`%eq)  !>((sign:al zero:al))
    %+  expect-eq  !>(`ord`%lt)  !>((sign:al (of-q:al [-5 2])))
    %+  expect-eq  !>(`ord`%lt)  !>((sign:al (neg:al sq2)))
    ::  two numbers sharing a minimal polynomial but not an interval are
    ::  NOT equal -- the interval is half the identity, not decoration
    %-  expect  !>(!=((mkr ~[-2 --0 --1] 0) (mkr ~[-2 --0 --1] 1)))
    %+  expect-eq  !>(`ord`%lt)
    !>((cmp:al (mkr ~[-2 --0 --1] 0) (mkr ~[-2 --0 --1] 1)))
  ==
++  test-a0-approx
  ;:  weld
    ::  within 2^-k, checked by bracketing rather than by comparing
    ::  floating-point approximations
    %+  expect-eq  !>(`frac`[--11.583 8.192])  !>((approx:al sq2 10))
    ::  an exact value comes back exactly
    %+  expect-eq  !>(`frac`[--3 2])  !>((approx:al (of-q:al [--3 2]) 20))
    ::  the error really is under the bound: |approx - sqrt2| < 2^-10,
    ::  i.e. (approx)^2 - 2 is small and of the right sign
    %-  expect  !>(=(%lt (cmp:al (of-q:al (approx:al sq2 10)) sq2)))
    %-  expect
    !>  %+  levy  `(list @ud)`~[2 5 10 16]
        |=  k=@ud
        =/  a=frac  (approx:al sq2 k)
        ::  a is within 2^-k, so a + 2^-k is above sqrt 2 and a - 2^-k below
        =/  e=frac  (new:qq --1 (pow 2 k))
        ?&  =(%gt (cmp:al (of-q:al (add:qq a e)) sq2))
            =(%lt (cmp:al (of-q:al (sub:qq a e)) sq2))
        ==
  ==
++  test-a1-unary
  ;:  weld
    ::  p(-x) and the coefficient reversal, neither needing a factoring
    %+  expect-eq  !>(`zol`~[-2 --0 --1])  !>(m:(neg:al sq2))
    %+  expect-eq  !>(`zol`~[-1 --0 --2])  !>(m:(inv:al sq2))
    ::  negation is an involution, and lands on the OTHER root
    %+  expect-eq  !>(`anum:al`sq2)  !>((neg:al (neg:al sq2)))
    %+  expect-eq  !>((mkr ~[-2 --0 --1] 0))  !>((neg:al sq2))
    ::  inversion is an involution
    %+  expect-eq  !>(`anum:al`sq2)  !>((inv:al (inv:al sq2)))
    %+  expect-eq  !>(`anum:al`phi)  !>((inv:al (inv:al phi)))
    ::  the golden ratio's inverse is phi - 1, so x^2 + x - 1
    %+  expect-eq  !>(`zol`~[-1 --1 --1])  !>(m:(inv:al phi))
    ::  and on rationals both stay in Q
    %+  expect-eq  !>(`(unit frac)`[~ [-3 2]])
    !>((to-q:al (neg:al (of-q:al [--3 2]))))
    %+  expect-eq  !>(`(unit frac)`[~ [--2 3]])
    !>((to-q:al (inv:al (of-q:al [--3 2]))))
    ::  zero has no inverse
    (expect-fail |.((inv:al zero:al)))
    (expect-fail |.((div:al sq2 zero:al)))
  ==
++  test-a2-binary
  =/  sum  (add:al sq2 sq3)
  =/  prd  (mul:al sq2 sq3)
  ;:  weld
    ::  sqrt2 + sqrt3 has minimal polynomial x^4 - 10x^2 + 1, which is
    ::  SD_2 -- the same polynomial the factorization tests use
    %+  expect-eq  !>(`zol`~[--1 --0 -10 --0 --1])  !>(m.sum)
    %+  expect-eq  !>(`@ud`4)  !>((deg:al sum))
    ::  THE DEGREE COLLAPSES on the product: the resultant is degree 4
    ::  but sqrt6 has degree 2.  This is the case that fails if the
    ::  factor-and-select step is skipped.
    %+  expect-eq  !>(`zol`~[-6 --0 --1])  !>(m.prd)
    %+  expect-eq  !>(`@ud`2)  !>((deg:al prd))
    ::  commutative
    %+  expect-eq  !>(`anum:al`sum)  !>((add:al sq3 sq2))
    %+  expect-eq  !>(`anum:al`prd)  !>((mul:al sq3 sq2))
    ::  subtraction inverts addition, over irrationals
    %+  expect-eq  !>(`anum:al`sq2)  !>((sub:al sum sq3))
    %+  expect-eq  !>(`anum:al`sq3)  !>((sub:al sum sq2))
    ::  and division inverts multiplication
    %+  expect-eq  !>(`anum:al`sq2)  !>((div:al prd sq3))
    ::  a rational operand keeps working
    %+  expect-eq
      !>(`zol`~[-8 --0 --1])
    !>(m:(mul:al sq2 (of-q:al [--2 1])))
    %+  expect-eq  !>(`ord`%gt)  !>((cmp:al (add:al sq2 one:al) sq2))
  ==
++  test-a2-degenerate
  ::  the cases that MUST come back rational.  A wrong implementation
  ::  looks right on every irrational case and fails only here.
  ;:  weld
    %+  expect-eq  !>(`(unit frac)`[~ [--2 1]])  !>((to-q:al (mul:al sq2 sq2)))
    %+  expect-eq  !>(`(unit frac)`[~ [--3 1]])  !>((to-q:al (mul:al sq3 sq3)))
    %+  expect-eq  !>(`(unit frac)`[~ [--0 1]])  !>((to-q:al (sub:al sq2 sq2)))
    %+  expect-eq  !>(`(unit frac)`[~ [--1 1]])  !>((to-q:al (div:al sq2 sq2)))
    ::  a + (-a) = 0, exactly, and structurally equal to zero
    %+  expect-eq  !>(`anum:al`zero:al)  !>((add:al sq2 (neg:al sq2)))
    %-  expect  !>((is-zero:al (add:al sq2 (neg:al sq2))))
    ::  a * a^-1 = 1
    %+  expect-eq  !>(`anum:al`one:al)  !>((mul:al sq2 (inv:al sq2)))
    %+  expect-eq  !>(`anum:al`one:al)  !>((mul:al phi (inv:al phi)))
    ::  phi^2 = phi + 1, the defining identity of the golden ratio
    %+  expect-eq  !>((add:al phi one:al))  !>((mul:al phi phi))
    ::  multiplying by zero collapses without touching a resultant
    %+  expect-eq  !>(`anum:al`zero:al)  !>((mul:al sq2 zero:al))
    %+  expect-eq  !>(`anum:al`zero:al)  !>((mul:al zero:al sq2))
  ==
++  test-a2-pow
  ;:  weld
    %+  expect-eq  !>(`anum:al`one:al)  !>((pow:al sq2 --0))
    %+  expect-eq  !>(`anum:al`sq2)     !>((pow:al sq2 --1))
    %+  expect-eq  !>((mul:al sq2 sq2))  !>((pow:al sq2 --2))
    %+  expect-eq  !>(`(unit frac)`[~ [--2 1]])  !>((to-q:al (pow:al sq2 --2)))
    %+  expect-eq  !>(`(unit frac)`[~ [--4 1]])  !>((to-q:al (pow:al sq2 --4)))
    ::  a negative exponent inverts
    %+  expect-eq  !>((inv:al sq2))  !>((pow:al sq2 -1))
    %+  expect-eq  !>(`(unit frac)`[~ [--1 2]])  !>((to-q:al (pow:al sq2 -2)))
    ::  cube root cubed is 2
    %+  expect-eq  !>(`(unit frac)`[~ [--2 1]])  !>((to-q:al (pow:al cb2 --3)))
    (expect-fail |.((pow:al zero:al -1)))
  ==
++  test-a3-root
  ;:  weld
    ::  the square root of 2 is sqrt 2, found by substitution and picked
    ::  by raising each candidate back to the k
    %+  expect-eq  !>(`(unit anum:al)`[~ sq2])
    !>((root:al (of-q:al [--2 1]) 2))
    %+  expect-eq  !>(`(unit anum:al)`[~ cb2])
    !>((root:al (of-q:al [--2 1]) 3))
    ::  exact roots come back rational
    %+  expect-eq  !>(`(unit anum:al)`[~ (of-q:al [--2 1])])
    !>((root:al (of-q:al [--8 1]) 3))
    %+  expect-eq  !>(`(unit anum:al)`[~ (of-q:al [--3 1])])
    !>((root:al (of-q:al [--9 1]) 2))
    ::  an odd root of a negative number exists; an even one does not
    %+  expect-eq  !>(`(unit anum:al)`[~ (of-q:al [-2 1])])
    !>((root:al (of-q:al [-8 1]) 3))
    %+  expect-eq  !>(`(unit anum:al)`~)  !>((root:al (of-q:al [-2 1]) 2))
    ::  for even k the NON-NEGATIVE root is taken, though both square to a
    %-  expect  !>(=(%gt (sign:al (need (root:al (of-q:al [--2 1]) 2)))))
    ::  zero, and the degenerate k
    %+  expect-eq  !>(`(unit anum:al)`[~ zero:al])  !>((root:al zero:al 5))
    (expect-fail |.((root:al sq2 0)))
  ==
--
