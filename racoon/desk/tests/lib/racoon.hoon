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
+|  %p1-crashes
::  S8: +deg and +lc crash on the zero polynomial.
++  test-p1-crash-zx-deg-zero
  (expect-fail |.((deg:zx ~)))
++  test-p1-crash-zx-lc-zero
  (expect-fail |.((lc:zx ~)))
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
--
