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
