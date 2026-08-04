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
--
