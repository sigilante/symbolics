  ::  /tests/lib/racoon-lt
::::  The Laplace transform -- SPEC Milestone C, phase F3
::
::  THE ROUND TRIP IS THE TEST (SPEC F9.3).  +laplace was built first
::  because it is the k-th s-derivative of a base transform, which is
::  +deriv:rf applied k times -- an arm phase F0 already verified.
::  Then inverse(laplace(e)) = e and laplace(inverse(f)) = f check
::  +inverse against it, and two errors would have to agree exactly to
::  survive both directions.  No oracle is involved.
::
::  ONE LITERAL WAS WRONG the first time these were written: s^2 - 1
::  where s^2 + 1 was meant, which made "y'' + y = 0" return sinh.  The
::  library was right and the test was not, which is the usual way
::  round.  The characteristic polynomials below are spelled out in the
::  comments for that reason.
::
/-  *racoon
/+  *test, racoon, rf=racoon-rf, lt=racoon-lt
=/  qq  qq:racoon
=/  qx  qx:racoon
|%
+|  %helpers
::    +q:  a rational from an integer
++  q  |=(n=@s ^-(frac [n 1]))
::    +p:  a Q[x] polynomial from integer coefficients, ascending
++  p  |=(cs=(list @s) ^-(qol (canon:qx (turn cs q))))
::    +e:  one exponential-polynomial term, from integers
++  e
  |=  [c=@s k=@ud sig=@s wsq=@s tr=?(%cos %sin)]
  ^-  eterm:lt
  [(q c) k (q sig) (q wsq) tr]
::    +trips:  does e survive inverse(laplace(e))?
::
::  Compared against +canon of the input, not the input: the claim is
::  that the round trip is the identity on CANONICAL $expo, and a
::  literal written below in a non-canonical order is a fact about the
::  literal.  One of them was -- e^t before e^-t, where the pinned order
::  is ascending in sig -- and this is what that cost.
++  trips
  |=  x=expo:lt
  ^-  ?
  =/  b  (inverse:lt (laplace:lt x))
  ?~  b  %.n
  =((canon:lt x) u.b)
::
+|  %f3-transform
::    +test-f3-round-trip:  inverse . laplace is the identity
::
::  Every term here has k = 0, because a t^k factor transforms to a
::  REPEATED pole and +inverse does not do those yet -- see
::  ++test-f3-repeated-is-out-of-range, which asserts exactly that.
++  test-f3-round-trip
  =/  cs=(list expo:lt)
    :~  ~[(e --3 0 --2 --0 %cos)]                 ::  3e^2t
        ~[(e --1 0 --0 --1 %cos)]                 ::  cos t
        ~[(e --1 0 --0 --1 %sin)]                 ::  sin t
        ~[(e --1 0 --0 --4 %cos)]                 ::  cos 2t
        ~[(e --1 0 --1 --4 %cos)]                 ::  e^t cos 2t
        ~[(e --1 0 --1 --4 %sin)]                 ::  e^t sin(2t)/2
        ~[(e --1 0 -1 --0 %cos) (e --2 0 --3 --0 %cos)]
        ~[(e --1 0 --0 --0 %cos)]                 ::  the constant 1
        ~[(e --5 0 -2 --9 %sin) (e --1 0 --4 --0 %cos)]
        ~[(e --1 0 --1 --0 %cos) (e -1 0 -1 --0 %cos)]
    ==
  =|  out=tang
  |-  ^-  tang
  ?~  cs  out
  $(cs t.cs, out (weld out (expect !>((trips i.cs)))))
::    +test-f3-values:  transforms a reader can check by eye
++  test-f3-values
  ;:  weld
    ::  L{3e^2t} = 3/(s-2)
    %+  expect-eq
      !>((new:rf (p ~[--3]) (p ~[-2 --1])))
    !>((laplace:lt ~[(e --3 0 --2 --0 %cos)]))
    ::  L{cos t} = s/(s^2+1)
    %+  expect-eq
      !>((new:rf (p ~[--0 --1]) (p ~[--1 --0 --1])))
    !>((laplace:lt ~[(e --1 0 --0 --1 %cos)]))
    ::  L{sin t} = 1/(s^2+1) -- the normalized basis is why this is 1
    ::  and not omega, which is what keeps every coefficient rational
    %+  expect-eq
      !>((new:rf (p ~[--1]) (p ~[--1 --0 --1])))
    !>((laplace:lt ~[(e --1 0 --0 --1 %sin)]))
    ::  L{t e^2t} = 1/(s-2)^2, which is the k = 1 ladder working
    %+  expect-eq
      !>((new:rf (p ~[--1]) (p ~[--4 -4 --1])))
    !>((laplace:lt ~[(e --1 1 --2 --0 %cos)]))
    ::  and the zero function transforms to zero
    (expect-eq !>(zero:rf) !>((laplace:lt ~)))
  ==
::    +test-f3-canon:  $expo is canonical, so equality is structural
++  test-f3-canon
  ;:  weld
    ::  like terms combine
    %+  expect-eq
      !>(`expo:lt`~[(e --5 0 --2 --0 %cos)])
    !>((canon:lt ~[(e --2 0 --2 --0 %cos) (e --3 0 --2 --0 %cos)]))
    ::  and cancel to nothing
    %+  expect-eq
      !>(`expo:lt`~)
    !>((canon:lt ~[(e --2 0 --2 --0 %cos) (e -2 0 --2 --0 %cos)]))
    ::  a zero coefficient is not a term
    (expect-eq !>(`expo:lt`~) !>((canon:lt ~[(e --0 0 --1 --1 %sin)])))
    ::  order does not survive as information
    %+  expect-eq
      !>((canon:lt ~[(e --1 0 --1 --0 %cos) (e --2 0 --3 --0 %cos)]))
    !>((canon:lt ~[(e --2 0 --3 --0 %cos) (e --1 0 --1 --0 %cos)]))
  ==
::    +test-f3-deriv:  the class is closed under d/dt
::
::  Checked twice over: against known derivatives, and against the
::  transform law L{f'} = s*L{f} - f(0), which ties +ederiv to +laplace
::  rather than letting either be wrong alone.
++  test-f3-deriv
  ::  cos t, and the right-hand side of L{f'} = s L{f} - f(0) for it
  =/  cs=expo:lt  ~[(e --1 0 --0 --1 %cos)]
  =/  law=rfun:rf
    %+  sub:rf
      (mul:rf (of-p:rf (p ~[--0 --1])) (laplace:lt cs))
    one:rf
  ;:  weld
    ::  d/dt sin t = cos t
    %+  expect-eq
      !>(`expo:lt`~[(e --1 0 --0 --1 %cos)])
    !>((ederiv:lt ~[(e --1 0 --0 --1 %sin)]))
    ::  d/dt cos t = -sin t, which in this basis is -wsq times the
    ::  normalized sine, and wsq is 1 here
    %+  expect-eq
      !>(`expo:lt`~[(e -1 0 --0 --1 %sin)])
    !>((ederiv:lt ~[(e --1 0 --0 --1 %cos)]))
    ::  d/dt e^2t = 2e^2t
    %+  expect-eq
      !>(`expo:lt`~[(e --2 0 --2 --0 %cos)])
    !>((ederiv:lt ~[(e --1 0 --2 --0 %cos)]))
    ::  d/dt t = 1
    %+  expect-eq
      !>(`expo:lt`~[(e --1 0 --0 --0 %cos)])
    !>((ederiv:lt ~[(e --1 1 --0 --0 %cos)]))
    ::  L{f'} = s L{f} - f(0), on cos t: f(0) = 1
    (expect-eq !>((laplace:lt (ederiv:lt cs))) !>(law))
  ==
::    +test-f3-ode:  constant-coefficient initial value problems
::
::  The characteristic polynomials are written out because getting one
::  wrong is silent: s^2 - 1 in place of s^2 + 1 turns "y'' + y = 0"
::  into a hyperbolic problem with a perfectly plausible answer.
++  test-f3-ode
  ;:  weld
    ::  y'' + y = 0, y(0) = 0, y'(0) = 1  ->  sin t.   p = s^2 + 1
    %+  expect-eq
      !>(`(unit expo:lt)`[~ ~[(e --1 0 --0 --1 %sin)]])
    !>((solve-ode:lt (p ~[--1 --0 --1]) ~[(q --0) (q --1)]))
    ::  y'' + 4y = 0, y(0) = 1, y'(0) = 0  ->  cos 2t.  p = s^2 + 4
    %+  expect-eq
      !>(`(unit expo:lt)`[~ ~[(e --1 0 --0 --4 %cos)]])
    !>((solve-ode:lt (p ~[--4 --0 --1]) ~[(q --1) (q --0)]))
    ::  y' - 3y = 0, y(0) = 2  ->  2e^3t.              p = s - 3
    %+  expect-eq
      !>(`(unit expo:lt)`[~ ~[(e --2 0 --3 --0 %cos)]])
    !>((solve-ode:lt (p ~[-3 --1]) ~[(q --2)]))
    ::  y'' - y = 0, y(0) = 1, y'(0) = 0  ->  cosh t.  p = s^2 - 1
    %+  expect-eq
      !>  ^-  (unit expo:lt)
      :-  ~
      :~  [[--1 2] 0 (q -1) (q --0) %cos]
          [[--1 2] 0 (q --1) (q --0) %cos]
      ==
    !>((solve-ode:lt (p ~[-1 --0 --1]) ~[(q --1) (q --0)]))
  ==
::    +test-f3-out-of-range:  SPEC F6, as a value and not a crash
++  test-f3-out-of-range
  ;:  weld
    ::  a repeated pole: L{t e^2t} is 1/(s-2)^2, and the expansion of a
    ::  repeated factor is the unbuilt half of F3
    (expect-eq !>(~) !>((inverse:lt (new:rf (p ~[--1]) (p ~[--4 -4 --1])))))
    ::  an irreducible quadratic with wsq < 0: s^2 - 2 has real but
    ::  IRRATIONAL roots, so the exponents are not rational and $eterm
    ::  cannot hold them
    (expect-eq !>(~) !>((inverse:lt (new:rf (p ~[--1]) (p ~[-2 --0 --1])))))
    ::  a cubic irreducible factor: s^3 - 2
    (expect-eq !>(~) !>((inverse:lt (new:rf (p ~[--1]) (p ~[-2 --0 --0 --1])))))
    ::  an improper fraction is not the transform of anything in this
    ::  class -- it would be a delta
    (expect-eq !>(~) !>((inverse:lt (of-p:rf (p ~[--1 --1])))))
    ::  but zero inverts to the empty sum rather than failing
    (expect-eq !>(`(unit expo:lt)`[~ ~]) !>((inverse:lt zero:rf)))
  ==
::    +test-f3-crash:  SPEC F7's crashing row
++  test-f3-crash
  ;:  weld
    ::  the wrong number of initial conditions is a CALLER error, not an
    ::  input out of range, so it crashes rather than producing ~
    (expect-fail |.((solve-ode:lt (p ~[--1 --0 --1]) ~[(q --0)])))
    (expect-fail |.((solve-ode:lt (p ~[--1 --0 --1]) ~[(q --0) (q --1) (q --2)])))
    (expect-success |.((solve-ode:lt (p ~[--1 --0 --1]) ~[(q --0) (q --1)])))
  ==
--
