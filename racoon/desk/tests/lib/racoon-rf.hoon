  ::  /tests/lib/racoon-rf
::::  The rational function field -- SPEC Milestone C, phase F
::
::  Naming: ++test-f0-* for the field, ++test-f1-* for decomposition,
::  ++test-f2-* for integration.  Every crash row in SPEC F7 gets a
::  dedicated arm, and every non-crash row a matching one -- F7 is a
::  two-sided contract and both halves are jettable.
::
::  INTEGRATION IS VERIFIED BY DIFFERENTIATING THE ANSWER (SPEC F9.1).
::  An antiderivative is not unique -- the constant, and every log term
::  up to the sign and scale of its argument -- so no other program's
::  output is an oracle.  d/dx of (rat + sum c*log(a)) is
::  rat' + sum c*a'/a, which lands back in $rfun exactly, and equality
::  there is structural.  This needs no oracle at all.
::
/-  *racoon
/+  *test, racoon, rf=racoon-rf
=/  qq  qq:racoon
=/  qx  qx:racoon
|%
+|  %helpers
::    +q:  a rational from an integer
++  q  |=(n=@s ^-(frac [n 1]))
::    +p:  a Q[x] polynomial from integer coefficients, ascending
++  p  |=(cs=(list @s) ^-(qol (canon:qx (turn cs q))))
::    +f:  an rfun from two integer coefficient lists
++  f  |=([n=(list @s) d=(list @s)] ^-(rfun:rf (new:rf (p n) (p d))))
::    +back:  d/dx of an integration result, as an rfun
::
::  The whole verification strategy in five lines: rat' plus, for each
::  logarithmic term, c times a'/a.
++  back
  |=  r=[rat=rfun:rf ls=(list [c=frac a=qol])]
  ^-  rfun:rf
  =/  ls  ls.r
  =/  acc  (deriv:rf rat.r)
  |-  ^-  rfun:rf
  ?~  ls  acc
  =/  t  (mul:rf (of-q:rf c.i.ls) (new:rf (pderiv:rf a.i.ls) a.i.ls))
  $(ls t.ls, acc (add:rf acc t))
::    +integrates:  does +integrate produce an answer that differentiates
::    back to the input?
++  integrates
  |=  g=rfun:rf
  ^-  ?
  =/  r  (integrate:rf g)
  ?~  r  %.n
  =(g (back u.r))
::
+|  %f0-the-field
::    +test-f0-canonical:  the representation has one form per value
::
::  Unreduced and rescaled inputs must land on the same noun, since
::  equality is structural and every arm downstream relies on that.
++  test-f0-canonical
  ;:  weld
    ::  (x+1)/(x^2+3x+2) reduces to 1/(x+2)
    (expect-eq !>((f ~[--1] ~[--2 --1])) !>((f ~[--1 --1] ~[--2 --3 --1])))
    ::  a non-monic denominator is rescaled, not merely accepted
    (expect-eq !>((f ~[--1] ~[--2 --1])) !>((f ~[--3] ~[--6 --3])))
    ::  every representation of zero is 0/1
    (expect-eq !>(zero:rf) !>((f ~ ~[--5 --1])))
    (expect-eq !>(zero:rf) !>((f ~[--0] ~[--7])))
    ::  and a constant is a constant
    (expect-eq !>(one:rf) !>((f ~[--4] ~[--4])))
  ==
::    +test-f0-arithmetic:  the field laws, on values with known answers
++  test-f0-arithmetic
  =/  a  (f ~[--1] ~[-1 --1])              ::  1/(x-1)
  =/  b  (f ~[--1] ~[--1 --1])             ::  1/(x+1)
  ;:  weld
    ::  1/(x-1) + 1/(x+1) = 2x/(x^2-1)
    (expect-eq !>((f ~[--0 --2] ~[-1 --0 --1])) !>((add:rf a b)))
    ::  1/(x-1) - 1/(x+1) = 2/(x^2-1)
    (expect-eq !>((f ~[--2] ~[-1 --0 --1])) !>((sub:rf a b)))
    ::  1/(x-1) * 1/(x+1) = 1/(x^2-1)
    (expect-eq !>((f ~[--1] ~[-1 --0 --1])) !>((mul:rf a b)))
    ::  the quotient is (x+1)/(x-1)
    (expect-eq !>((f ~[--1 --1] ~[-1 --1])) !>((div:rf a b)))
    ::  inverse and negation
    (expect-eq !>((f ~[-1 --1] ~[--1])) !>((inv:rf a)))
    (expect-eq !>(a) !>((inv:rf (inv:rf a))))
    (expect-eq !>(zero:rf) !>((add:rf a (neg:rf a))))
    (expect-eq !>(one:rf) !>((mul:rf a (inv:rf a))))
    ::  powers, including negative ones through +inv
    (expect-eq !>((mul:rf a a)) !>((pow:rf a --2)))
    (expect-eq !>(one:rf) !>((pow:rf a --0)))
    (expect-eq !>((inv:rf a)) !>((pow:rf a -1)))
  ==
::    +test-f0-deriv:  the quotient rule, and the reduction it needs
::
::  (u/v)' comes out over v^2, which is NOT in lowest terms when v has a
::  repeated factor.  1/(x-1)^2 is the case that catches a +deriv which
::  forgot to reduce: the answer is -2/(x-1)^3 and not -2(x-1)/(x-1)^4.
++  test-f0-deriv
  ;:  weld
    ::  d/dx 1/x = -1/x^2
    (expect-eq !>((f ~[-1] ~[--0 --0 --1])) !>((deriv:rf (f ~[--1] ~[--0 --1]))))
    ::  d/dx 1/(x-1)^2 = -2/(x-1)^3
    %+  expect-eq
      !>((f ~[-2] ~[-1 --3 -3 --1]))
    !>((deriv:rf (f ~[--1] ~[--1 -2 --1])))
    ::  the product rule holds on a pair with nothing in common
    =/  a  (f ~[--1] ~[-1 --1])
    =/  b  (f ~[--0 --1] ~[--2 --1])
    %+  expect-eq
      !>((deriv:rf (mul:rf a b)))
    !>((add:rf (mul:rf (deriv:rf a) b) (mul:rf a (deriv:rf b))))
    ::  and a constant differentiates to zero
    (expect-eq !>(zero:rf) !>((deriv:rf (of-q:rf [--7 3]))))
  ==
::    +test-f0-eval:  values away from poles
++  test-f0-eval
  =/  a  (f ~[--1] ~[-1 --0 --1])          ::  1/(x^2-1)
  ;:  weld
    (expect-eq !>(`frac`[--1 8]) !>((eval:rf a (q --3))))
    (expect-eq !>(`frac`[-1 1]) !>((eval:rf a (q --0))))
    ::  evaluation commutes with the field operations off the poles
    =/  b  (f ~[--0 --1] ~[--2 --1])
    %+  expect-eq
      !>((eval:rf (add:rf a b) (q --3)))
    !>((add:qq (eval:rf a (q --3)) (eval:rf b (q --3))))
  ==
::    +test-f0-deg:  the degree is a difference and may be negative
++  test-f0-deg
  ;:  weld
    (expect-eq !>(`@s`-2) !>((deg:rf (f ~[--1] ~[-1 --0 --1]))))
    (expect-eq !>(`@s`--1) !>((deg:rf (f ~[--0 --0 --1] ~[--0 --1]))))
    (expect-eq !>(`@s`--0) !>((deg:rf one:rf)))
  ==
::    +test-f0-crash:  SPEC F7, the crashing rows
++  test-f0-crash
  ;:  weld
    ::  a zero denominator has no value
    (expect-fail |.((new:rf (p ~[--1]) ~)))
    (expect-fail |.((new:rf (p ~[--1]) (p ~[--0]))))
    ::  inverse and division by zero
    (expect-fail |.((inv:rf zero:rf)))
    (expect-fail |.((div:rf one:rf zero:rf)))
    ::  a negative power of zero
    (expect-fail |.((pow:rf zero:rf -1)))
    ::  the zero function has no degree
    (expect-fail |.((deg:rf zero:rf)))
    ::  and evaluation at a pole
    (expect-fail |.((eval:rf (f ~[--1] ~[-1 --1]) (q --1))))
  ==
::    +test-f0-nocrash:  the other half of the same contract
++  test-f0-nocrash
  ;:  weld
    (expect-success |.((new:rf ~ (p ~[--1]))))
    (expect-success |.((pow:rf zero:rf --3)))
    (expect-success |.((deg:rf one:rf)))
    ::  a pole elsewhere is not a pole here
    (expect-success |.((eval:rf (f ~[--1] ~[-1 --1]) (q --2))))
  ==
::
+|  %f1-decomposition
::    +test-f1-values:  decompositions with known answers
++  test-f1-values
  ;:  weld
    ::  1/(x^2-1) = (1/2)/(x-1) - (1/2)/(x+1)
    %+  expect-eq
      !>  ^-  [qol (list [qol qol @ud])]
      :-  ~
      :~  [~[[--1 2]] (p ~[-1 --1]) 1]
          [~[[-1 2]] (p ~[--1 --1]) 1]
      ==
    !>((pfrac-full:rf (f ~[--1] ~[-1 --0 --1])))
    ::  a repeated factor produces both powers
    %+  expect-eq
      !>  ^-  [qol (list [qol qol @ud])]
      [~ ~[[(p ~[--1]) (p ~[-1 --1]) 2]]]
    !>((pfrac-full:rf (f ~[--1] ~[--1 -2 --1])))
  ==
::    +test-f1-recombines:  every decomposition sums back to its input
::
::  The property that makes the arm worth having, over a corpus wide
::  enough to hit proper and improper fractions, repeated factors,
::  irreducible quadratics, and a denominator that is already 1.
++  test-f1-recombines
  =/  cs=(list rfun:rf)
    :~  (f ~[--1] ~[-1 --0 --1])
        (f ~[--1] ~[--1 -2 --1])
        (f ~[--0 --0 --0 --1] ~[-1 --0 --1])
        (f ~[--5 --3] ~[-4 --0 --1])
        (f ~[--1] ~[--0 -1 --0 --1])
        (f ~[--1] ~[--1 --0 --1])
        (f ~[--2 --1] ~[--1])
        (f ~[--1] ~[--1 --0 --0 --0 --1])
        (f ~[--7 --0 --2] ~[--0 --0 --1])
        (f ~[--1 --1 --1] ~[--6 --11 --6 --1])
    ==
  =|  out=tang
  |-  ^-  tang
  ?~  cs  out
  %=  $
    cs  t.cs
    out
      %+  weld  out
      ;:  weld
        (expect-eq !>(i.cs) !>((recombine:rf (pfrac:rf i.cs))))
        (expect-eq !>(i.cs) !>((recombine:rf (pfrac-full:rf i.cs))))
      ==
  ==
::    +test-f1-squarefree-vs-full:  the two bases differ where they should
::
::  On a denominator that is already irreducible the two agree; on one
::  that factors, the full decomposition has strictly more terms.  A
::  +pfrac-full that quietly returned the squarefree answer would pass
::  every recombination test, and this is what catches it.
++  test-f1-squarefree-vs-full
  =/  g  (f ~[--1] ~[-1 --0 --1])          ::  1/(x^2-1), splits
  =/  h  (f ~[--1] ~[--1 --0 --1])         ::  1/(x^2+1), does not
  ;:  weld
    (expect-eq !>(1) !>((lent ts:(pfrac:rf g))))
    (expect-eq !>(2) !>((lent ts:(pfrac-full:rf g))))
    (expect-eq !>((pfrac:rf h)) !>((pfrac-full:rf h)))
  ==
::    +test-f1-poles:  the factorization, made visible
++  test-f1-poles
  ;:  weld
    %+  expect-eq
      !>  ^-  (list [qol @ud])
      ~[[(p ~[-1 --1]) 1] [(p ~[--1 --1]) 1]]
    !>((poles:rf (f ~[--1] ~[-1 --0 --1])))
    ::  multiplicity is reported, not flattened
    %+  expect-eq
      !>  ^-  (list [qol @ud])
      ~[[(p ~[-1 --1]) 2]]
    !>((poles:rf (f ~[--1] ~[--1 -2 --1])))
    ::  a constant denominator has no poles
    (expect-eq !>(*(list [qol @ud])) !>((poles:rf (of-q:rf (q --3)))))
  ==
::
+|  %f2-integration
::    +test-f2-differentiates-back:  SPEC F9.1, the load-bearing check
++  test-f2-differentiates-back
  =/  cs=(list rfun:rf)
    :~  (f ~[--1] ~[-1 --0 --1])           ::  1/(x^2-1)
        (f ~[--0 --2] ~[--1 --0 --1])      ::  2x/(x^2+1), rational residue
        (f ~[--1] ~[--0 --0 --1])          ::  1/x^2, no logs
        (f ~[--1] ~[--1 -2 --1])           ::  1/(x-1)^2
        (f ~[--0 --0 --0 --1] ~[-1 --0 --1])  ::  improper
        (f ~[--5 --3] ~[-4 --0 --1])
        (f ~[--1] ~[--0 -1 --0 --1])       ::  1/(x^3-x), three logs
        (f ~[--1] ~[--0 --1])              ::  1/x
        (f ~[--2 --1] ~[--1])              ::  a polynomial
        (f ~[--1] ~[--1 -4 --6 -4 --1])    ::  1/(x-1)^4
    ==
  =|  out=tang
  |-  ^-  tang
  ?~  cs  out
  $(cs t.cs, out (weld out (expect !>((integrates i.cs)))))
::    +test-f2-values:  answers a reader can check by eye
++  test-f2-values
  ::  bound BEFORE the ;:, not inside it: `=/ a b  c` scopes over the
  ::  one expression that follows, so a binding written between two
  ::  arguments of a ;: reaches the first of them and not the second
  =/  r  (need (integrate:rf (f ~[--1] ~[--0 --0 --1])))
  =/  s  (need (integrate:rf (f ~[--0 --2] ~[--1 --0 --1])))
  =/  u  (need (integrate:rf (f ~[--1] ~[-1 --0 --1])))
  ;:  weld
    ::  int 1/x^2 = -1/x, and no logarithm
    (expect-eq !>((f ~[-1] ~[--0 --1])) !>(rat.r))
    (expect-eq !>(0) !>((lent ls.r)))
    ::  int 2x/(x^2+1) = log(x^2+1): ONE term, coefficient 1, and the
    ::  argument is the irreducible quadratic rather than two linears
    (expect-eq !>(1) !>((lent ls.s)))
    (expect-eq !>(`frac`[--1 1]) !>(c:(snag 0 ls.s)))
    (expect-eq !>((p ~[--1 --0 --1])) !>(a:(snag 0 ls.s)))
    (expect-eq !>(zero:rf) !>(rat.s))
    ::  int 1/(x^2-1) = (1/2)log(x-1) - (1/2)log(x+1)
    (expect-eq !>(2) !>((lent ls.u)))
    (expect-eq !>(`frac`[--1 2]) !>(c:(snag 0 ls.u)))
    (expect-eq !>(`frac`[-1 2]) !>(c:(snag 1 ls.u)))
  ==
::    +test-f2-hermite:  the rational part is separated correctly
::
::  +hermite's contract is that what it leaves behind has a SQUAREFREE
::  denominator -- that is what makes the remainder purely logarithmic.
::  Asserting the contract directly, rather than only through
::  +integrate, is what would catch a reduction that stopped one power
::  early and still summed to the right answer.
++  test-f2-hermite
  =/  cs=(list rfun:rf)
    :~  (f ~[--1] ~[--1 -2 --1])
        (f ~[--1] ~[--1 -4 --6 -4 --1])
        (f ~[--1] ~[--0 --0 --1])
        (f ~[--1 --1] ~[--0 --0 --0 --1])
        (f ~[--0 --0 --0 --1] ~[-1 --0 --1])
    ==
  =|  out=tang
  |-  ^-  tang
  ?~  cs  out
  =/  h  (hermite:rf i.cs)
  %=  $
    cs  t.cs
    out
      %+  weld  out
      ;:  weld
        ::  the remainder's denominator is squarefree: gcd(d, d') = 1
        %-  expect
        !>
        =/  d  den.log.h
        ?:  =(0 (deg:qx d))  %.y
        =(1 (lent (sqf-den:rf d)))
        ::  and rat' + log is the original, which is what "reduction"
        ::  means -- nothing was dropped on the way
        %+  expect-eq
          !>(i.cs)
        !>((add:rf (deriv:rf rat.h) log.h))
      ==
  ==
::    +test-f2-out-of-range:  SPEC F6, and it is a value not a crash
::
::  The arctangent is the case the whole restriction is about: the
::  residues of 1/(x^2+1) are -i/2 and +i/2, so there is no rational c,
::  and the answer is ~ rather than a wrong one.  A +integrate that
::  returned SOMETHING here would be the worst failure available, since
::  it would differentiate back to the wrong function.
++  test-f2-out-of-range
  ;:  weld
    (expect-eq !>(~) !>((integrate:rf (f ~[--1] ~[--1 --0 --1]))))
    ::  1/(x^2-2): residues are +-1/(2 sqrt 2), real but irrational, and
    ::  §F6 says that is out of range too -- naming them is not the
    ::  problem, arithmetic in Q(sqrt 2)[x] is
    (expect-eq !>(~) !>((integrate:rf (f ~[--1] ~[-2 --0 --1]))))
    ::  but the rational-residue quadratic IS in range
    (expect-success |.((need (integrate:rf (f ~[--0 --2] ~[--1 --0 --1])))))
  ==
--
