  ::  /lib/racoon-alg
::::  Real algebraic number arithmetic -- SPEC Milestone C, phase A
::
::  Phase R isolates real roots; it does not add or multiply them.  This
::  does.  sqrt 2 + sqrt 3 is a value here, not a polynomial someone had
::  to know to write down.
::
::  A CONSUMER of /lib/racoon and /lib/racoon-roots.  Sixth application of
::  that rule; %zx and %qx stay frozen and gain nothing.
::
::  REPRESENTATION IS CANONICAL: the minimal polynomial (primitive,
::  positive leading coefficient, irreducible over Z) together with the
::  canonical isolating interval of that root.  Both halves are unique, so
::
::    - EQUALITY IS STRUCTURAL.  =(a b) decides it.  No refinement loop,
::      no tolerance, no separate +equals.
::    - every arm is `free`, and a jet may use any algorithm at all.
::
::  The price is that every operation reduces to the minimal polynomial,
::  which means factoring.  Paid deliberately: carrying any polynomial
::  that happens to vanish at alpha would make equality undecidable
::  without a gcd per comparison, and make nothing canonical.
::
::  NO FLOATING POINT.  Every endpoint is an exact $frac forever, and
::  +approx produces a rational within 2^-k rather than a float.
::
::  COST: deg(a*b) <= deg a * deg b, so two degree-4 numbers give a
::  degree-16 resultant, and the minimal polynomial is an irreducible
::  factor of it.  SPEC A8 called that the wall, on the strength of §9's
::  claim that SD_4 was out of scope; §V0 measured §9's claim and it was
::  wrong, and the numbers below say A8's inherited it.  MEASURED with
::  /gen/racoon-alg-bench, largest real root of each argument, timing
::  the sum, before and after the swap described next:
::
::                                       degrees   factor:zx  van hoeij
::    (sqrt2+sqrt3) + (sqrt5+sqrt7)       4 + 4      3.34 s     3.34 s
::    (sqrt2+..+sqrt7) + sqrt11          16 + 2    281.9 s     90.4 s
::
::  The sums are SD_4 and SD_5.  At degree 16 the factorization is 0.3 s
::  of the 3.34 s and the BIVARIATE RESULTANT is the cost -- 17
::  univariate resultants and an interpolation, none of which van Hoeij
::  touches.  At degree 32 it inverts: 202.5 s of the 281.9 s was
::  Zassenhaus, and van Hoeij does that part in 9.4 s.
::
::  So the factorization goes through /lib/vanhoeij, which SPEC A8 asked
::  for in advance -- "one call, so a better algorithm replaces it" --
::  and +facz is that call.  The price is that this library, alone among
::  Racoon's consumers, needs Baloon on the desk; see SPEC-QUESTIONS R4.
::
/-  *racoon
/+  racoon, rr=racoon-roots, vh=vanhoeij
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  qx  qx:racoon
|%
+|  %types
::    $anum:  a real algebraic number
::
::  .m minimal: primitive, lc > 0, irreducible over Z.  .iv the canonical
::  isolating interval of this root of m, as +isolate:rr produces it.
::  A degenerate .iv means the number is rational and .m is linear.
+$  anum  [m=zol iv=ivl:rr]
::
+|  %private
::    +qneg:  negate a rational
++  qneg  |=(x=frac ^-(frac (neg:qq x)))
::    +qmin:  the lesser of two rationals
++  qmin  |=([a=frac b=frac] ^-(frac ?:(=(%gt (cmp:qq a b)) b a)))
::    +qmax:  the greater of two rationals
++  qmax  |=([a=frac b=frac] ^-(frac ?:(=(%lt (cmp:qq a b)) b a)))
::    +qmid:  the midpoint of two rationals
++  qmid  |=([a=frac b=frac] ^-(frac (mul:qq (add:qq a b) [--1 2])))
::    +qwid:  the width of an interval
++  qwid  |=(iv=ivl:rr ^-(frac (sub:qq hi.iv lo.iv)))
::    +thin:  is this interval a single exact point?
++  thin  |=(iv=ivl:rr ^-(? =(%eq (cmp:qq lo.iv hi.iv))))
::    +nrm:  primitive, with positive leading coefficient
++  nrm
  |=  p=zol
  ^-  zol
  ?~  p  !!
  =/  f=zol  (pp:zx p)
  ?:  (syn:si (lc:zx f))  f  (neg:zx f)
::    +sub-neg:  p(-x), by negating the odd-index coefficients
++  sub-neg
  |=  p=zol
  ^-  zol
  =/  cs=zol  p
  =/  k=@ud   0
  =|  out=zol
  |-  ^-  zol
  ?~  cs  (flop out)
  =/  c=@s  ?:(=(0 (mod k 2)) i.cs (dif:si --0 i.cs))
  $(cs t.cs, k +(k), out [c out])
::    +sub-pow:  p(x^k), by spreading each coefficient k apart
++  sub-pow
  |=  [p=zol k=@ud]
  ^-  zol
  ?<  =(0 k)
  =/  cs=zol  p
  =|  out=zol
  |-  ^-  zol
  ?~  cs  (canon:zx (flop out))
  ::  the first coefficient goes in directly; each later one is preceded
  ::  by k-1 zeros
  =/  gap=zol  ?~(out ~ (reap (dec k) --0))
  $(cs t.cs, out [i.cs (weld gap out)])
::    +rat-here:  the rational root of p lying in this interval, if any
::
::  At most one can: the caller has established that iv isolates a single
::  root of p.
++  rat-here
  |=  [p=zol iv=ivl:rr]
  ^-  (unit frac)
  =/  rs  (rational-roots:rr p)
  |-  ^-  (unit frac)
  ?~  rs  ~
  =/  r=frac  r.i.rs
  ?:  (thin iv)
    ?:(=(%eq (cmp:qq r lo.iv)) `r $(rs t.rs))
  ?:  ?&(=(%lt (cmp:qq lo.iv r)) ?!(=(%gt (cmp:qq r hi.iv))))
    `r
  $(rs t.rs)
::    +holds:  does the overlap of two intervals contain a root of f?
::
::  Both intervals are assumed to hold a root of the irreducible f, whose
::  degree is at least 2 -- so the root is irrational, sits strictly
::  inside each, and the overlap has positive width whenever they share
::  it.  An empty or degenerate overlap therefore means "different root".
++  holds
  |=  [f=zol a=ivl:rr b=ivl:rr]
  ^-  ?
  =/  lo=frac  (qmax lo.a lo.b)
  =/  hi=frac  (qmin hi.a hi.b)
  ?:  =(%gt (cmp:qq lo hi))  %.n
  =(1 (count:rr f lo hi))
::    +canon-iv:  the canonical isolating interval of f's root inside iv
::
::  f must be irreducible of degree at least 2, so every one of its
::  canonical intervals is non-degenerate and the overlap test decides.
++  canon-iv
  |=  [f=zol iv=ivl:rr]
  ^-  ivl:rr
  =/  cs  (isolate:rr f)
  |-  ^-  ivl:rr
  ?~  cs  !!
  ?:  (holds f iv i.cs)  i.cs
  $(cs t.cs)
::    +mk-irr:  build from a polynomial already known irreducible
++  mk-irr
  |=  [f=zol iv=ivl:rr]
  ^-  anum
  ?:  =(1 (deg:zx f))  (of-q (rat-of f))
  [f (canon-iv f iv)]
::    +rat-of:  the root of a linear polynomial
++  rat-of
  |=  f=zol
  ^-  frac
  ?~  f  !!
  =/  c1=@s  (lc:zx f)
  ::  c1*x + c0 = 0, so the root is -c0/c1 with c1 made positive
  ?:  (syn:si c1)
    (new:qq (dif:si --0 i.f) (abs:si c1))
  (new:qq i.f (abs:si c1))
::
+|  %public
::    +of-q:  embed a rational
::
::  m is q*x - p, already primitive (gcd(|p|, q) = 1 by the canonical
::  form of $frac) with positive leading coefficient (q > 0).
++  of-q
  |=  r=frac
  ^-  anum
  [~[(dif:si --0 p.r) (sun:si q.r)] [r r]]
::    +zero:  the algebraic number 0
++  zero  ^-(anum (of-q zero:qq))
::    +one:  the algebraic number 1
++  one   ^-(anum (of-q one:qq))
::    +facz:  the irreducible factors of a nonzero polynomial over Z
::
::  [a=zol] -> (list zol).  THE ONE FACTORIZATION CALL (SPEC A8), and
::  what it calls is van Hoeij rather than +factor:zx.
::
::  +factor:zx is Yun's squarefree decomposition followed by +firr:zx on
::  each part; this is the same pipeline with +factor:vh in place of
::  +firr:zx.  Below sixteen modular factors +factor:vh IS +firr:zx --
::  it falls through the +lat-min gate to the identical enumeration --
::  so this is never the slower choice and is 21x faster at r = 16.
::
::  Multiplicities and the content are dropped on purpose.  A minimal
::  polynomial is one irreducible factor; how many times it divides the
::  resultant, and what constant the resultant carried, say nothing
::  about which root is the answer.
::
::  Crashes on ~, as +factor:zx does.  A degree-0 input yields ~, and
::  +make crashes on that -- also as before.
++  facz
  |=  a=zol
  ^-  (list zol)
  ?~  a  !!
  %-  zing
  %+  turn  fs:(sqfree:zx a)
  |=([p=zol m=@ud] (factor:vh p))
::    +make:  canonicalize a polynomial and an isolating interval
::
::  [m=zol iv=ivl] -> anum, where m need not be minimal but iv must
::  isolate exactly one of its real roots.  The only entry point that
::  accepts a non-minimal polynomial.
::
::  A rational root is recognized FIRST, which skips factoring entirely
::  in that case; otherwise the minimal polynomial is the irreducible
::  factor having this root, found by asking which factor has a root in
::  the same place.  That step is where the cost lives (SPEC A8) and is
::  deliberately one call -- +facz.
++  make
  |=  [m=zol iv=ivl:rr]
  ^-  anum
  ?~  m  !!
  =/  hit  (rat-here m iv)
  ?^  hit  (of-q u.hit)
  =/  fs=(list zol)  (facz m)
  |-  ^-  anum
  ?~  fs  !!
  ::  factors are primitive with lc > 0 already (SPEC S9), and a linear
  ::  factor would have been caught by the rational test above.  The
  ::  overlap of iv with itself is iv, so this asks: does this factor
  ::  have exactly one root where the number is?
  ?:  ?&((gth (deg:zx i.fs) 1) (holds i.fs iv iv))
    [i.fs (canon-iv i.fs iv)]
  $(fs t.fs)
::    +to-q:  the rational value, when there is one
++  to-q
  |=  a=anum
  ^-  (unit frac)
  ?.  =(1 (deg:zx m.a))  ~
  `(rat-of m.a)
::    +deg:  the degree of Q(alpha) over Q
++  deg  |=(a=anum ^-(@ud (deg:zx m.a)))
::    +is-rational:  is this number rational?
++  is-rational  |=(a=anum ^-(? =(1 (deg:zx m.a))))
::    +is-zero:  is this number zero?
::
::  Structural, because the form is canonical -- no refinement needed.
++  is-zero  |=(a=anum ^-(? =(a zero)))
::    +approx:  a rational within 2^-k of the value
::
::  Pinned as the midpoint of the first canonical refinement whose width
::  is at most 2^-k, so the product is a function of the input and k
::  alone.  An exact value comes back exactly.
++  approx
  |=  [a=anum k=@ud]
  ^-  frac
  ?:  (thin iv.a)  lo.iv.a
  =/  tgt=frac  (new:qq --1 (^pow 2 k))
  =/  cur=ivl:rr  iv.a
  |-  ^-  frac
  ?:  ?!(=(%gt (cmp:qq (qwid cur) tgt)))  (qmid lo.cur hi.cur)
  $(cur (refine:rr m.a cur 1))
::    +cmp:  compare two algebraic numbers
::
::  STRUCTURAL EQUALITY IS TESTED FIRST.  Without that the refinement
::  loop never terminates on equal inputs, which is the classic way this
::  is written wrong.  Past it the values differ, so their intervals must
::  separate at some finite depth.
++  cmp
  |=  [a=anum b=anum]
  ^-  ord
  ?:  =(a b)  %eq
  =/  x=ivl:rr  iv.a
  =/  y=ivl:rr  iv.b
  |-  ^-  ord
  ?:  =(%lt (cmp:qq hi.x lo.y))  %lt
  ?:  =(%lt (cmp:qq hi.y lo.x))  %gt
  $(x (refine:rr m.a x 1), y (refine:rr m.b y 1))
::    +sign:  the sign, against zero
++  sign  |=(a=anum ^-(ord (cmp a zero)))
::    +neg:  additive inverse
::
::  p(-x) is irreducible whenever p is, so this needs no factoring.  The
::  interval must still be recanonicalized: negation maps (lo, hi] to
::  [-hi, -lo), which is not a node of the subdivision tree.
++  neg
  |=  a=anum
  ^-  anum
  ?:  (is-rational a)  (of-q (qneg (rat-of m.a)))
  (mk-irr (nrm (sub-neg m.a)) [(qneg hi.iv.a) (qneg lo.iv.a)])
::    +inv:  multiplicative inverse
::
::  The coefficient reversal of p is irreducible whenever p is, so this
::  needs no factoring either.  Crashes on zero.
::
::  The interval is refined until it excludes zero before inverting --
::  otherwise 1/x is not monotone across it and the endpoints do not map
::  to endpoints.
++  inv
  |=  a=anum
  ^-  anum
  ?<  (is-zero a)
  ?:  (is-rational a)  (of-q (inv:qq (rat-of m.a)))
  =/  cur=ivl:rr  iv.a
  |-  ^-  anum
  ?:  ?|(=(%gt (cmp:qq lo.cur zero:qq)) =(%lt (cmp:qq hi.cur zero:qq)))
    ::  1/x reverses order on an interval of constant sign, for both signs
    %-  mk-irr
    :-  (nrm (flop m.a))
    [(inv:qq hi.cur) (inv:qq lo.cur)]
  $(cur (refine:rr m.a cur 1))
::
+|  %resultants
::    +shift-neg:  q(t - y), as a polynomial in y
++  shift-neg
  |=  [q=zol t=@s]
  ^-  zol
  =/  lin=zol  ~[t -1]
  =/  cs=zol   (flop q)
  =|  acc=zol
  |-  ^-  zol
  ?~  cs  acc
  $(cs t.cs, acc (add:zx (mul:zx acc lin) (canon:zx ~[i.cs])))
::    +scale-pow:  y^d * q(t/y), as a polynomial in y
::
::  Coefficient b_j of q lands at y^(d-j) scaled by t^j.  Its leading
::  y-coefficient is q(0), which is nonzero for any irreducible q of
::  degree at least 2 -- so the degree never drops and specialization is
::  valid at every t.
++  scale-pow
  |=  [q=zol t=@s]
  ^-  zol
  =/  d=@ud   (deg:zx q)
  =/  cs=zol  (flop q)
  =/  j=@ud   d
  =|  out=zol
  |-  ^-  zol
  ?~  cs  (canon:zx (flop out))
  ::  j is guarded rather than decremented blindly: %= evaluates every
  ::  binding, so (dec 0) on the last pass would crash before ?~ cs fires
  $(cs t.cs, j ?:(=(0 j) 0 (dec j)), out [(pro:si i.cs (pows-s j t)) out])
::    +pows-s:  t^j over the integers
++  pows-s
  |=  [j=@ud t=@s]
  ^-  @s
  =/  k=@ud  j
  =/  acc=@s  --1
  |-  ^-  @s
  ?:  =(0 k)  acc
  $(k (dec k), acc (pro:si acc t))
::    +lagrange:  the polynomial through these points, over Z
::
::  The interpolant of a resultant has integer coefficients, so +clear:qx
::  scales by 1 and merely changes representation.
++  lagrange
  |=  pts=(list [t=@s v=@s])
  ^-  zol
  %-  clear:qx
  =/  rest=(list [t=@s v=@s])  pts
  =|  acc=qol
  |-  ^-  qol
  ?~  rest  acc
  =/  b=qol  (basis pts t.i.rest)
  $(rest t.rest, acc (add:qx acc (scale:qx b (new:qq v.i.rest 1))))
::    +basis:  the Lagrange basis polynomial at ti
++  basis
  |=  [pts=(list [t=@s v=@s]) ti=@s]
  ^-  qol
  =/  rest=(list [t=@s v=@s])  pts
  =/  acc=qol  ~[one:qq]
  |-  ^-  qol
  ?~  rest  acc
  ?:  =(t.i.rest ti)  $(rest t.rest)
  =/  den=frac  (new:qq (dif:si ti t.i.rest) 1)
  =/  lin=qol
    :~  (neg:qq (div:qq (new:qq t.i.rest 1) den))
        (inv:qq den)
    ==
  $(rest t.rest, acc (mul:qx acc lin))
::    +bires:  a bivariate resultant, by evaluation and interpolation
::
::  [p=zol q=zol kind=?(%sum %prod)] -> zol.
::
::  +res:zx is univariate over Z, and Res_y of a polynomial in Z[x][y]
::  cannot be formed symbolically with the frozen arms -- Baloon's
::  polynomial-entry determinants are unreachable, since Baloon depends
::  on Racoon and not the reverse.
::
::  So: Res_y has degree at most deg p * deg q in x, and every evaluation
::  of it at an integer x is an ORDINARY univariate integer resultant.
::  Evaluate at that many points plus one and interpolate.  Only existing
::  frozen arms are needed (SPEC A3).
++  bires
  |=  [p=zol q=zol kind=?(%sum %prod)]
  ^-  zol
  ::  ^mul: the bare name is this core's own algebraic multiplication
  =/  n=@ud  (^mul (deg:zx p) (deg:zx q))
  =/  i=@ud  0
  =|  pts=(list [t=@s v=@s])
  |-  ^-  zol
  ?:  (gth i n)  (lagrange (flop pts))
  =/  t=@s   (sun:si i)
  =/  qt=zol
    ?:(=(%sum kind) (shift-neg q t) (scale-pow q t))
  $(i +(i), pts [[t (res:zx p qt)] pts])
::
+|  %arithmetic
::    +add:  addition
::
::  Res_y(p(y), q(x-y)) has alpha + beta among its roots; +make picks out
::  the minimal polynomial.  The interval comes from interval arithmetic
::  on the operands, refined until it isolates exactly one root of the
::  resultant.
::
::  Terminates because the box shrinks to the point alpha + beta and the
::  resultant has finitely many roots.
++  add
  |=  [a=anum b=anum]
  ^-  anum
  ?:  ?&((is-rational a) (is-rational b))
    (of-q (add:qq (rat-of m.a) (rat-of m.b)))
  =/  r=zol   (bires m.a m.b %sum)
  =/  sq=zol  (sqpart:rr r)
  =/  x=ivl:rr  iv.a
  =/  y=ivl:rr  iv.b
  |-  ^-  anum
  =/  box=ivl:rr  [(add:qq lo.x lo.y) (add:qq hi.x hi.y)]
  ?:  =(1 (count:rr sq lo.box hi.box))  (make r box)
  $(x (refine:rr m.a x 1), y (refine:rr m.b y 1))
::    +sub:  subtraction
++  sub  |=([a=anum b=anum] ^-(anum (add a (neg b))))
::    +mul:  multiplication
::
::  Res_y(p(y), y^deg q * q(x/y)), with the same root selection.
::
::  The box is the min and max of the FOUR CORNER PRODUCTS, not
::  [lo1*lo2, hi1*hi2] -- which is wrong for any interval straddling
::  zero, and silently so.
++  mul
  |=  [a=anum b=anum]
  ^-  anum
  ?:  ?|((is-zero a) (is-zero b))  zero
  ?:  ?&((is-rational a) (is-rational b))
    (of-q (mul:qq (rat-of m.a) (rat-of m.b)))
  =/  r=zol   (bires m.a m.b %prod)
  =/  sq=zol  (sqpart:rr r)
  =/  x=ivl:rr  iv.a
  =/  y=ivl:rr  iv.b
  |-  ^-  anum
  =/  box=ivl:rr  (ibox x y)
  ?:  =(1 (count:rr sq lo.box hi.box))  (make r box)
  $(x (refine:rr m.a x 1), y (refine:rr m.b y 1))
::    +ibox:  the product of two intervals
++  ibox
  |=  [x=ivl:rr y=ivl:rr]
  ^-  ivl:rr
  =/  c1=frac  (mul:qq lo.x lo.y)
  =/  c2=frac  (mul:qq lo.x hi.y)
  =/  c3=frac  (mul:qq hi.x lo.y)
  =/  c4=frac  (mul:qq hi.x hi.y)
  [(qmin (qmin c1 c2) (qmin c3 c4)) (qmax (qmax c1 c2) (qmax c3 c4))]
::    +div:  division.  Crashes on a zero divisor
++  div  |=([a=anum b=anum] ^-(anum (mul a (inv b))))
::    +pow:  integer power
::
::  Binary square-and-multiply.  A negative exponent inverts first, and
::  so crashes on zero; alpha^0 is 1 for every alpha including zero.
++  pow
  |=  [a=anum e=@s]
  ^-  anum
  ?:  =(--0 e)  one
  ?.  (syn:si e)  (pow (inv a) (dif:si --0 e))
  =/  n=@ud     (abs:si e)
  =/  k=@ud     (dec (met 0 n))
  =/  acc=anum  a
  |-  ^-  anum
  ?:  =(0 k)  acc
  =/  nk=@ud    (dec k)
  =/  sq=anum   (mul acc acc)
  %=  $
    k    nk
    acc  ?:(=(1 (cut 0 [nk 1] n)) (mul sq a) sq)
  ==
::    +root:  the real k-th root
::
::  [a=anum k=@ud] -> (unit anum).  ~ when there is none: an even root of
::  a negative number.  Crashes on k = 0.
::
::  p(x^k) has every k-th root of alpha among its roots, so no resultant
::  is needed -- a substitution suffices.  The right one is picked by
::  raising each candidate to the k and comparing, which is exact.  For
::  even k both +g and -g qualify, so the non-negative one is taken.
++  root
  |=  [a=anum k=@ud]
  ^-  (unit anum)
  ?<  =(0 k)
  ?:  (is-zero a)  `zero
  ?:  ?&(=(0 (mod k 2)) =(%lt (sign a)))  ~
  =/  q=zol  (nrm (sub-pow m.a k))
  =/  cs  (isolate:rr q)
  |-  ^-  (unit anum)
  ?~  cs  ~
  =/  g=anum  (make q i.cs)
  ?.  =(%eq (cmp (pow g (sun:si k)) a))  $(cs t.cs)
  ?:  ?&(=(0 (mod k 2)) =(%lt (sign g)))  $(cs t.cs)
  `g
--
