  ::  /lib/racoon-lt
::::  The Laplace transform -- SPEC Milestone C, phase F3
::
::  A CONSUMER of /lib/racoon and /lib/racoon-rf, and of nothing else.
::  In particular NOT of /lib/racoon-alg: see the note on $eterm below,
::  which is why every coefficient here is rational.
::
::  A DOOR OVER THE SAME FACTORIZATION SAMPLE as /lib/racoon-rf, threaded
::  through to it -- +inverse takes a partial fraction decomposition, so
::  it factors, so it inherits that cliff.  SPEC F1 makes the threading
::  normative and this is the file it is about: `rf` below is
::  ~(. rfd fir) and never plain `rfd`.
::
::  WHAT IS BUILT.  +laplace is total.  +inverse handles denominators
::  whose irreducible factors are SIMPLE -- multiplicity one -- and
::  linear or quadratic.  Repeated factors return ~; that is the second
::  half of F3 and is not written, because the expansion of
::  1/((s-sig)^2 + wsq)^m is a recurrence and a recurrence wants the
::  round trip below as its test rather than as its afterthought.
::
::  THE ROUND TRIP IS THE TEST.  +laplace was built first on purpose: it
::  is the k-th s-derivative of a base transform, which is +deriv:rf
::  applied k times, so it leans on an arm already verified rather than
::  on a closed formula written out by hand.  Then
::  laplace(inverse(f)) = f checks +inverse against it, and two errors
::  would have to agree exactly to survive that.
::
/-  *racoon
/+  racoon, rfd=racoon-rf
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  qx  qx:racoon
=<  ~(. lt firr:zx)
|%
::    +lt:  the transform, as a door over its factorization step
++  lt
  |_  fir=$-(zol (list zol))
  +|  %types
  ::    $eterm:  one exponential-polynomial term
  ::
  ::      %cos   c * t^k * e^(sig*t) * cos(sqrt(wsq)*t)
  ::      %sin   c * t^k * e^(sig*t) * sin(sqrt(wsq)*t) / sqrt(wsq)
  ::
  ::  EVERY COEFFICIENT IS RATIONAL, and the /sqrt(wsq) in the %sin case
  ::  is what makes that possible -- SPEC F5 records the version of this
  ::  type that carried $anum coefficients and why it does not work.
  ::  The short form: L{e^(sig t)} is 1/(s - sig), which is not a
  ::  rational function over Q when sig is irrational, so the transform
  ::  would not land in $rfun and the two arms would not compose.
  ::  Completing the square on a rational quadratic gives sig and wsq
  ::  both rational; only the frequency itself is irrational, and the
  ::  sine always arrives carrying a compensating 1/omega.
  ::
  ::  wsq = 0 with %cos is the pure exponential, since cos 0 = 1.  The
  ::  %sin convention degenerates continuously there too, since
  ::  sin(wt)/w -> t, which is the same t^k ladder repeated roots walk.
  +$  eterm  [c=frac k=@ud sig=frac wsq=frac tr=?(%cos %sin)]
  ::    $expo:  a finite sum, sorted, no zero coefficients
  +$  expo  (list eterm)
  ::
  +|  %private
  ::    +rf:  the rational function field, AT THIS BINDING
  ::
  ::  ~(. rfd fir) and not rfd: SPEC F1 makes threading the sample
  ::  normative, and this is the line it is about.
  ++  rf  ~(. rfd fir)
  ::    +qz:  0, as a rational
  ++  qz  ^-(frac [--0 1])
  ::    +qo:  1, as a rational
  ++  qo  ^-(frac [--1 1])
  ::    +qi:  a rational from a small integer
  ++  qi  |=(n=@s ^-(frac [n 1]))
  ::    +is-qz:  is this rational zero?
  ++  is-qz  |=(a=frac ^-(? =(--0 p.a)))
  ::    +coef:  the coefficient of x^i, zero past the end
  ++  coef
    |=  [a=qol i=@ud]
    ^-  frac
    ?:  (gte i (lent a))  qz
    (snag i a)
  ::    +ekey:  the pinned sort key, as a comparison
  ::
  ::  Ascending by sig, then wsq, then %cos before %sin, then k.  The
  ::  order is pinned so that $expo is canonical and the arms stay
  ::  `free`; any total order would do and this one is chosen.
  ++  eord
    |=  [x=eterm y=eterm]
    ^-  ?
    =/  cs  (cmp:qq sig.x sig.y)
    ?.  =(%eq cs)  =(%lt cs)
    =/  cw  (cmp:qq wsq.x wsq.y)
    ?.  =(%eq cw)  =(%lt cw)
    ?.  =(tr.x tr.y)  =(%cos tr.x)
    (lte k.x k.y)
  ::    +same:  do two terms differ only in their coefficient?
  ++  same
    |=  [x=eterm y=eterm]
    ^-  ?
    ?&  =(k.x k.y)
        =(tr.x tr.y)
        =(%eq (cmp:qq sig.x sig.y))
        =(%eq (cmp:qq wsq.x wsq.y))
    ==
  ::
  +|  %expo
  ::    +canon:  sort, combine like terms, drop zero coefficients
  ::
  ::  The only arm accepting an unsorted or redundant list.  Every other
  ::  arm produces canonical output, so =(a b) decides equality.
  ::
  ::  Written with +snag and +slag rather than ?~: ?~ REFINES the
  ::  accumulator to the empty list inside its branch, and the next
  ::  iteration assigns a one-element list back to it, which then fails
  ::  to nest.  Guarding with =(~ ...) leaves the types alone.
  ++  canon
    |=  e=expo
    ^-  expo
    =/  ts=expo   (sort e eord)
    =/  cur=expo  ~
    =|  out=expo
    |-  ^-  expo
    ::  the pending term, kept unless it cancelled to zero
    =/  flush=expo
      ?:  |(=(~ cur) (is-qz c:(snag 0 cur)))  out
      [(snag 0 cur) out]
    ?:  =(~ ts)  (flop flush)
    =/  hd=eterm  (snag 0 ts)
    ?:  =(~ cur)  $(ts (slag 1 ts), cur ~[hd])
    =/  cu=eterm  (snag 0 cur)
    ?:  (same cu hd)
      $(ts (slag 1 ts), cur ~[cu(c (add:qq c.cu c.hd))])
    $(ts (slag 1 ts), cur ~[hd], out flush)
  ::    +escale:  multiply through by a rational
  ++  escale
    |=  [e=expo r=frac]
    ^-  expo
    ?:  (is-qz r)  ~
    (canon (turn e |=(x=eterm ^-(eterm x(c (mul:qq c.x r))))))
  ::    +eadd:  add two exponential polynomials
  ++  eadd  |=([a=expo b=expo] ^-(expo (canon (weld a b))))
  ::    +ederiv:  d/dt, which the class is closed under
  ::
  ::  For the %cos term, the three pieces are the power rule, the
  ::  exponential, and the derivative of the cosine -- and that last one
  ::  contributes -w*sin(wt), which in the normalized basis is
  ::  -wsq * [sin(wt)/w].  That is the second place the /omega
  ::  convention pays for itself.
  ++  ederiv
    |=  e=expo
    ^-  expo
    %-  canon
    %-  zing
    %+  turn  e
    |=  x=eterm
    ^-  expo
    =/  pw=expo
      ?:  =(0 k.x)  ~
      ~[x(c (mul:qq c.x (qi (sun:si k.x))), k (dec k.x))]
    %+  weld  pw
    ?:  =(%cos tr.x)
      :~  x(c (mul:qq c.x sig.x))
          x(c (neg:qq (mul:qq c.x wsq.x)), tr %sin)
      ==
    :~  x(c (mul:qq c.x sig.x))
        x(tr %cos)
    ==
  ::
  +|  %transform
  ::    +lap-term:  the transform of one term
  ::
  ::  Base case, with q = (s - sig)^2 + wsq:
  ::
  ::      %cos   (s - sig) / q
  ::      %sin           1 / q
  ::
  ::  both rational over Q.  Then L{t^k f(t)} = (-1)^k F^(k)(s), so the
  ::  t^k ladder is k applications of +deriv:rf -- an arm that is
  ::  already tested -- rather than a closed formula.
  ++  lap-term
    |=  x=eterm
    ^-  rfun:rf
    =/  den=qol
      %-  canon:qx
      :~  (add:qq (mul:qq sig.x sig.x) wsq.x)
          (neg:qq (mul:qq (qi --2) sig.x))
          qo
      ==
    =/  num=qol
      ?:(=(%cos tr.x) (canon:qx ~[(neg:qq sig.x) qo]) (canon:qx ~[qo]))
    =/  base=rfun:rf  (new:rf num den)
    =/  j=@ud  k.x
    =/  acc=rfun:rf  base
    |-  ^-  rfun:rf
    ?.  =(0 j)  $(j (dec j), acc (deriv:rf acc))
    ::  (-1)^k times the k-th derivative, scaled by the coefficient
    =/  sg=frac  ?:(=(0 (mod k.x 2)) c.x (neg:qq c.x))
    (mul:rf (of-q:rf sg) acc)
  ::    +laplace:  the transform, total
  ++  laplace
    |=  e=expo
    ^-  rfun:rf
    =/  ts=expo  e
    =/  acc=rfun:rf  zero:rf
    |-  ^-  rfun:rf
    ?~  ts  acc
    $(ts t.ts, acc (add:rf acc (lap-term i.ts)))
  ::    +inv-term:  the inverse of one partial-fraction term
  ::
  ::  ~ when the term is out of range, which is what +inverse reports.
  ::  Three cases and only three:
  ::
  ::    e > 1        a repeated factor.  Not built; see the header.
  ::    deg g = 1    g = s - r monic, so r = -g_0, and n/(s-r) is
  ::                 n * e^(rt) -- a %cos term at wsq = 0.
  ::    deg g = 2    complete the square: sig = -b/2, wsq = c - b^2/4.
  ::                 Writing n = A(s - sig) + (A*sig + B) splits it into
  ::                 the cosine and the normalized sine exactly.
  ::
  ::  wsq must be POSITIVE.  An irreducible rational quadratic has
  ::  either complex roots, and then wsq > 0, or irrational real ones,
  ::  and then wsq < 0 and the exponents would be irrational -- which
  ::  $eterm cannot hold and SPEC F6 excludes.
  ++  inv-term
    |=  t=pterm:rf
    ^-  (unit expo)
    ?.  =(1 e.t)  ~
    =/  dg=@ud  (deg:qx d.t)
    ?:  =(1 dg)
      =/  r=frac  (neg:qq (coef d.t 0))
      `~[[(coef n.t 0) 0 r qz %cos]]
    ?.  =(2 dg)  ~
    =/  b=frac   (coef d.t 1)
    =/  c0=frac  (coef d.t 0)
    =/  sig=frac  (neg:qq (div:qq b (qi --2)))
    =/  wsq=frac  (sub:qq c0 (div:qq (mul:qq b b) (qi --4)))
    ?.  =(%gt (cmp:qq wsq qz))  ~
    =/  aa=frac  (coef n.t 1)
    =/  bb=frac  (coef n.t 0)
    :-  ~
    :~  [aa 0 sig wsq %cos]
        [(add:qq bb (mul:qq aa sig)) 0 sig wsq %sin]
    ==
  ::    +inverse:  the inverse transform, when it is in range
  ::
  ::  ~ rather than a crash: being out of range is a property of the
  ::  input that a caller could not reasonably have checked (SPEC F7).
  ::  A polynomial part is out of range too -- the transform of an
  ::  $expo is always strictly proper, so anything else would be a
  ::  delta and those are not in this class.
  ++  inverse
    |=  f=rfun:rf
    ^-  (unit expo)
    ?:  (is-zero:rf f)  `~
    =/  d  (pfrac-full:rf f)
    ?.  (is-zero:qx p.d)  ~
    =/  ts=(list pterm:rf)  ts.d
    =|  acc=expo
    |-  ^-  (unit expo)
    ?~  ts  `(canon acc)
    =/  it  (inv-term i.ts)
    ?~  it  ~
    $(ts t.ts, acc (weld acc u.it))
  ::    +solve-ode:  a constant-coefficient homogeneous linear ODE
  ::
  ::  [p ics] -> (unit expo), where p is the characteristic polynomial
  ::  and .ics is y(0), y'(0), ... in order.  Transforming
  ::  sum a_i y^(i) = 0 term by term, with
  ::  L{y^(i)} = s^i Y - sum_{j<i} s^(i-1-j) y^(j)(0), gives p(s)Y = Q
  ::  with Q = sum_i a_i sum_{j<i} y^(j)(0) s^(i-1-j).  Then invert.
  ::
  ::  Crashes on the wrong number of initial conditions, which is a
  ::  caller error rather than an input out of range (SPEC F7); returns
  ::  ~ when the characteristic polynomial is out of +inverse's range.
  ++  solve-ode
    |=  [p=qol ics=(list frac)]
    ^-  (unit expo)
    ?>  =((deg:qx p) (lent ics))
    (inverse (new:rf (ode-num p ics) p))
  ::    +ode-num:  the numerator the initial conditions contribute
  ::
  ::  A named arm rather than a loop inside +solve-ode: the inner sum
  ::  produces a $qol and the outer one a (unit expo), and a nested |-
  ::  cannot be cast to both.
  ++  ode-num
    |=  [p=qol ics=(list frac)]
    ^-  qol
    =/  n=@ud  (deg:qx p)
    =/  i=@ud  1
    =/  q=qol  ~
    |-  ^-  qol
    ?:  (gth i n)  q
    =/  ai=frac  (coef p i)
    =/  inner=qol
      =/  j=@ud    0
      =/  acc=qol  ~
      |-  ^-  qol
      ?:  =(j i)  acc
      %=  $
        j    +(j)
        acc
          %+  add:qx  acc
          (shift:qx ~[(mul:qq ai (snag j ics))] (sub (dec i) j))
      ==
    $(i +(i), q (add:qx q inner))
  --
--
