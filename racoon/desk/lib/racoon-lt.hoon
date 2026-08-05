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
::  whose irreducible factors are linear or quadratic, at ANY
::  multiplicity -- repeated poles included, by the recurrence in
::  +base-pq.  A factor of degree 3 or more, or a quadratic whose roots
::  are real and irrational, is out of range and returns ~ (SPEC F6).
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
  ::    +fact:  n! as a rational
  ++  fact
    |=  n=@ud
    ^-  frac
    =/  i=@ud    1
    =/  acc=@ud  1
    |-  ^-  frac
    ?:  (gth i n)  [(sun:si acc) 1]
    $(i +(i), acc (mul acc i))
  ::    +tmul:  multiply by t, which is k+1 on every term
  ::
  ::  No +canon needed: raising every k by one preserves both
  ::  distinctness and the pinned order, since k is the last sort key.
  ++  tmul  |=(e=expo ^-(expo (turn e |=(x=eterm ^-(eterm x(k +(k.x)))))))
  ::    +setsig:  multiply by e^(g*t), on terms that carry no exponential
  ::
  ::  +canon IS needed here: sig is the FIRST sort key, so changing it
  ::  reorders.
  ++  setsig
    |=  [e=expo g=frac]
    ^-  expo
    (canon (turn e |=(x=eterm ^-(eterm x(sig g)))))
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
    ::  the degenerate sine is NOT a distinct term.  sin(wt)/w -> t as
    ::  w -> 0, so [c k sig 0 %sin] is c*t^(k+1)*e^(sig t), which is
    ::  [c k+1 sig 0 %cos] -- and without this rewrite two $eterm
    ::  denote one function, +laplace maps them to the same $rfun, and
    ::  the claim that equality is structural is false.  Nothing in this
    ::  library produces such a term; a caller can write one.
    =/  ts=expo
      %+  sort
        %+  turn  e
        |=  x=eterm
        ^-  eterm
        ?.  ?&(=(%sin tr.x) (is-qz wsq.x))  x
        x(k +(k.x), tr %cos)
      eord
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
  ::    +base-pq:  the two inverse transforms of a repeated quadratic
  ::
  ::  [w j] -> [p q], where with q(s) = s^2 + w,
  ::
  ::      P_j = L^-1{ s / q^j }        Q_j = L^-1{ 1 / q^j }
  ::
  ::  at sigma = 0.  Both come from differentiating the transform, which
  ::  is the same L{t*f} = -F'(s) the t^k ladder in +lap-term uses:
  ::
  ::      P_1 = cos(wt)                Q_1 = sin(wt)/w
  ::      P_(j+1) = t*Q_j / (2j)
  ::      Q_(j+1) = [(2j-1)*Q_j - t*P_j] / (2*j*w)
  ::
  ::  The second falls out of d/ds[s/q^j] once s^2 is rewritten as
  ::  q - w, which is what keeps a w in the denominator rather than an
  ::  s.  Checked against SymPy at j = 1, 2, 3 before being written, and
  ::  checked here by the round trip afterwards.
  ::
  ::  Everything stays rational: the normalized sine basis carries the
  ::  1/omega, and w -- not omega -- is what the recurrence divides by.
  ++  base-pq
    |=  [w=frac j=@ud]
    ^-  [p=expo q=expo]
    =/  p=expo  ~[[qo 0 qz w %cos]]
    =/  q=expo  ~[[qo 0 qz w %sin]]
    =/  i=@ud   1
    |-  ^-  [p=expo q=expo]
    ?:  (gte i j)  [p q]
    =/  tw=frac  (qi (sun:si (mul 2 i)))
    =/  np=expo  (escale (tmul q) (inv:qq tw))
    =/  nq=expo
      %+  escale
        %+  eadd
          (escale q (qi (sun:si (dec (mul 2 i)))))
        (escale (tmul p) (qi -1))
      (inv:qq (mul:qq tw w))
    $(i +(i), p np, q nq)
  ::
  +|  %integration
  ::    +bkeys:  the distinct (sig, wsq) blocks of a CANONICAL $expo
  ::
  ::  +canon sorts by sig then wsq, so equal keys are adjacent and this
  ::  is one pass.
  ++  bkeys
    |=  e=expo
    ^-  (list [g=frac w=frac])
    ::  the previous key is carried as a plain value rather than read
    ::  back off the accumulator: ?= on the accumulator refines it, and
    ::  then +snag will not nest against the refined type
    =/  cs=expo  e
    =/  hav=?   %.n
    =/  lst=[g=frac w=frac]  [qz qz]
    =|  out=(list [g=frac w=frac])
    |-  ^-  (list [g=frac w=frac])
    ?~  cs  (flop out)
    =/  ky=[g=frac w=frac]  [sig.i.cs wsq.i.cs]
    ?:  &(hav =(ky lst))  $(cs t.cs)
    $(cs t.cs, hav %.y, lst ky, out [ky out])
  ::    +at-zero:  the value at t = 0
  ::
  ::  Only k = 0 cosine terms survive it: t^k vanishes for k > 0, and
  ::  every sine term is zero at the origin -- including the degenerate
  ::  one, which +canon has already rewritten into a cosine anyway.
  ++  at-zero
    |=  e=expo
    ^-  frac
    =/  cs=expo   e
    =/  acc=frac  qz
    |-  ^-  frac
    ?~  cs  acc
    ?.  ?&(=(0 k.i.cs) =(%cos tr.i.cs))  $(cs t.cs)
    $(cs t.cs, acc (add:qq acc c.i.cs))
  ::    +blk-int:  integrate one (sig, wsq) block
  ::
  ::  Writing a block as the coefficient pairs (a_k, b_k) of
  ::  t^k cos and t^k sin-normalized, +ederiv acts as
  ::
  ::      D_k = M E_k + (k+1) E_(k+1),      M = [[sig 1] [-wsq sig]]
  ::
  ::  -- block-triangular, level k feeding level k-1.  So integration is
  ::  the same recurrence read DOWNWARD from the top level, which is why
  ::  this arm solves rather than substitutes: there is no closed form to
  ::  apply term by term, but there is an exactly determined system.
  ::
  ::  det M = sig^2 + wsq, and it is zero only when both are, so the one
  ::  special case is the pure polynomial in t -- the only block where
  ::  integration RAISES k rather than preserving it.
  ++  blk-int
    |=  [g=frac w=frac ts=expo]
    ^-  expo
    =/  det=frac  (add:qq (mul:qq g g) w)
    ?:  (is-qz det)
      %+  turn  ts
      |=  x=eterm
      ^-  eterm
      x(c (div:qq c.x (qi (sun:si +(k.x)))), k +(k.x))
    =/  kk=@ud
      =/  m=@ud   0
      =/  cs=expo  ts
      |-  ^-  @ud
      ?~  cs  m
      $(cs t.cs, m (max m k.i.cs))
    ::  the derivative's coefficients, indexed by k
    =/  ds=(list [a=frac b=frac])
      %+  turn  (gulf 0 kk)
      |=  k=@ud
      ^-  [a=frac b=frac]
      =/  cs=expo   ts
      =/  a=frac    qz
      =/  b=frac    qz
      |-  ^-  [a=frac b=frac]
      ?~  cs  [a b]
      ?.  =(k k.i.cs)  $(cs t.cs)
      ?:  =(%cos tr.i.cs)  $(cs t.cs, a (add:qq a c.i.cs))
      $(cs t.cs, b (add:qq b c.i.cs))
    =/  i=@ud  0
    =/  nx=[a=frac b=frac]  [qz qz]
    =/  res=expo  ~
    |-  ^-  expo
    ?:  (gth i kk)  (canon res)
    =/  k=@ud   (sub kk i)
    =/  d=[a=frac b=frac]  (snag k ds)
    =/  kp=frac  (qi (sun:si +(k)))
    ::  the right-hand side, less what level k+1 already contributed
    =/  ra=frac  (sub:qq a.d (mul:qq kp a.nx))
    =/  rb=frac  (sub:qq b.d (mul:qq kp b.nx))
    ::  M^-1 = (1/det) [[sig -1] [wsq sig]]
    =/  ea=frac  (div:qq (sub:qq (mul:qq g ra) rb) det)
    =/  eb=frac  (div:qq (add:qq (mul:qq w ra) (mul:qq g rb)) det)
    %=  $
      i    +(i)
      nx   [ea eb]
      ::  annotated: an un-typed ~[...] infers as a fixed tuple, which
      ::  the wet +skip cannot nest
      res
        %+  weld
          %+  skip  `expo`~[[ea k g w %cos] [eb k g w %sin]]
          |=(x=eterm ^-(? (is-qz c.x)))
        res
    ==
  ::    +eintegrate:  the antiderivative vanishing at t = 0
  ::
  ::  The constant is pinned to make the product a function of the input
  ::  alone, exactly as SPEC F3 pins it for +integrate on $rfun.  With
  ::  that convention this is the definite integral from 0 to t, so
  ::  L{eintegrate(e)} is laplace(e)/s -- which is how the suite checks
  ::  it against an arm that does not share a line of code with it.
  ++  eintegrate
    |=  e=expo
    ^-  expo
    =/  ce=expo  (canon e)
    =/  cs=(list [g=frac w=frac])  (bkeys ce)
    =/  acc=expo  ~
    |-  ^-  expo
    ?~  cs
      =/  v0=frac  (at-zero acc)
      ?:  (is-qz v0)  (canon acc)
      (canon [[(neg:qq v0) 0 qz qz %cos] acc])
    =/  blk=expo
      %+  skim  ce
      |=  x=eterm
      ^-  ?
      ?&  =(%eq (cmp:qq sig.x g.i.cs))
          =(%eq (cmp:qq wsq.x w.i.cs))
      ==
    $(cs t.cs, acc (weld acc (blk-int g.i.cs w.i.cs blk)))
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
    =/  dg=@ud  (deg:qx d.t)
    ?:  =(1 dg)
      ::  c/(s-r)^e is c * t^(e-1) * e^(rt) / (e-1)!, which at e = 1 is
      ::  the plain exponential
      =/  r=frac  (neg:qq (coef d.t 0))
      =/  c=frac  (div:qq (coef n.t 0) (fact (dec e.t)))
      `~[[c (dec e.t) r qz %cos]]
    ?.  =(2 dg)  ~
    =/  b=frac    (coef d.t 1)
    =/  c0=frac   (coef d.t 0)
    =/  sig=frac  (neg:qq (div:qq b (qi --2)))
    =/  wsq=frac  (sub:qq c0 (div:qq (mul:qq b b) (qi --4)))
    ?.  =(%gt (cmp:qq wsq qz))  ~
    ::  n = A*(s - sig) + (A*sig + B), so the two pieces ride P_e and
    ::  Q_e, and the exponential comes back on at the end
    =/  aa=frac  (coef n.t 1)
    =/  bb=frac  (add:qq (coef n.t 0) (mul:qq aa sig))
    =/  pq  (base-pq wsq e.t)
    :-  ~
    %+  setsig
      (eadd (escale p.pq aa) (escale q.pq bb))
    sig
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
