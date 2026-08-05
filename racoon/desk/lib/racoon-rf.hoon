  ::  /lib/racoon-rf
::::  The rational function field over Q -- SPEC Milestone C, phase F
::
::  Q(x): quotients of polynomials, in lowest terms with a monic
::  denominator.  Phases F0 (the field), F1 (decomposition), and F2
::  (integration).  The Laplace transform is F3, in /lib/racoon-lt.
::
::  A CONSUMER of /lib/racoon, and of /lib/racoon-alg for the residues
::  in F2.  Seventh application of that rule; %zx and %qx stay frozen.
::
::  REPRESENTATION IS CANONICAL: .num and .den coprime, .den monic and
::  nonzero, zero written 0/1.  That is the unique representative of an
::  element of Q(x), so
::
::    - EQUALITY IS STRUCTURAL.  =(a b) decides it.
::    - every arm is `free`, and a jet may use any algorithm at all.
::
::  This is what SPEC F0 means by saying phase (B) will not be able to
::  promise the same: an expression language has no canonical form to
::  name, and by Richardson's theorem cannot get one.
::
::  A DOOR OVER ITS FACTORIZATION STEP, exactly as /lib/racoon-alg is.
::  .fir takes a primitive squarefree polynomial to its irreducibles;
::  +firr:zx is the default, and /lib/baloon-rf binds +factor:vh.
::  Partial fractions factors the denominator, which is the same cost
::  cliff SPEC V0 measured, so this is not decoration.
::
::  THREADING THE SAMPLE IS NORMATIVE (SPEC F1).  A consumer that calls
::  another door over the SAME sample must pass ~(. that fir) rather
::  than `that`: a caller who binds the fast factorizer here and gets
::  the slow one one layer down has been handed wrong performance and
::  no error.
::
::  PUBLIC API (SPEC F4): new of-q of-p zero one is-zero deg neg add sub
::  mul div inv pow deriv eval pderiv sqf-den fac-den poles pfrac
::  pfrac-full recombine hermite integrate.
::
::  Delegated helpers, which SPEC S14 lets change without escalation:
::  qone pone monic exact ppow to-z of-z pegcd psort split expand pf
::  terms pint residue.  They are reachable -- a door has no private
::  chapter, only a convention -- and resting on them is the caller's
::  risk, not this library's contract.
::
/-  *racoon
/+  racoon, rr=racoon-roots, al=racoon-alg
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  qx  qx:racoon
=<  ~(. rf firr:zx)
|%
::    +rf:  the field, as a door over its factorization step
++  rf
  |_  fir=$-(zol (list zol))
  +|  %types
  ::    $rfun:  a rational function over Q
  ::
  ::  .num and .den are coprime, .den is monic and nonzero.  Zero is
  ::  0/1, so it has exactly one representative and +is-zero is a
  ::  structural test rather than a computation.
  +$  rfun  [num=qol den=qol]
  ::    $pterm:  one partial-fraction term, n/d^e
  +$  pterm  [n=qol d=qol e=@ud]
  ::    $pfd:  a partial fraction decomposition, polynomial part first
  +$  pfd  [p=qol ts=(list pterm)]
  ::
  +|  %private
  ::    +qone:  1, as a rational
  ++  qone  ^-(frac [--1 1])
  ::    +pone:  1, as a polynomial
  ++  pone  ^-(qol ~[qone])
  ::    +monic:  scale to leading coefficient 1
  ++  monic
    |=  a=qol
    ^-  qol
    ?~  a  ~
    (scale:qx a (inv:qq (lc:qx a)))
  ::    +exact:  division asserted to leave no remainder
  ::
  ::  Every division in this library is exact by construction -- by a
  ::  gcd, by a squarefree part, by a factor.  Asserting it turns a
  ::  wrong quotient into a crash instead of a wrong answer.
  ++  exact
    |=  [a=qol b=qol]
    ^-  qol
    =/  d  (divmod:qx a b)
    ?>  (is-zero:qx r.d)
    q.d
  ::    +ppow:  a polynomial raised to a whole power
  ++  ppow
    |=  [a=qol e=@ud]
    ^-  qol
    =/  k=@ud   e
    =/  acc=qol  pone
    |-  ^-  qol
    ?:  =(0 k)  acc
    $(k (dec k), acc (mul:qx acc a))
  ::    +pderiv:  the formal derivative in Q[x]
  ::
  ::  Local because %qx has no +deriv -- SPEC R1 promoted one to %zx,
  ::  and this is four lines rather than a second escalation.
  ++  pderiv
    |=  a=qol
    ^-  qol
    ?~  a  ~
    =/  cs=qol  t.a
    =/  k=@ud   1
    =|  out=qol
    |-  ^-  qol
    ?~  cs  (canon:qx (flop out))
    $(cs t.cs, k +(k), out [(mul:qq i.cs [(sun:si k) 1]) out])
  ::    +to-z:  clear denominators, mapping Q[x] into Z[x]
  ::
  ::  Written out rather than calling +clear:qx, which SPEC S14 lists as
  ::  a DELEGATED helper: delegated arms may change without escalation,
  ::  and resting a whole phase on one to save twelve lines is the wrong
  ::  trade.  The scaling factor is discarded, which is right for every
  ::  caller here -- all of them rescale to monic or take a gcd.
  ++  to-z
    |=  a=qol
    ^-  zol
    ?~  a  ~
    =/  l=@ud
      =/  cs=qol  a
      =/  x=@ud   1
      |-  ^-  @ud
      ?~  cs  x
      $(cs t.cs, x (^div (^mul x q.i.cs) (gcd:nz:racoon x q.i.cs)))
    %-  canon:zx
    %+  turn  a
    |=(c=frac ^-(@s (pro:si p.c (sun:si (^div l q.c)))))
  ::    +of-z:  the canonical injection of Z[x] into Q[x]
  ++  of-z  |=(a=zol ^-(qol (turn a |=(c=@s ^-(frac [c 1])))))
  ::    +pegcd:  the extended Euclidean algorithm in Q[x]
  ::
  ::  [a b] -> [g s t] with s*a + t*b = g, g monic.  Q[x] is Euclidean,
  ::  so this is the textbook loop; it is here rather than in %qx
  ::  because only this library needs it.
  ::
  ::  Bezout and NOT undetermined coefficients (SPEC F3): solving a
  ::  linear system for the same numbers would work and would drag
  ::  Baloon in for nothing.
  ++  pegcd
    |=  [a=qol b=qol]
    ^-  [g=qol s=qol t=qol]
    =/  r0=qol  (canon:qx a)
    =/  r1=qol  (canon:qx b)
    =/  s0=qol  pone
    =/  s1=qol  ~
    =/  t0=qol  ~
    =/  t1=qol  pone
    |-  ^-  [g=qol s=qol t=qol]
    ?:  (is-zero:qx r1)
      ::  rescale so the gcd is monic, which makes the coprime case
      ::  read as g = 1 exactly
      ?~  r0  [~ ~ ~]
      =/  c=frac  (inv:qq (lc:qx r0))
      [(scale:qx r0 c) (scale:qx s0 c) (scale:qx t0 c)]
    =/  dm  (divmod:qx r0 r1)
    %=  $
      r0  r1
      r1  r.dm
      s0  s1
      s1  (sub:qx s0 (mul:qx q.dm s1))
      t0  t1
      t1  (sub:qx t0 (mul:qx q.dm t1))
    ==
  ::    +psort:  the pinned order on partial-fraction bases
  ++  psort  |=(fs=(list [p=qol m=@ud]) (sort fs |=([x=[p=qol *] y=[p=qol *]] ?!(=(%gt (pcmp:qx p.x p.y))))))
  ::
  +|  %field
  ::    +zero:  0/1
  ++  zero  ^-(rfun [~ pone])
  ::    +one:  1/1
  ++  one   ^-(rfun [pone pone])
  ::    +is-zero:  structural, because zero has one representative
  ++  is-zero  |=(f=rfun ^-(? =(~ num.f)))
  ::    +new:  reduce a pair to lowest terms with a monic denominator
  ::
  ::  The only arm accepting an unreduced pair, mirroring +canon in %zx
  ::  and +make in /lib/racoon-alg.  Crashes on a zero denominator.
  ++  new
    |=  [n=qol d=qol]
    ^-  rfun
    =/  nc=qol  (canon:qx n)
    =/  dc=qol  (canon:qx d)
    ?~  dc  !!
    ?:  (is-zero:qx nc)  zero
    =/  g=qol   (gcd:qx nc dc)
    =/  n2=qol  (exact nc g)
    =/  d2=qol  (exact dc g)
    =/  c=frac  (inv:qq (lc:qx d2))
    [(scale:qx n2 c) (scale:qx d2 c)]
  ::    +of-q:  embed a rational constant
  ++  of-q  |=(r=frac ^-(rfun (new ~[r] pone)))
  ::    +of-p:  embed a polynomial
  ++  of-p  |=(a=qol ^-(rfun (new a pone)))
  ::    +deg:  deg num - deg den, negative for a proper fraction
  ::
  ::  Crashes on zero, as +deg:zx does: the zero polynomial has no
  ::  degree and neither does the zero function.
  ++  deg
    |=  f=rfun
    ^-  @s
    ?<  (is-zero f)
    (dif:si (sun:si (deg:qx num.f)) (sun:si (deg:qx den.f)))
  ::    +neg:  negation, which cannot disturb the canonical form
  ++  neg  |=(f=rfun ^-(rfun [(neg:qx num.f) den.f]))
  ::    +add:  addition
  ++  add
    |=  [a=rfun b=rfun]
    ^-  rfun
    %+  new
      (add:qx (mul:qx num.a den.b) (mul:qx num.b den.a))
    (mul:qx den.a den.b)
  ::    +sub:  subtraction
  ++  sub  |=([a=rfun b=rfun] ^-(rfun (add a (neg b))))
  ::    +mul:  multiplication
  ++  mul
    |=  [a=rfun b=rfun]
    ^-  rfun
    (new (mul:qx num.a num.b) (mul:qx den.a den.b))
  ::    +inv:  the multiplicative inverse; crashes on zero
  ++  inv
    |=  f=rfun
    ^-  rfun
    ?<  (is-zero f)
    (new den.f num.f)
  ::    +div:  division; crashes on a zero divisor
  ++  div  |=([a=rfun b=rfun] ^-(rfun (mul a (inv b))))
  ::    +pow:  integer powers, negative ones through +inv
  ++  pow
    |=  [f=rfun e=@s]
    ^-  rfun
    =/  n=@ud  (abs:si e)
    =/  b=rfun  ?:((syn:si e) f (inv f))
    =/  k=@ud   n
    =/  acc=rfun  one
    |-  ^-  rfun
    ?:  =(0 k)  acc
    $(k (dec k), acc (mul acc b))
  ::    +deriv:  the quotient rule, then reduce
  ::
  ::  The reduction is NOT optional: (u/v)' comes out over v^2, which is
  ::  not in lowest terms whenever v has a repeated factor.
  ++  deriv
    |=  f=rfun
    ^-  rfun
    %+  new
      %+  sub:qx
        (mul:qx (pderiv num.f) den.f)
      (mul:qx num.f (pderiv den.f))
    (mul:qx den.f den.f)
  ::    +eval:  the value at a rational point; crashes at a pole
  ++  eval
    |=  [f=rfun x=frac]
    ^-  frac
    =/  dv=frac  (eval:qx den.f x)
    ?<  =(--0 p.dv)
    (div:qq (eval:qx num.f x) dv)
  ::
  +|  %decomposition
  ::    +sqf-den:  the squarefree factorization of a denominator
  ::
  ::  Needs no irreducible factorization, so it is cheap and always
  ::  available -- and it is the form Hermite reduction consumes.
  ++  sqf-den
    |=  d=qol
    ^-  (list [p=qol m=@ud])
    ?:  =(0 (deg:qx d))  ~
    %+  turn  fs:(sqfree:zx (to-z d))
    |=([p=zol m=@ud] ^-([qol @ud] [(monic (of-z p)) m]))
  ::    +fac-den:  the irreducible factorization of a denominator
  ::
  ::  Squarefree first, then .fir on each part: a squarefree part's
  ::  irreducible factors are distinct and all carry that part's
  ::  multiplicity.  This is +factor:zx's pipeline with the
  ::  recombination left open, which is what the door is for.
  ++  fac-den
    |=  d=qol
    ^-  (list [p=qol m=@ud])
    ?:  =(0 (deg:qx d))  ~
    %-  zing
    %+  turn  fs:(sqfree:zx (to-z d))
    |=  [p=zol m=@ud]
    ^-  (list [qol @ud])
    (turn (fir p) |=(q=zol ^-([qol @ud] [(monic (of-z q)) m])))
  ::    +poles:  the denominator's irreducible factors, with multiplicity
  ::
  ::  Exposed because a caller who wants them should not have to redo
  ::  the factorization the decomposition arms already paid for.
  ++  poles  |=(f=rfun ^-((list [p=qol m=@ud]) (psort (fac-den den.f))))
  ::    +split:  Chinese remaindering over pairwise coprime moduli
  ::
  ::  [r ms] -> the numerators a_k with r/prod(ms) = sum(a_k/m_k), for
  ::  PROPER r.  a_k is r * (D/m_k)^-1 reduced mod m_k, the inverse
  ::  coming from +pegcd -- which exists because the moduli are coprime.
  ++  split
    |=  [r=qol ms=(list qol)]
    ^-  (list qol)
    =/  big=qol
      =/  cs=(list qol)  ms
      =/  acc=qol  pone
      |-  ^-  qol
      ?~  cs  acc
      $(cs t.cs, acc (mul:qx acc i.cs))
    %+  turn  ms
    |=  m=qol
    ^-  qol
    =/  co=qol  (exact big m)
    =/  eg  (pegcd co m)
    ::  coprime, so the gcd is 1 and s is the inverse of co mod m
    ?>  =(pone g.eg)
    r:(divmod:qx (mul:qx r s.eg) m)
  ::    +expand:  a/g^e as a sum of c_j/g^j, ascending in j
  ::
  ::  Repeated division: a = q*g + rem gives c_e = rem, and the
  ::  quotient carries the rest at one lower power.
  ++  expand
    |=  [a=qol g=qol e=@ud]
    ^-  (list pterm)
    =/  k=@ud    e
    =/  cur=qol  a
    =|  out=(list pterm)
    |-  ^-  (list pterm)
    ?:  =(0 k)  out
    =/  dm  (divmod:qx cur g)
    $(k (dec k), cur q.dm, out [[r.dm g k] out])
  ::    +pf:  the partial fraction decomposition, against either basis
  ++  pf
    |=  [full=? f=rfun]
    ^-  pfd
    =/  dm  (divmod:qx num.f den.f)
    =/  fs=(list [p=qol m=@ud])
      (psort ?:(full (fac-den den.f) (sqf-den den.f)))
    =/  ms=(list qol)  (turn fs |=([p=qol m=@ud] ^-(qol (ppow p m))))
    =/  as=(list qol)  (split r.dm ms)
    ::  a zero numerator means that power does not occur; dropping it
    ::  keeps the decomposition canonical, since a term that is not
    ::  there and a term that is zero are the same function
    :-  q.dm
    %+  skip  (terms fs as)
    |=(t=pterm ^-(? (is-zero:qx n.t)))
  ::    +terms:  expand each numerator against its base and multiplicity
  ::
  ::  A named arm rather than a |- inside the %+ skip above: the inline
  ::  form walks two lists at once and the inferrer would not close on
  ::  it, reporting fuse-loop.
  ++  terms
    |=  [fs=(list [p=qol m=@ud]) as=(list qol)]
    ^-  (list pterm)
    ?~  fs  ~
    ?~  as  ~
    (weld (expand i.as p.i.fs m.i.fs) $(fs t.fs, as t.as))
  ::    +pfrac:  decomposition against the SQUAREFREE factorization
  ++  pfrac       |=(f=rfun ^-(pfd (pf %.n f)))
  ::    +pfrac-full:  decomposition against the irreducible factorization
  ++  pfrac-full  |=(f=rfun ^-(pfd (pf %.y f)))
  ::    +recombine:  a decomposition back to the function it came from
  ::
  ::  Public because it is the property test worth having, and a caller
  ::  should not have to write it a second time.
  ++  recombine
    |=  d=pfd
    ^-  rfun
    =/  ts=(list pterm)  ts.d
    =/  acc=rfun  (of-p p.d)
    |-  ^-  rfun
    ?~  ts  acc
    $(ts t.ts, acc (add acc (new n.i.ts (ppow d.i.ts e.i.ts))))
  ::
  +|  %integration
  ::    +pint:  the antiderivative of a polynomial, constant term zero
  ++  pint
    |=  a=qol
    ^-  qol
    =/  cs=qol   a
    =/  k=@ud    0
    =/  out=qol  ~[[--0 1]]
    |-  ^-  qol
    ?~  cs  (canon:qx (flop out))
    $(cs t.cs, k +(k), out [(div:qq i.cs [(sun:si +(k)) 1]) out])
  ::    +hermite:  Hermite reduction
  ::
  ::  [f] -> [rat log], where +rat is a closed-form piece of the
  ::  antiderivative and +log is what remains -- a proper fraction whose
  ::  denominator is SQUAREFREE, so nothing is left but logarithms.
  ::
  ::  Per squarefree term c/g^j with j >= 2: g is squarefree, so g and
  ::  g' are coprime and +pegcd gives s*g + t*g' = 1.  Then
  ::
  ::      c/g^j = c*s/g^(j-1) + c*t*g'/g^j
  ::
  ::  and integrating the second by parts, with v = -1/((j-1)g^(j-1)),
  ::
  ::      int c*t*g'/g^j = -c*t/((j-1)g^(j-1)) + int (c*t)'/((j-1)g^(j-1))
  ::
  ::  so the first piece is closed form and the rest reappears at power
  ::  j-1.  Descending to j = 1 terminates in at most j steps per term.
  ::
  ::  The polynomial part is integrated straight into .rat: it is
  ::  closed form too, and leaving it in .log would break that arm's
  ::  contract that the denominator is squarefree.
  ++  hermite
    |=  f=rfun
    ^-  [rat=rfun log=rfun]
    =/  d=pfd  (pfrac f)
    =/  ts=(list pterm)  ts.d
    =/  rat=rfun  (of-p (pint p.d))
    =/  lg=rfun   zero
    |-  ^-  [rat=rfun log=rfun]
    ?~  ts  [rat lg]
    =/  c=qol   n.i.ts
    =/  g=qol   d.i.ts
    =/  j=@ud   e.i.ts
    =/  acc=rfun  rat
    =/  inner
      |-  ^-  [r=rfun n=qol]
      ?:  =(1 j)  [acc c]
      =/  eg  (pegcd g (pderiv g))
      ?>  =(pone g.eg)
      =/  ct=qol  (mul:qx c t.eg)
      =/  cs=qol  (mul:qx c s.eg)
      =/  jm=@ud  (dec j)
      ::  rat -= c*t / ((j-1) * g^(j-1)); +new absorbs the scalar
      =/  nr=rfun
        %-  neg
        (new ct (scale:qx (ppow g jm) [(sun:si jm) 1]))
      %=  $
        acc  (add acc nr)
        c    (add:qx cs (scale:qx (pderiv ct) [--1 jm]))
        j    jm
      ==
    $(ts t.ts, rat r.inner, lg (add lg (new n.inner g)))
  ::    +residue:  the residue at the roots of an irreducible factor
  ::
  ::  [a d g] -> (unit frac).  For squarefree d with irreducible factor
  ::  g, every root alpha of g has residue a(alpha)/d'(alpha).  Those
  ::  residues are all equal to one RATIONAL c exactly when
  ::  a * (d')^-1 mod g is the constant c, which is what this tests.
  ::
  ::  This is Rothstein-Trager without forming the resultant: the RT
  ::  polynomial's roots ARE these residues, and testing each
  ::  irreducible factor directly avoids a bivariate resultant, an
  ::  interpolation, and a second factorization.
  ::
  ::  ~ means the residues at g are irrational -- conjugates rather
  ::  than one rational number.  See +integrate.
  ++  residue
    |=  [a=qol d=qol g=qol]
    ^-  (unit frac)
    =/  eg  (pegcd (pderiv d) g)
    ?.  =(pone g.eg)  ~
    =/  v=qol  r:(divmod:qx (mul:qx a s.eg) g)
    ?~  v  `[--0 1]
    ?.  =(0 (deg:qx v))  ~
    `i.v
  ::    +integrate:  the antiderivative, when it is in range
  ::
  ::  [f] -> (unit [rat ls]), where the answer is
  ::
  ::      rat + sum over ls of c * log(a)
  ::
  ::  and every c is RATIONAL.  ~ when it is not; see below.
  ::
  ::  WHAT IS OUT OF RANGE, AND WHY IT IS NARROWER THAN SPEC F6 SAID.
  ::  §F6 was written expecting real algebraic residues to be usable,
  ::  since /lib/racoon-alg can name them.  Naming them is not the
  ::  problem.  The log ARGUMENT is gcd(a - c*d', d) computed over
  ::  Q(c)[x], and polynomial arithmetic over an algebraic extension of
  ::  Q does not exist in this project -- /lib/racoon-fp3 has the shape
  ::  for F_p and nothing has it for Q.  So the reachable class is the
  ::  RATIONAL residues, not the real ones, and §F6 is corrected rather
  ::  than quietly narrowed.
  ::
  ::  That class is bigger than "the denominator splits into linear
  ::  factors": int 2x/(x^2+1) has residue 1 at both roots and comes
  ::  back as log(x^2+1).  What it excludes is a residue that genuinely
  ::  differs between conjugate roots.  Lifting it wants either
  ::  Lazard-Rioboo-Trager or a RootSum representation, and both are
  ::  new specification rather than new code.
  ++  integrate
    |=  f=rfun
    ^-  (unit [rat=rfun ls=(list [c=frac a=qol])])
    =/  h  (hermite f)
    =/  a=qol  num.log.h
    =/  d=qol  den.log.h
    ?:  (is-zero:qx a)  `[rat.h ~]
    =/  fs=(list [p=qol m=@ud])  (psort (fac-den d))
    =|  ls=(list [c=frac a=qol])
    |-  ^-  (unit [rat=rfun ls=(list [c=frac a=qol])])
    ?~  fs  `[rat.h (flop ls)]
    =/  rc  (residue a d p.i.fs)
    ?~  rc  ~
    ::  a zero residue contributes nothing, and log(g) with coefficient
    ::  zero is not a term
    ?:  =(--0 p.u.rc)  $(fs t.fs)
    $(fs t.fs, ls [[u.rc p.i.fs] ls])
  --
--
