  ::  /lib/racoon-roots
::::  Real-root isolation over Z[x] -- SPEC Milestone C, phase R
::
::  Racoon is named for real algebraic numbers and did not produce any.
::  Phases R0, R1, and R2: an EXACT count of the distinct real roots in
::  any rational interval, the exact rational roots, and a canonical
::  isolating interval for every root with refinement on demand.
::
::  A root of p isolated to an interval IS an exact object: the pair
::  (p, interval) determines one real algebraic number and no other, and
::  +refine narrows it to any width without ever leaving Q.  What this
::  library does NOT do is arithmetic on such numbers -- adding or
::  multiplying two of them needs resultants and a minimal polynomial,
::  which SPEC R8 fences out as separate work.
::
::  This is a CONSUMER of /lib/racoon, not part of it.  %zx and %qx froze
::  under R6 at Milestone A's P2 gate; nothing inside the frozen library
::  needs root isolation, so nothing needs it there.  Fourth application
::  of that rule, after racoon-fmt, racoon-rs, racoon-fp3, and
::  racoon-zfac.
::
::  EVERY ARM HERE IS `free` (SPEC R4).  Counting roots has one right
::  answer, so a jet may use Descartes with Taylor shifts, VCA, or
::  anything else.  Sturm is the reference because it is simpler and more
::  obviously correct, which is this project's stated order of priorities.
::
::  NO FLOATING POINT, and none later either: every endpoint here is an
::  exact $frac and stays one.  Lagoon owns approximation.
::
/-  *racoon
/+  racoon, zf=racoon-zfac
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  qx  qx:racoon
|%
+|  %types
::    $ivl:  an isolating interval for exactly one real root
::
::  Declared here rather than in /sur/racoon: SPEC §6 is pinned, and a
::  consumer adding to it would be an escalation for no gain.  See
::  SPEC-QUESTIONS R2.
::
::  lo <= hi always.  lo = hi means the root is EXACTLY that rational --
::  a degenerate interval, not an approximation that happens to be tight.
+$  ivl  [lo=frac hi=frac]
::    $rrt:  a real root, isolated, with its multiplicity in the input
+$  rrt  [iv=ivl m=@ud]
::
+|  %private
::    +qneg:  negate a rational
++  qneg  |=(x=frac ^-(frac (neg:qq x)))
::    +vars:  sign changes in a list of signs, ignoring %eq
::
::  Zeros are skipped rather than counted, which is what makes Sturm's
::  theorem hold at a point where some chain member vanishes.
++  vars
  |=  ss=(list ord)
  ^-  @ud
  =/  rest=(list ord)  ss
  =/  prev=ord         %eq
  =/  n=@ud            0
  |-  ^-  @ud
  ?~  rest  n
  ?:  =(%eq i.rest)  $(rest t.rest)
  ?:  =(%eq prev)    $(rest t.rest, prev i.rest)
  ?:  =(prev i.rest)  $(rest t.rest, prev i.rest)
  $(rest t.rest, prev i.rest, n +(n))
::
::    +half:  the midpoint scale, x/2
++  half  |=(x=frac ^-(frac (mul:qq x [--1 2])))
::    +mid:  the midpoint of two rationals
++  mid  |=([a=frac b=frac] ^-(frac (half (add:qq a b))))
::    +rat-in:  the rational root lying in (lo, hi], if there is one
::
::  At most one can, wherever this is called: the caller has already
::  established that the range holds exactly one root.
++  rat-in
  |=  [rs=(list [r=frac m=@ud]) lo=frac hi=frac]
  ^-  (unit frac)
  ?~  rs  ~
  ?:  ?&(=(%lt (cmp:qq lo r.i.rs)) ?!(=(%gt (cmp:qq r.i.rs hi))))
    `r.i.rs
  $(rs t.rs)
::
+|  %public
::    +bound:  the Cauchy root bound
::
::  [p=zol] -> frac.  Every real root of p lies strictly inside (-B, B),
::  where B = 1 + max(|a_i|) / |a_n| over i < n.
::
::  Pinned as a VALUE, not an algorithm: SPEC R3 states every canonical
::  output relative to this bound, so a different bound would give a
::  different -- equally valid, but different -- isolation.
::
::  Crashes on the zero polynomial (SPEC R5).
++  bound
  |=  p=zol
  ^-  frac
  ?~  p  !!
  =/  an=@ud  (abs:si (rear p))
  =/  hi=@ud
    =/  cs=zol  p
    =/  k=@ud   0
    =/  n=@ud   (deg:zx p)
    =/  m=@ud   0
    |-  ^-  @ud
    ?~  cs  m
    ::  the leading coefficient is excluded: the bound is over i < n
    ?:  =(k n)  m
    $(cs t.cs, k +(k), m (max m (abs:si i.cs)))
  ::  1 + hi/an = (hi + an)/an, formed in one step so +new never sees a
  ::  non-canonical pair
  (new:qq (sun:si (add hi an)) an)
::    +deriv:  the formal derivative in Z[x]
::
::  [p=zol] -> zol.  The derivative of a constant is ~, the zero
::  polynomial, which is the right answer and not an edge case.
::
::  DUPLICATES +zderiv:pv, which is private to the frozen library and so
::  unreachable from a consumer.  Four lines against unfreezing %zx for
::  one arm; see SPEC-QUESTIONS R1.  No canonicalization is needed for a
::  nonconstant p: the leading term is n * a_n with both factors nonzero.
++  deriv
  |=  p=zol
  ^-  zol
  ?~  p  !!
  =/  ts=zol  t.p
  =/  k=@s    --1
  =|  out=zol
  |-  ^-  zol
  ?~  ts  (flop out)
  $(ts t.ts, k (sum:si k --1), out [(pro:si k i.ts) out])
::    +sign-at:  the sign of p(x) at a rational point
::
::  [p=zol x=frac] -> ord.  %eq exactly when x is a root, which is an
::  exact statement here and not a tolerance.  Reuses SPEC §6's $ord,
::  which is what that type is for.
::
::  Crashes on the zero polynomial (SPEC R5) -- its sign is not %eq
::  "everywhere", it is undefined as a root test.
++  sign-at
  |=  [p=zol x=frac]
  ^-  ord
  ?~  p  !!
  (cmp:qq (eval:qx (embed:qx p) x) zero:qq)
::    +is-squarefree:  does p have no repeated factor?
::
::  [p=zol] -> ?.  True iff gcd(p, p') is constant.  A nonzero constant
::  is squarefree; the zero polynomial crashes.
++  is-squarefree
  |=  p=zol
  ^-  ?
  ?~  p  !!
  =/  d=zol  (deriv p)
  ?~  d  %.y
  =(0 (deg:zx (gcd:zx p d)))
::    +sturm:  the Sturm chain of a squarefree polynomial
::
::  [p=zol] -> (list zol), the sequence p, p', -rem(p, p'), ... down to a
::  constant.  REQUIRES p SQUAREFREE, asserted: the chain's root count is
::  valid only there, and returning a silently wrong count would be worse
::  than crashing (SPEC R5).
::
::  SIGNS ARE THE WHOLE DIFFICULTY.  Racoon has no exact remainder over
::  Z, only the pseudo-remainder +pdiv:zx, whose identity is
::
::      lc(b)^e * a = q*b + r,     e = deg a - deg b + 1
::
::  so r is the true remainder scaled by lc(b)^e -- and that factor is
::  NEGATIVE when lc(b) < 0 and e is odd.  Sturm needs each term to be
::  -rem up to a strictly POSITIVE factor, so the sign of lc(b)^e has to
::  be undone rather than assumed away.  Getting this wrong does not
::  crash; it silently miscounts, which is why it is spelled out here.
::
::  Each term is then reduced to its primitive part.  +pp:zx carries the
::  input's sign (content is non-negative and content * pp = input), so
::  that is safe -- which is the only reason it can be used at all.
++  sturm
  |=  p=zol
  ^-  (list zol)
  ?~  p  !!
  ?>  (is-squarefree p)
  =/  d=zol  (deriv p)
  ?~  d  ~[p]
  =/  a=zol  p
  =/  b=zol  d
  =/  out=(list zol)  ~[d p]
  |-  ^-  (list zol)
  =/  r=zol  r:(pdiv:zx a b)
  ?~  r  (flop out)
  =/  e=@ud  +((sub (deg:zx a) (deg:zx b)))
  ::  lc(b)^e < 0 exactly when lc(b) < 0 and e is odd
  =/  down=?  ?&(!(syn:si (lc:zx b)) =(1 (mod e 2)))
  =/  nx=zol  (pp:zx ?:(down r (neg:zx r)))
  $(a b, b nx, out [nx out])
::    +count:  distinct real roots in the half-open interval (a, b]
::
::  [p=zol a=frac b=frac] -> @ud.  Sturm's theorem: the count is the drop
::  in sign variations of the chain from a to b.  Exact, and independent
::  of any subdivision -- which is what makes every arm here `free`.
::
::  Requires p squarefree, through +sturm.  Crashes unless a <= b (SPEC
::  R5).  An empty range is not a crash: the product is 0.
++  count
  |=  [p=zol a=frac b=frac]
  ^-  @ud
  ?>  !=(%gt (cmp:qq a b))
  =/  ch  (sturm p)
  =/  va=@ud  (vars (turn ch |=(q=zol (sign-at q a))))
  =/  vb=@ud  (vars (turn ch |=(q=zol (sign-at q b))))
  ::  variations never increase left to right, so this cannot underflow
  (sub va vb)
::    +sqpart:  the squarefree part, p / gcd(p, p')
::
::  [p=zol] -> zol with the same roots as p, each simple.  The division
::  is exact by construction, so +xdiv:zx is the right arm for it.  A
::  constant is already squarefree and comes back unchanged.
++  sqpart
  |=  p=zol
  ^-  zol
  ?~  p  !!
  =/  d=zol  (deriv p)
  ?~  d  p
  (xdiv:zx p (gcd:zx p d))
::    +lowz:  split off the factor x^k
::
::  [p=zol] -> [k=@ud q=zol] with p = x^k * q and q(0) != 0.  Little-endian
::  storage makes this a walk from the front.
::
::  +rational-roots needs it for two separate reasons: the rational root
::  theorem says nothing when a_0 = 0, since every integer divides zero,
::  and +divisors:zf crashes there anyway.
++  lowz
  |=  p=zol
  ^-  [k=@ud q=zol]
  =/  cs=zol  p
  =/  k=@ud   0
  |-  ^-  [k=@ud q=zol]
  ?~  cs  [k ~]
  ?.  =(--0 i.cs)  [k cs]
  $(cs t.cs, k +(k))
::    +rational-roots:  every exactly-rational root, with multiplicity
::
::  [p=zol] -> (list [r=frac m=@ud]), ascending by +cmp:qq, each
::  multiplicity at least 1.  Canonical: the root set is unique and the
::  order is pinned, so the arm is `free` like the rest.
::
::  By the RATIONAL ROOT THEOREM: a root a/b in lowest terms has a | a_0
::  and b | a_n, so the candidates are the divisors of the trailing and
::  leading coefficients, both signs.  That is why /lib/racoon-zfac had to
::  exist first -- the candidate set IS +divisors:zf, and there is no
::  cheaper way to enumerate it.
::
::  Multiplicities come from dividing each root out over Q as many times
::  as it goes, rather than from a separate squarefree decomposition.  A
::  repeated candidate is therefore self-cancelling: the second sighting
::  divides zero times and contributes nothing.
::
::  Crashes on the zero polynomial (SPEC R5).  A constant has no roots and
::  produces ~ without crashing, as does a polynomial with only
::  irrational ones.
++  rational-roots
  |=  p=zol
  ^-  (list [r=frac m=@ud])
  ?~  p  !!
  =/  lz  (lowz p)
  =/  q=zol   q.lz
  =/  k=@ud   k.lz
  ::  x^k contributes the root 0 with multiplicity k, and nothing else:
  ::  no other linear factor divides x^k
  =/  zed=(list [r=frac m=@ud])  ?:(=(0 k) ~ ~[[zero:qq k]])
  ?~  q  zed
  ?:  =(0 (deg:zx q))  zed
  =/  a0=@ud  (abs:si i.q)
  =/  an=@ud  (abs:si (lc:zx q))
  =/  ds0=(list @ud)  (divisors:zf a0)
  =/  dsn=(list @ud)  (divisors:zf an)
  =/  cands=(list frac)
    =/  as=(list @ud)  ds0
    =|  acc=(list frac)
    |-  ^-  (list frac)
    ?~  as  acc
    =/  inner=(list frac)
      =/  bs=(list @ud)  dsn
      =|  ac2=(list frac)
      |-  ^-  (list frac)
      ?~  bs  ac2
      =/  up=frac  (new:qq (sun:si i.as) i.bs)
      =/  dn=frac  (new:qq (dif:si --0 (sun:si i.as)) i.bs)
      $(bs t.bs, ac2 [up dn ac2])
    $(as t.as, acc (weld inner acc))
  =/  res=(list [r=frac m=@ud])
    =/  cs=(list frac)  cands
    =/  cur=qol         (embed:qx q)
    =|  acc=(list [r=frac m=@ud])
    |-  ^-  (list [r=frac m=@ud])
    ?~  cs  acc
    =/  step
      =/  c=qol  cur
      =/  m=@ud  0
      |-  ^-  [c=qol m=@ud]
      ?~  c  [c m]
      ?.  =(zero:qq (eval:qx c i.cs))  [c m]
      =/  lin=qol  ~[(neg:qq i.cs) one:qq]
      $(c q:(divmod:qx c lin), m +(m))
    ?:  =(0 m.step)  $(cs t.cs)
    $(cs t.cs, cur c.step, acc [[i.cs m.step] acc])
  %+  sort  (weld zed res)
  |=  [x=[r=frac m=@ud] y=[r=frac m=@ud]]
  ?!(=(%gt (cmp:qq r.x r.y)))
::    +subdiv:  the canonical isolating intervals of q inside (lo, hi]
::
::  [q=zol rs=(list [r=frac m=@ud]) lo=frac hi=frac] -> (list ivl), with q
::  SQUAREFREE and rs its rational roots.  Recurses on the binary
::  subdivision tree, stopping at the SHALLOWEST node holding exactly one
::  root -- which is what makes the product a function of q alone (SPEC
::  R3) and every arm here `free`.
::
::  THE HALF-OPEN CONVENTION IS WHY THIS IS EXACT.  (lo, mid] and
::  (mid, hi] partition (lo, hi] with no overlap and no gap, so a root can
::  neither be counted twice nor fall between the children -- including a
::  root that lands exactly on mid.  A closed convention would need a
::  special case there; this needs none.
::
::  A node whose one root is RATIONAL collapses to the degenerate
::  interval at that root, rather than being reported as a range around
::  it.  That is also what keeps the products pairwise disjoint: the
::  exact point replaces the node it sat in, so it cannot overlap a
::  sibling.
::
::  Terminates because q is squarefree: its roots are distinct, so any
::  two separate at some finite depth.
++  subdiv
  |=  [q=zol rs=(list [r=frac m=@ud]) lo=frac hi=frac]
  ^-  (list ivl)
  =/  c=@ud  (count q lo hi)
  ?:  =(0 c)  ~
  ?:  =(1 c)
    =/  hit  (rat-in rs lo hi)
    ?~  hit  ~[[lo hi]]
    ~[[u.hit u.hit]]
  =/  md=frac  (mid lo hi)
  ::  left child first, so the product comes out ascending with no sort
  (weld $(hi md) $(lo md))
::    +isolate:  a canonical isolating interval for every real root
::
::  [p=zol] -> (list ivl), ascending, pairwise disjoint, each holding
::  exactly one distinct real root of p.  A rational root appears as the
::  degenerate interval at its exact value, never as a range.
::
::  Never crashes on a nonzero p: a constant, and a polynomial with no
::  real roots, both produce ~.  Crashes on ~ (SPEC R5).
::
::  Runs on the SQUAREFREE PART, so a repeated factor yields one interval
::  and not several; +roots below recovers the multiplicities.
++  isolate
  |=  p=zol
  ^-  (list ivl)
  ?~  p  !!
  =/  q=zol  (sqpart p)
  ?~  q  ~
  ?:  =(0 (deg:zx q))  ~
  =/  rs  (rational-roots q)
  =/  b=frac  (bound q)
  ::  every root is strictly inside (-B, B), so the half-open end at B
  ::  cannot clip one
  (subdiv q rs (qneg b) b)
::    +refine:  narrow an isolating interval by bisection
::
::  [p=zol iv=ivl k=@ud] -> ivl, bisected k times, keeping the half that
::  holds the root.  Canonical given k, since the starting interval is
::  canonical and bisection is deterministic.
::
::  A degenerate interval is already exact and comes back unchanged --
::  there is nothing to narrow, and bisecting it would produce nonsense.
::
::  The width falls by exactly 2^k, so a caller wanting a given precision
::  computes k once rather than looping.  No floating point is involved
::  at any point, and none ever will be: the endpoints stay $frac.
++  refine
  |=  [p=zol iv=ivl k=@ud]
  ^-  ivl
  ?:  =(%eq (cmp:qq lo.iv hi.iv))  iv
  =/  q=zol    (sqpart p)
  =/  lo=frac  lo.iv
  =/  hi=frac  hi.iv
  =/  j=@ud    0
  |-  ^-  ivl
  ?:  =(j k)  [lo hi]
  =/  md=frac  (mid lo hi)
  ?:  =(1 (count q lo md))  $(j +(j), hi md)
  $(j +(j), lo md)
::    +mult-of:  the multiplicity of the root isolated by iv
++  mult-of
  |=  [fs=(list [p=zol m=@ud]) iv=ivl]
  ^-  @ud
  ::  the squarefree factors partition the distinct roots, so exactly one
  ::  of them holds this root; reaching the end is an invariant violation
  ?~  fs  !!
  =/  hit=?
    ?:  =(%eq (cmp:qq lo.iv hi.iv))
      =(%eq (sign-at p.i.fs lo.iv))
    =(1 (count p.i.fs lo.iv hi.iv))
  ?:  hit  m.i.fs
  $(fs t.fs)
::    +roots:  every real root, isolated, with its multiplicity
::
::  [p=zol] -> (list rrt), ascending.  Isolation comes from +isolate on
::  the squarefree part, so the intervals are canonical and disjoint;
::  multiplicities come from Yun's decomposition in +sqfree:zx, whose
::  factors partition the distinct roots.
::
::  Isolating on the squarefree part rather than per factor is what keeps
::  the intervals disjoint: separate factors would be subdivided from
::  different Cauchy bounds, on different trees, and their products could
::  overlap.
++  roots
  |=  p=zol
  ^-  (list rrt)
  ?~  p  !!
  =/  sf  (sqfree:zx p)
  %+  turn  (isolate p)
  |=  iv=ivl
  ^-  rrt
  [iv (mult-of fs.sf iv)]
::    +nroots:  the number of distinct real roots
::
::  [p=zol] -> @ud, over all of R.  Counted on (-B, B] with B the Cauchy
::  bound, which contains every root strictly -- so the half-open end
::  cannot clip one.
::
::  Counts DISTINCT roots: unlike +count this accepts ANY nonzero p and
::  takes the squarefree part itself, so a repeated factor contributes
::  once.  A nonzero constant has none.
::
::  The bound is taken on the squarefree part, not the input.  Both
::  bound the same root set, and the squarefree part's is never larger.
++  nroots
  |=  p=zol
  ^-  @ud
  ?~  p  !!
  =/  q=zol   (sqpart p)
  =/  b=frac  (bound q)
  (count q (qneg b) b)
--
