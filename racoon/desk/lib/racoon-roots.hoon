  ::  /lib/racoon-roots
::::  Real-root isolation over Z[x] -- SPEC Milestone C, phase R
::
::  Racoon is named for real algebraic numbers and did not produce any.
::  Phases R0 and R1: an EXACT count of the distinct real roots in any
::  rational interval, and the exact rational roots themselves.  Phase R2
::  -- isolation and refinement of the irrational ones -- is bookkeeping
::  on top of a count that is already right.
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
