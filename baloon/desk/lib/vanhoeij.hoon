  ::  /lib/vanhoeij
::::  Lattice reduction, toward van Hoeij recombination -- SPEC §V
::
::  SPEC §9 records the cost cliff: +factor:zx recombines Hensel-lifted
::  modular factors by ZASSENHAUS, enumerating subsets, which is
::  exponential in their number.  SD_4 and beyond are out of scope
::  because of it, and §A8 showed the same wall stops algebraic
::  arithmetic at degree 4.  Van Hoeij replaces that step with a lattice
::  problem; this is phase V0, the lattice reduction it needs.
::
::  A CONSUMER OF BOTH LIBRARIES, which is why it lives on the Baloon
::  side (escalation R4).  LLL operates on integer lattice bases -- that
::  is exactly $zmat -- and Baloon Milestone C already supplies +det,
::  +mul, +rank, and the Hermite form over Z.  Racoon cannot import
::  Baloon, the dependency runs the other way, so putting this in Racoon
::  would mean duplicating all of it.
::
::  +lll IS PINNED, not free -- the first pinned arm outside Racoon's
::  five.  A lattice has many LLL-reduced bases, so the output is
::  underdetermined by the specification and a jet cannot be allowed to
::  pick a different one.  The procedure is the contract, exactly as for
::  +egcd:nz.
::
::  EXACT RATIONALS THROUGHOUT.  The classic LLL failure mode is a
::  Gram-Schmidt computed in floating point drifting until the Lovasz
::  test flips the wrong way.  Here that cannot happen: every quantity is
::  a $frac and stays one.
::
/-  *baloon, *racoon
/+  baloon, racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  mx  mx:racoon
=/  zm  zm:baloon
|%
+|  %private
::    +hlf:  one half, as a rational
++  hlf   ^-(frac [--1 2])
::    +del:  the LLL parameter, pinned at 3/4 (SPEC V2)
++  del   ^-(frac [--3 4])
::    +zq:  embed an integer vector in Q
++  zq  |=(v=zvec ^-(qvec (turn v |=(x=@s ^-(frac [x 1])))))
::    +qdot:  inner product of two rational vectors
++  qdot
  |=  [a=qvec b=qvec]
  ^-  frac
  =/  acc=frac  zero:qq
  |-  ^-  frac
  ?~  a  acc
  ?~  b  acc
  $(a t.a, b t.b, acc (add:qq acc (mul:qq i.a i.b)))
::    +qscale:  multiply a rational vector by a scalar
++  qscale
  |=  [v=qvec c=frac]
  ^-  qvec
  (turn v |=(x=frac (mul:qq c x)))
::    +qsub:  elementwise difference of two rational vectors
++  qsub
  |=  [a=qvec b=qvec]
  ^-  qvec
  ?~  a  ~
  ?~  b  ~
  [(sub:qq i.a i.b) $(a t.a, b t.b)]
::    +zaxpy:  the integer combination a - c*b
++  zaxpy
  |=  [a=zvec b=zvec c=@s]
  ^-  zvec
  ?~  a  ~
  ?~  b  ~
  [(dif:si i.a (pro:si c i.b)) $(a t.a, b t.b)]
::    +zround:  the nearest integer to a rational, ties AWAY FROM ZERO
::
::  Pinned (SPEC V2).  Ties are rare but they do occur -- mu of exactly
::  1/2 is the boundary of size-reduction -- and a rule that rounded
::  toward even would give a different, equally reduced, basis.
++  zround
  |=  f=frac
  ^-  @s
  ::  |f| + 1/2, floored, then signed
  =/  a=frac  (add:qq [(sun:si (abs:si p.f)) q.f] hlf)
  =/  n=@ud   (div (abs:si p.a) q.a)
  ?:  (syn:si p.f)  (sun:si n)
  (dif:si --0 (sun:si n))
::    +qabs:  absolute value of a rational
++  qabs  |=(f=frac ^-(frac ?:((syn:si p.f) f (neg:qq f))))
::    +nth:  the i-th element of a list of rational vectors
++  nth
  |=  [vs=(list qvec) i=@ud]
  ^-  qvec
  ?~  vs  !!
  ?:  =(0 i)  i.vs
  $(vs t.vs, i (dec i))
::    +znth:  the i-th row of an integer matrix
++  znth
  |=  [m=zmat i=@ud]
  ^-  zvec
  ?~  m  !!
  ?:  =(0 i)  i.m
  $(m t.m, i (dec i))
::    +zput:  replace the i-th row of an integer matrix
++  zput
  |=  [m=zmat i=@ud r=zvec]
  ^-  zmat
  ?~  m  !!
  ?:  =(0 i)  [r t.m]
  [i.m $(m t.m, i (dec i))]
::    +zswap:  exchange two rows
++  zswap
  |=  [m=zmat i=@ud j=@ud]
  ^-  zmat
  ?:  =(i j)  m
  (zput (zput m i (znth m j)) j (znth m i))
::
+|  %gso
::    +gso:  exact rational Gram-Schmidt
::
::  [b=zmat] -> [bs=(list qvec) mu=(list qvec)] with
::
::      b*_i = b_i - sum_{j<i} mu_ij b*_j,   mu_ij = <b_i, b*_j>/<b*_j, b*_j>
::
::  .mu is lower triangular with a 1 on the diagonal and zeros above, so
::  every row has full length and indexing needs no special cases.
::
::  Computed from scratch, and +lll calls it ONCE per outer iteration
::  rather than once per size-reduction step, updating mu row k in place
::  across the inner loop.  That is where the cost is: the from-scratch
::  version inside the loop made +lll ~n times slower, which at the
::  dimensions SPEC V1 needs is the difference between minutes and hours
::  (see /gen/baloon-lll-bench).  It changes NOTHING about the output:
::  exact rational GSO and an incrementally updated one are mathematically
::  equal, which is why SPEC V2 pins the reduction sequence but not this
::  computation.
::
::  Crashes on a rank-deficient basis, through a zero <b*_j, b*_j>; +lll
::  asserts full rank first so callers see the assertion instead.
++  gso
  |=  b=zmat
  ^-  [bs=(list qvec) mu=(list qvec)]
  =/  n=@ud  (lent b)
  =/  i=@ud  0
  =|  bs=(list qvec)
  =|  ms=(list qvec)
  |-  ^-  [bs=(list qvec) mu=(list qvec)]
  ?:  =(i n)  [(flop bs) (flop ms)]
  =/  bi=qvec  (zq (znth b i))
  ::  subtract the projection onto each earlier b*
  =/  done=(list qvec)  (flop bs)
  =/  j=@ud     0
  =/  v=qvec    bi
  =|  row=qvec
  =/  step
    ::  the cast is what gives the pair its faces; [v (flop row)] alone
    ::  would leave the tail unnamed and row.step would not resolve
    |-  ^-  [v=qvec row=qvec]
    ?:  =(j i)  [v (flop row)]
    =/  bj=qvec   (nth done j)
    =/  d=frac    (qdot bj bj)
    =/  m=frac    (div:qq (qdot bi bj) d)
    $(j +(j), v (qsub v (qscale bj m)), row [m row])
  ::  pad the mu row out to n: 1 on the diagonal, 0 above it
  =/  full=qvec
    %+  weld  row.step
    [one:qq (reap (sub n +(i)) zero:qq)]
  $(i +(i), bs [v.step bs], ms [full ms])
::    +qat:  the j-th element of a rational vector
++  qat
  |=  [v=qvec j=@ud]
  ^-  frac
  =/  r=qvec  v
  =/  k=@ud   j
  |-  ^-  frac
  ?~  r  !!
  ?:  =(0 k)  i.r
  $(r t.r, k (dec k))
::    +mu-at:  the Gram-Schmidt coefficient mu_ij
++  mu-at
  |=  [mu=(list qvec) i=@ud j=@ud]
  ^-  frac
  (qat (nth mu i) j)
::    +nrm2:  the squared norm of the i-th Gram-Schmidt vector
++  nrm2
  |=  [bs=(list qvec) i=@ud]
  ^-  frac
  =/  v=qvec  (nth bs i)
  (qdot v v)
::
+|  %recombination
::    +cand:  the candidate factor a subset of modular factors proposes
::
::  [sel=(list mol) rem=zol md=@ud] -> (unit zol).  Forms the product of
::  .sel modulo .md, scales it so the lift carries lc(rem), symmetric-lifts
::  into Z, takes the primitive part, normalizes the sign, and returns it
::  ONLY if it actually divides .rem.
::
::  THIS IS THE CONFIRMATION SPEC V4 RESTS ON.  Whatever proposed the
::  subset -- a lattice vector or brute enumeration -- it is a factor only
::  if the division is exact.  Nothing downstream trusts the proposer,
::  which is what lets the lattice be a heuristic and +factor still be
::  canonical.  Lifted verbatim out of +firr:zx so both callers confirm
::  identically.
++  cand
  |=  [sel=(list mol) rem=zol md=@ud]
  ^-  (unit zol)
  =/  dm  ~(. mx md)
  =/  pr=mol  (mprod:zx sel md)
  =/  lr=@ud  (mod (abs:si (lc:zx rem)) md)
  =/  sc=mol
    ?:  (syn:si (lc:zx rem))  (scale:dm pr lr)
    (scale:dm pr (cneg:dm lr))
  =/  c0=zol  (lift:zx sc md)
  ?~  c0  ~
  =/  c1=zol  (pp:zx c0)
  =/  cd=zol
    ?:  (syn:si (lc:zx c1))  c1
    (neg:zx c1)
  ?.  ?&  (gth (deg:zx cd) 0)
          (lte (deg:zx cd) (deg:zx rem))
          =(~ r:(pdiv:zx rem cd))
      ==
    ~
  `cd
::    +psums:  the first m power sums of a monic polynomial's roots
::
::  [g=mol m=@ud md=@ud] -> (list @ud), [s_1 ... s_m], each in [0, md).
::  .g must be MONIC.  Nothing here checks that; the identities are simply
::  false without it.
::
::  Newton's identities.  For g = x^d + c_(d-1) x^(d-1) + ... + c_0,
::
::      s_k = -( k*c_(d-k) + sum_(i=1..k-1) c_(d-i) * s_(k-i) )    k <= d
::      s_k = -(             sum_(i=1..d)   c_(d-i) * s_(k-i) )    k >  d
::
::  NO DIVISION ANYWHERE, and that is the point.  The textbook form solves
::  for s_k by dividing by k, which is exactly wrong over Z/p^a: it is not
::  a field, and k is a non-unit whenever p divides k -- so the textbook
::  form fails for precisely the k that matter most.  The monic form never
::  divides.
::
::  ADDITIVE OVER PRODUCTS, since the roots of g*h are the roots of g
::  together with the roots of h.  That additivity is the whole reason the
::  recombination condition is LINEAR in the subset indicator, and hence
::  why a lattice can find it at all (SPEC V3).
++  psums
  |=  [g=mol m=@ud md=@ud]
  ^-  (list @ud)
  =/  dm  ~(. mx md)
  =/  d=@ud  (deg:dm g)
  =/  k=@ud  1
  =|  ps=(list @ud)
  |-  ^-  (list @ud)
  ?:  (gth k m)  (flop ps)
  ::  s_(k-i) sits at index i-1 of .ps, which carries s_(k-1) at its head
  =/  lim=@ud  (min (dec k) d)
  =/  sum=@ud
    =/  i=@ud  1
    =/  s=@ud  0
    |-  ^-  @ud
    ?:  (gth i lim)  s
    =/  ci=@ud  (snag (sub d i) `(list @ud)`g)
    =/  sk=@ud  (snag (dec i) `(list @ud)`ps)
    $(i +(i), s (cadd:dm s (cmul:dm ci sk)))
  =/  lin=@ud
    ?:  (gth k d)  0
    (cmul:dm (mod k md) (snag (sub d k) `(list @ud)`g))
  $(k +(k), ps [(cneg:dm (cadd:dm sum lin)) ps])
::    +drop:  remove a subset's indices from the remaining index set
++  drop
  |=  [idx=(list @ud) s=(list @ud)]
  ^-  (list @ud)
  (skip idx |=(j=@ud (lien s |=(k=@ud =(k j)))))
::    +zass:  Zassenhaus recombination over a remaining index set
::
::  [rem=zol idx=(list @ud) gs=(list mol) md=@ud acc=(list zol)] ->
::  (list zol).  Subsets by ascending cardinality, stopping once
::  2*card > |idx| because the complement of every larger subset has
::  already been tried.  The enumeration order is +combos:zx, pinned by
::  SPEC S9.
::
::  Ported from +firr:zx unchanged.  SPEC V4 makes this the MANDATORY
::  fallback: the lattice pass may leave anything behind, up to and
::  including everything, and this still has to finish the job.  When the
::  lattice proposes nothing, +factor degenerates to exactly +firr:zx --
::  which is what makes SPEC V7.3's "the two must agree" hold by
::  construction rather than by luck.
++  zass
  |=  [rem=zol idx=(list @ud) gs=(list mol) md=@ud acc=(list zol)]
  ^-  (list zol)
  =/  card=@ud  1
  |-  ^-  (list zol)
  ?:  (gth (mul 2 card) (lent idx))
    ?:  (gth (deg:zx rem) 0)  (flop [rem acc])
    (flop acc)
  =/  hit
    =/  cs=(list (list @ud))  (combos:zx card idx)
    |-  ^-  (unit [s=(list @ud) f=zol])
    ?~  cs  ~
    =/  sel=(list mol)  (turn i.cs |=(j=@ud (snag j gs)))
    =/  cd  (cand sel rem md)
    ?~  cd  $(cs t.cs)
    `[i.cs u.cd]
  ?~  hit  $(card +(card))
  %=  $
    idx  (drop idx s.u.hit)
    rem  (xdiv:zx rem f.u.hit)
    acc  [f.u.hit acc]
  ==
::
+|  %public
::    +reduced:  is this basis LLL-reduced at delta = 3/4?
::
::  Both halves of the definition, checked exactly: size-reduction and
::  the Lovasz condition.  Exposed because it is the specification of
::  +lll -- SPEC V7 verifies the output against this rather than against
::  another implementation, since an LLL-reduced basis is not unique and
::  matching some other program's choice is neither necessary nor
::  sufficient.
++  reduced
  |=  b=zmat
  ^-  ?
  =/  n=@ud  (lent b)
  ?:  (lth n 2)  %.y
  =/  g   (gso b)
  =/  i=@ud  1
  |-  ^-  ?
  ?:  =(i n)  %.y
  ::  size-reduced against every earlier row
  =/  small=?
    =/  j=@ud  0
    |-  ^-  ?
    ?:  =(j i)  %.y
    ?:  =(%gt (cmp:qq (qabs (mu-at mu.g i j)) hlf))  %.n
    $(j +(j))
  ?.  small  %.n
  ::  Lovasz at this index
  =/  m=frac  (mu-at mu.g i (dec i))
  =/  rhs=frac
    (mul:qq (sub:qq del (mul:qq m m)) (nrm2 bs.g (dec i)))
  ?:  =(%lt (cmp:qq (nrm2 bs.g i) rhs))  %.n
  $(i +(i))
::    +lll:  an LLL-reduced basis of the same lattice
::
::  [b=zmat] -> zmat.  PINNED (SPEC V2): delta = 3/4, classic
::  Lenstra-Lenstra-Lovasz, size-reduction against rows k-1 down to 0 in
::  descending order, ties rounded away from zero, and k reset to
::  max(k-1, 1) on a swap.
::
::  Requires the rows to be linearly independent, asserted through
::  +rank:zm -- a dependent basis makes some <b*_j, b*_j> zero and the
::  Gram-Schmidt divide by it.  Crashing on the assertion says which
::  precondition failed; crashing inside +gso would not.
::
::  Terminates by the standard argument: the integer quantity
::  prod ||b*_i||^(2(n-i)) strictly decreases at every swap and is
::  bounded below.
++  lll
  ~/  %lll
  |=  b=zmat
  ^-  zmat
  ?~  b  !!
  =/  n=@ud  (lent b)
  ?>  =(n (rank:zm b))
  ?:  (lth n 2)  b
  =/  cur=zmat  b
  =/  k=@ud     1
  |-  ^-  zmat
  ?:  =(k n)  cur
  ::  ONE Gram-Schmidt per outer iteration, not one per size-reduction
  ::  step.  Everything the rest of this iteration reads survives the
  ::  reductions below unchanged:
  ::
  ::    b*_0 .. b*_k   b_k -= q*b_j with j < k subtracts a vector lying
  ::                   in span(b_0 .. b_k-1), which is precisely what the
  ::                   projection already removes, so the orthogonal part
  ::                   is untouched -- and b_0 .. b_k-1 never move at all
  ::    mu_i for i < k does not depend on row k
  ::
  ::  Only mu row k moves, and it is threaded through the loop instead.
  ::  Rows above k do change, and are not read before the next +gso.
  =/  g  (gso cur)
  ::  size-reduce row k against k-1 .. 0, descending
  =/  rk
    =/  j=@ud     (dec k)
    =/  acc=zmat  cur
    =/  mk=qvec   (nth mu.g k)
    |-  ^-  [acc=zmat mk=qvec]
    =/  q=@s    (zround (qat mk j))
    =/  nx=zmat
      ?:  =(--0 q)  acc
      (zput acc k (zaxpy (znth acc k) (znth acc j) q))
    ::  b_k -= q*b_j sends mu_ki to mu_ki - q*mu_ji for every i.  mu_ji
    ::  is 0 above the diagonal and 1 on it, so the plain vector update
    ::  is exact at i=j and a no-op for i>j -- in particular mu_kk stays
    ::  1, as the padding in +gso requires.
    =/  nm=qvec
      ?:  =(--0 q)  mk
      (qsub mk (qscale (nth mu.g j) [q 1]))
    ?:  =(0 j)  [nx nm]
    $(j (dec j), acc nx, mk nm)
  ::  Lovasz, on the size-reduced basis
  =/  m=frac  (qat mk.rk (dec k))
  =/  rhs=frac
    (mul:qq (sub:qq del (mul:qq m m)) (nrm2 bs.g (dec k)))
  ?:  ?!(=(%lt (cmp:qq (nrm2 bs.g k) rhs)))
    $(cur acc.rk, k +(k))
  $(cur (zswap acc.rk k (dec k)), k ?:((gth k 1) (dec k) 1))
::    +factor:  the irreducible factors over Z of a squarefree f
::
::  [f=zol] -> (list zol), each primitive irreducible with positive lc.
::  The same product +firr:zx returns, and SPEC V7.3 requires the two to
::  agree on every input -- +factor:zx is the oracle here, being already
::  verified against SymPy over the Milestone A corpus.
::
::  Crashes on ~ and on non-squarefree .f (SPEC V5).  Recombination is
::  defined on DISTINCT modular factors, so a repeated factor is not
::  merely unsupported here, it is meaningless: the subset-to-factor
::  correspondence the whole method rests on stops being injective.
::
::  The caller guarantees .f primitive with positive lc; that is asserted
::  too, since +sqfree:zx has to run for the squarefree check anyway and
::  its decomposition answers both questions at once.
::
::  FREE, not pinned, even though it calls the pinned +lll.  Every factor
::  is confirmed by trial division in +cand, so which reduced basis the
::  lattice produced cannot reach the answer -- see SPEC V2's last line.
++  factor
  |=  f=zol
  ^-  (list zol)
  ?~  f  !!
  =/  sq=zfac  (sqfree:zx f)
  ?~  fs.sq  !!
  ?>  ?&(=(~ t.fs.sq) =(1 m.i.fs.sq) =(f p.i.fs.sq))
  =/  hd  (hdata:zx f)
  ::  ~ means the modular data already proved f irreducible
  ?~  hd  ~[f]
  =/  gs=(list mol)  gs.u.hd
  =/  md=@ud         md.u.hd
  (zass f (gulf 0 (dec (lent gs))) gs md ~)
--
