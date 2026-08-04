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
::  +lll NO LONGER CALLS THIS.  It runs on the integral data of the
::  %integral chapter instead, which carries the same information without
::  paying a gcd per operation.  This arm survives because +reduced is
::  written on it, and +reduced is the SPECIFICATION of +lll (SPEC V7.1)
::  -- checking the output against an independent formulation is worth
::  more than sharing code with it.
::
::  The history is worth keeping, since each step was a factor of n and
::  none of it changed the output: called inside the size-reduction loop,
::  then once per outer iteration, then maintained incrementally, then
::  replaced by integers.  Dimension 9 went 315 s -> 52 s -> 3.4 s ->
::  0.135 s.  SPEC V2 pins the reduction sequence but not this
::  computation, which is what licensed every one of those.
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
+|  %integral
::  INTEGER-PRESERVING LLL (de Weger; Cohen Alg. 2.6.3/2.6.7).
::
::  The rational Gram-Schmidt above is exact but every operation on a
::  $frac pays a gcd to restore lowest terms, on operands hundreds of
::  bits wide.  This chapter carries the same information in integers and
::  never divides inexactly, so the gcd traffic is gone STRUCTURALLY
::  rather than merely reduced.
::
::  The change of variables, with d_0 = 1:
::
::      d_i          = det of the Gram matrix of b_0 .. b_(i-1)
::                   = prod_(j<i) ||b*_j||^2          -- so all d_i > 0
::      ||b*_i||^2   = d_(i+1) / d_i
::      lam_ij       = d_(j+1) * mu_ij                -- integral, by Cramer
::
::  Every quantity +lll needs is then a ratio of these, and every test it
::  makes clears its denominators.  SPEC V2 pins the reduction SEQUENCE
::  but explicitly not the method of computing the Gram-Schmidt data, so
::  this is licensed -- and the output must come out bit-identical, which
::  is what /gen/lllfp checks.
::
::    +zat:  the i-th element of an integer vector
++  zat
  |=  [v=zvec i=@ud]
  ^-  @s
  ?~  v  !!
  ?:  =(0 i)  i.v
  $(v t.v, i (dec i))
::    +zeput:  replace the i-th element of an integer vector
++  zeput
  |=  [v=zvec i=@ud x=@s]
  ^-  zvec
  ?~  v  !!
  ?:  =(0 i)  [x t.v]
  [i.v $(v t.v, i (dec i))]
::    +idot:  inner product of two integer vectors
++  idot
  |=  [a=zvec b=zvec]
  ^-  @s
  =/  acc=@s  --0
  |-  ^-  @s
  ?~  a  acc
  ?~  b  acc
  $(a t.a, b t.b, acc (sum:si acc (pro:si i.a i.b)))
::    +ired:  the fraction-free reduction behind the integral Gram step
::
::  Folds l = 0 .. j-1 into u by
::
::      u <- (d_(l+1) * u - lam_il * lam_jl) / d_l
::
::  Every division is EXACT -- this is Bareiss elimination, where the
::  divisor is the previous pivot and divides the numerator identically.
::  +fra:si truncates, so an inexact step here would be silent; the
::  fingerprint is what would catch it.
++  ired
  |=  [u=@s li=zvec lj=zvec d=zvec j=@ud]
  ^-  @s
  =/  l=@ud   0
  =/  acc=@s  u
  |-  ^-  @s
  ?:  =(l j)  acc
  %=  $
    l  +(l)
    acc
      %+  fra:si
        %+  dif:si
          (pro:si (zat d +(l)) acc)
        (pro:si (zat li l) (zat lj l))
      (zat d l)
  ==
::    +igso:  the integral Gram-Schmidt data of a basis
::
::  [b=zmat] -> [d=zvec lam=zmat], with .d holding d_0 .. d_n (so n+1
::  entries, d_0 = 1) and .lam lower triangular, n by n.  Entries on and
::  above the diagonal of .lam are never read.
++  igso
  |=  b=zmat
  ^-  [d=zvec lam=zmat]
  =/  n=@ud     (lent b)
  =/  d=zvec    [--1 `zvec`(reap n --0)]
  =/  lam=zmat  (reap n `zvec`(reap n --0))
  =/  i=@ud     0
  |-  ^-  [d=zvec lam=zmat]
  ?:  =(i n)  [d lam]
  =/  bi=zvec  (znth b i)
  =/  st
    =/  j=@ud    0
    =/  dd=zvec  d
    =/  ll=zmat  lam
    |-  ^-  [d=zvec lam=zmat]
    ?:  (gth j i)  [dd ll]
    =/  u=@s  (ired (idot bi (znth b j)) (znth ll i) (znth ll j) dd j)
    ?:  (lth j i)
      $(j +(j), ll (zput ll i (zeput (znth ll i) j u)))
    $(j +(j), dd (zeput dd +(i) u))
  $(i +(i), d d.st, lam lam.st)
::    +iround:  +zround of a/d, without ever forming the rational
::
::  .d is a d_i and so is strictly positive, which is what makes the sign
::  of the quotient the sign of .a.  Ties go AWAY FROM ZERO, matching the
::  pinned rounding exactly: floor((2|a| + d) / 2d) is |a/d| + 1/2
::  floored.
++  iround
  |=  [a=@s d=@s]
  ^-  @s
  =/  na=@ud  (abs:si a)
  =/  nd=@ud  (abs:si d)
  =/  q=@ud   (div (add (mul 2 na) nd) (mul 2 nd))
  ?:  (syn:si a)  (sun:si q)
  (dif:si --0 (sun:si q))
::    +iswap:  the integral data after exchanging rows k and k-1
::
::  Writing j = k-1 and lam = lam_kj, the new d_k is
::
::      D = (d_(k-1) * d_(k+1) + lam^2) / d_k
::
::  and no other d moves: for i <= k-1 the first i rows are untouched,
::  and for i >= k+1 they are the same SET reordered, whose Gram
::  determinant is invariant.
::
::  lam_kj itself is UNCHANGED -- the new mu_kj is lam/D and the new
::  scale is D, so the product comes back to lam.  Rows j and k trade
::  their entries below column j, and every row below k updates as
::
::      t          = lam_ik                    (old)
::      lam'_ik    = (d_(k+1) * lam_ij - lam * t) / d_k
::      lam'_ij    = (D * t + lam * lam'_ik) / d_(k+1)     -- the NEW ik
::
::  Derived by substituting the change of variables into the rational
::  swap, which was itself derived twice.  A wrong sign here does not
::  crash; it silently returns a different reduced basis, and +lll is
::  PINNED.
++  iswap
  |=  [d=zvec lam=zmat k=@ud n=@ud]
  ^-  [d=zvec lam=zmat]
  =/  j=@ud    (dec k)
  =/  lk=@s    (zat (znth lam k) j)
  =/  dj=@s    (zat d j)
  =/  dk=@s    (zat d k)
  =/  dk1=@s   (zat d +(k))
  =/  bb=@s
    %+  fra:si
      (sum:si (pro:si dj dk1) (pro:si lk lk))
    dk
  ::  rows j and k trade their entries in the columns below j
  =/  l0=zmat
    =/  c=@ud    0
    =/  rj=zvec  (znth lam j)
    =/  rk=zvec  (znth lam k)
    |-  ^-  zmat
    ?:  =(c j)  (zput (zput lam j rj) k rk)
    =/  x=@s  (zat rj c)
    =/  y=@s  (zat rk c)
    $(c +(c), rj (zeput rj c y), rk (zeput rk c x))
  ::  every row below k sees both columns move
  =/  l1=zmat
    =/  i=@ud    +(k)
    =/  ll=zmat  l0
    |-  ^-  zmat
    ?:  (gte i n)  ll
    =/  ri=zvec  (znth ll i)
    =/  t=@s     (zat ri k)
    =/  nik=@s
      %+  fra:si
        (dif:si (pro:si dk1 (zat ri j)) (pro:si lk t))
      dk
    =/  nij=@s
      %+  fra:si
        (sum:si (pro:si bb t) (pro:si lk nik))
      dk1
    $(i +(i), ll (zput ll i (zeput (zeput ri k nik) j nij)))
  [(zeput d k bb) l1]
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
::    +kroot:  the least b with b^k * d >= v
::
::  Doubling to bracket, then bisection.  Integer throughout; used only
::  by +rbound, where an over-estimate is safe and an under-estimate is
::  not, so this rounds up.
++  kroot
  |=  [v=@ud d=@ud k=@ud]
  ^-  @ud
  ?:  =(0 v)  0
  =/  top=@ud
    =/  hi=@ud  1
    |-  ^-  @ud
    ?:  (gte (mul (pow hi k) d) v)  hi
    $(hi (mul 2 hi))
  ?:  =(1 top)  1
  =/  lo=@ud  (div top 2)
  =/  hi=@ud  top
  |-  ^-  @ud
  ?:  =(+(lo) hi)  hi
  =/  mid=@ud  (div (add lo hi) 2)
  ?:  (gte (mul (pow mid k) d) v)  $(hi mid)
  $(lo mid)
::    +rbound:  a bound on the modulus of every complex root of f
::
::  [f=zol] -> @ud.  Fujiwara's bound,
::
::      |z| <= 2 * max_k ( |a_(n-k)| / |a_n| )^(1/k)
::
::  NOT the Cauchy bound 1 + max|a_i|/|a_n| that +bound:racoon-roots
::  uses.  Cauchy is useless here: SD_5 has eighteen-digit coefficients
::  and leading coefficient 1, so it returns ~1e18 where the true bound
::  is about 11.  The trace bound is n*B^m, so an exponentially loose B
::  makes the lattice unusable rather than merely slow.
++  rbound
  |=  f=zol
  ^-  @ud
  =/  n=@ud  (deg:zx f)
  ?:  =(0 n)  1
  =/  an=@ud    (abs:si (lc:zx f))
  =/  k=@ud     1
  =/  best=@ud  0
  |-  ^-  @ud
  ?:  (gth k n)  (max 1 (mul 2 best))
  =/  ak=@ud  (abs:si (snag (sub n k) `(list @s)`f))
  $(k +(k), best (max best (kroot ak an k)))
::    +spike:  a length-n integer vector holding v at index i, else 0
++  spike
  |=  [i=@ud n=@ud v=@s]
  ^-  zvec
  =/  k=@ud  0
  =|  out=zvec
  |-  ^-  zvec
  ?:  =(k n)  (flop out)
  $(k +(k), out [?:(=(k i) v --0) out])
::    +jmax:  the largest index in a list of power-sum indices
++  jmax
  |=  js=(list @ud)
  ^-  @ud
  =/  m=@ud  0
  |-  ^-  @ud
  ?~  js  m
  $(js t.js, m (max m i.js))
::    +lat:  the van Hoeij knapsack lattice (SPEC V3)
::
::  [gs md cc m] -> zmat of dimension r+m,
::
::      [ cc*I_r       T     ]        T_ij = s_j(g_i)
::      [   0      p^a * I_m ]
::
::  A lattice vector is [cc*v | u] with u_j = sum_i v_i s_j(g_i) mod p^a.
::  For a TRUE subset the power sums add to those of a genuine integer
::  factor, so u is small; for any other v it is a residue modulo p^a and
::  so is enormous.  That gap is what LLL finds.
::
::  Square and block triangular with nonzero diagonal, hence full rank,
::  so +lll's rank assertion cannot fire.
++  lat
  |=  [gs=(list mol) md=@ud cc=@ud js=(list @ud)]
  ^-  zmat
  =/  r=@ud  (lent gs)
  =/  m=@ud  (lent js)
  =/  hi=@ud  (jmax js)
  =/  top=zmat
    =/  i=@ud  0
    =|  out=zmat
    |-  ^-  zmat
    ?:  =(i r)  (flop out)
    =/  ps=(list @ud)  (psums (snag i `(list mol)`gs) hi md)
    =/  sel=(list @ud)
      (turn js |=(j=@ud ^-(@ud (snag (dec j) `(list @ud)`ps))))
    =/  row=zvec
      %+  weld  (spike i r (sun:si cc))
      `zvec`(turn sel |=(x=@ud ^-(@s (sun:si x))))
    $(i +(i), out [row out])
  =/  bot=zmat
    =/  j=@ud  0
    =|  out=zmat
    |-  ^-  zmat
    ?:  =(j m)  (flop out)
    =/  row=zvec  (weld `zvec`(reap r --0) (spike j m (sun:si md)))
    $(j +(j), out [row out])
  (weld top bot)
::    +extract:  the 0-1 subsets a reduced basis proposes
::
::  A row whose first r coordinates are all 0 or all +-cc, with a single
::  sign, is a subset indicator scaled by cc -- possibly negated, since a
::  basis is only defined up to sign.
::
::  BOTH HALVES MUST BE CHECKED.  The trailing trace coordinates have to
::  be small as well, because that is the actual condition: v names a
::  true factor when its power sums add up to a genuine integer trace
::  rather than to a residue modulo p^a.  Testing only the indicator
::  shape admits the untouched basis rows themselves -- [cc*e_i | s_j],
::  which look exactly like singletons and mean nothing.  That is not a
::  harmless surplus: on an IRREDUCIBLE f the only true subset is the
::  whole set, and those fake singletons crowded it out entirely, so
::  SD_5's enumeration was not avoided at all.
++  extract
  |=  [b=zmat r=@ud cc=@ud n=@ud rb=@ud js=(list @ud)]
  ^-  (list (list @ud))
  =/  cs=@s  (sun:si cc)
  =/  nc=@s  (dif:si --0 cs)
  %-  zing
  %+  turn  b
  |=  v=zvec
  ^-  (list (list @ud))
  ::  column k carries s_(js_k), bounded by n * B^(js_k) -- PER COLUMN,
  ::  since one bound for all of them would be the largest and so nearly
  ::  vacuous at the smallest index
  ?.  =/  ts=(list @s)   (slag r `(list @s)`v)
      =/  ks=(list @ud)  js
      |-  ^-  ?
      ?~  ts  %.y
      ?~  ks  %.y
      ?.  (lte (abs:si i.ts) (mul n (pow rb i.ks)))  %.n
      $(ts t.ts, ks t.ks)
    ~
  =/  i=@ud  0
  =|  pos=(list @ud)
  =|  neg=(list @ud)
  |-  ^-  (list (list @ud))
  ?:  =(i r)
    =/  hp=?  ?!(=(~ pos))
    =/  hn=?  ?!(=(~ neg))
    ?:  ?&(hp ?!(hn))  ~[(flop pos)]
    ?:  ?&(hn ?!(hp))  ~[(flop neg)]
    ~
  =/  x=@s  (snag i `(list @s)`v)
  ?:  =(--0 x)  $(i +(i))
  ?:  =(cs x)   $(i +(i), pos [i pos])
  ?:  =(nc x)   $(i +(i), neg [i neg])
  ::  a coordinate that is neither 0 nor +-cc: not an indicator
  ~
::    +pcols:  which power sums to build columns from
::
::  [gs md want cap] -> (list @ud), up to .want indices from 1..cap,
::  skipping any j whose column is identically zero across every modular
::  factor.
::
::  A ZERO COLUMN CARRIES NO INFORMATION: it imposes the same condition
::  on every subset, so it cannot separate one from another, and it costs
::  a full big-entry column of LLL time to say nothing.  This is not a
::  corner case, it is the benchmark family -- a Swinnerton-Dyer
::  polynomial is even, its roots come in +- pairs, so every modular
::  factor's roots sum to zero and EVERY ODD power sum vanishes
::  identically.  Taking j = 1..m blindly spends half the budget on dead
::  columns and, at m=2, left SD_3 and SD_5 with one live column between
::  them -- not enough to separate, so both fell back to the full
::  enumeration having paid for the lattice first.
++  pcols
  |=  [gs=(list mol) md=@ud n=@ud rb=@ud want=@ud cap=@ud]
  ^-  (list @ud)
  =/  j=@ud  1
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  ?|(=((lent out) want) (gth j cap))  (flop out)
  ::  stop before the bound outgrows the modulus.  n*B^j climbs fast, and
  ::  a column whose true trace cannot be told from a residue is worse
  ::  than no column: it rejects everything.  Taking FEWER live columns
  ::  than asked is correct -- one live column already separates when r
  ::  is small, and insisting on two here cost a small modulus every
  ::  proposal it had been making.
  ?:  (gte (mul 2 (mul n (pow rb j))) md)  (flop out)
  =/  col=(list @ud)
    (turn gs |=(g=mol ^-(@ud (snag (dec j) `(list @ud)`(psums g j md)))))
  ?:  (levy col |=(x=@ud =(0 x)))  $(j +(j))
  $(j +(j), out [j out])
::    +propose:  candidate subsets from the lattice (SPEC V3)
::
::  [f gs md] -> (list (list @ud)).  A HEURISTIC and nothing more.  Every
::  subset it returns is confirmed by trial division in +cand before it
::  becomes a factor, and anything it misses is found by +zass.  SPEC V4
::  is explicit that the lattice is an accelerator and never an oracle,
::  and that is exactly what lets this arm be wrong without +factor being
::  wrong -- a bad bound, a bad scaling, or a bad column choice costs
::  time, not correctness.
::
::  COLUMNS ARE CHOSEN, not assumed -- see +pcols.  Taking j = 1..m
::  blindly is wrong on the benchmark family: a Swinnerton-Dyer
::  polynomial is even, so every modular factor's roots sum to zero and
::  every ODD power sum vanishes identically.  At j = 1,2 that left one
::  live column, and SD_2 and SD_3 both got junk proposals.  +pcols skips
::  dead columns and stops before the bound outgrows the modulus, so it
::  may return one column, or none.
::
::  EIGHT live columns, and the count is what makes phase V1 work at all.
::  Four separated SD_3 but not SD_5: the offending subsets there have
::  size 8, so their indicator is SHORTER than the all-ones vector and
::  survives four conditions.  Eight excludes them, and SD_5 drops from
::  206 s (falling back to the full enumeration) to 9.6 s.
::
::  This budget is affordable only because of the integral rewrite.  On
::  the rational Gram-Schmidt, four columns at r=16 cost 221.7 s -- more
::  than the enumeration being replaced -- which is why the count was
::  pinned at two and why the pass lost to Zassenhaus everywhere.  The
::  same lattice now reduces in 2.3 s.  The algorithm did not change; the
::  arithmetic under it did.
::
::  cc scales the identity block to the trace bound so that the two
::  halves of a vector weigh comparably.  Without it the first r
::  coordinates are 0/1 against residues of size p^a and contribute
::  nothing to the norm, so LLL would happily return short vectors whose
::  v is not an indicator at all.
++  propose
  |=  [f=zol gs=(list mol) md=@ud]
  ^-  (list (list @ud))
  =/  r=@ud  (lent gs)
  =/  n=@ud  (deg:zx f)
  =/  b=@ud  (rbound f)
  ::  two LIVE columns, chosen rather than assumed
  =/  js=(list @ud)  (pcols gs md n b 8 20)
  ?~  js  ~
  =/  hi=@ud  (jmax js)
  ::  |s_j(F)| <= deg(F) * B^j <= n * B^hi for any true factor F
  =/  tb=@ud  (mul n (pow b hi))
  ::  if the true trace does not fit inside the modulus it cannot be told
  ::  from a residue, and every row is noise
  ?:  (gte (mul 2 tb) md)  ~
  =/  cc=@ud  (max 1 tb)
  (extract (lll (lat gs md cc js)) r cc n b js)
::    +harvest:  confirm proposed subsets, peeling factors off as they hold
++  harvest
  |=  $:  rem=zol
          idx=(list @ud)
          gs=(list mol)
          md=@ud
          ps=(list (list @ud))
          acc=(list zol)
      ==
  ^-  [rem=zol idx=(list @ud) acc=(list zol)]
  |-  ^-  [rem=zol idx=(list @ud) acc=(list zol)]
  ?~  ps  [rem idx acc]
  ::  usable only while every index it names is still unclaimed
  ?.  (levy i.ps |=(j=@ud (lien idx |=(k=@ud =(k j)))))
    $(ps t.ps)
  =/  sel=(list mol)  (turn i.ps |=(j=@ud (snag j `(list mol)`gs)))
  =/  cd  (cand sel rem md)
  ?~  cd  $(ps t.ps)
  %=  $
    ps   t.ps
    rem  (xdiv:zx rem u.cd)
    idx  (drop idx i.ps)
    acc  [u.cd acc]
  ==
::    +lat-min:  the smallest r at which the lattice pass runs
::
::  MEASURED, both ways, same inputs, same machine, by /gen/baloon-vh-bench:
::
::                  zassenhaus     van hoeij
::      SD_3           22.4 ms       42.5 ms
::      SD_4          298.7 ms      459.7 ms
::      SD_5          202.5 s         9.42 s    <- 21.5x
::
::  The crossover is between r = 8 and r = 16, and this sits at the
::  measured win rather than an interpolated guess, so engaging the
::  lattice is never the slower choice.  r = 12 is untested; lowering
::  this to reach it should be measured, not assumed.
::
::  SPEC V0 named SD_5's 204 s as the number phase V1 has to beat.  It is
::  beaten by a factor of twenty.
++  lat-min  ^-(@ud 16)
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
  ::  ONE Gram-Schmidt for the whole reduction.  It is computed here and
  ::  then MAINTAINED, never recomputed, because every mutation below has
  ::  a closed-form effect on it:
  ::
  ::    size-reduction   b_k -= q*b_j with j < k subtracts a vector lying
  ::                     in span(b_0 .. b_k-1), which is precisely what
  ::                     the projection already removes -- so no b* moves
  ::                     at all, and only mu row k does
  ::    swap             +gswap, two rows of b* and three groups of mu
  ::
  ::  Recomputing from scratch cost a full O(n^3) rational Gram-Schmidt
  ::  per outer iteration and was almost the entire runtime: hoisting it
  ::  out of the inner loop alone bought 6x at dimension 9, more than the
  ::  call-count reduction, which is only possible if the rest is noise.
  ::  SPEC V2 pins the reduction sequence but NOT this computation.
  =/  g  (igso cur)
  =/  k=@ud     1
  |-  ^-  zmat
  ?:  =(k n)  cur
  ::  size-reduce row k against k-1 .. 0, descending
  =/  rk
    =/  j=@ud     (dec k)
    =/  acc=zmat  cur
    =/  lm=zmat   lam.g
    |-  ^-  [acc=zmat lam=zmat]
    =/  dj=@s   (zat d.g +(j))
    =/  q=@s    (iround (zat (znth lm k) j) dj)
    =/  nx=zmat
      ?:  =(--0 q)  acc
      (zput acc k (zaxpy (znth acc k) (znth acc j) q))
    ::  b_k -= q*b_j sends mu_ki to mu_ki - q*mu_ji for every i.  Scaled
    ::  by d_(i+1) that is lam_ki -= q*lam_ji for i < j, and at i = j it
    ::  is lam_kj -= q*d_(j+1), since mu_jj = 1.  Above j, mu_ji is 0 and
    ::  nothing moves.  No d changes: b*_k is untouched by a subtraction
    ::  lying in the span the projection already removes.
    =/  nl=zmat
      ?:  =(--0 q)  lm
      =/  rk1=zvec  (znth lm k)
      =/  rj1=zvec  (znth lm j)
      =/  r2=zvec   (zeput rk1 j (dif:si (zat rk1 j) (pro:si q dj)))
      =/  r3=zvec
        =/  i=@ud    0
        =/  rr=zvec  r2
        |-  ^-  zvec
        ?:  =(i j)  rr
        %=  $
          i   +(i)
          rr  (zeput rr i (dif:si (zat rr i) (pro:si q (zat rj1 i))))
        ==
      (zput lm k r3)
    ?:  =(0 j)  [nx nl]
    $(j (dec j), acc nx, lm nl)
  =/  g1  [d=d.g lam=lam.rk]
  ::  Lovasz.  ||b*_k||^2 >= (3/4 - mu^2) ||b*_(k-1)||^2 becomes, on
  ::  multiplying through by 4*d_k*d_(k-1) and substituting
  ::  ||b*_i||^2 = d_(i+1)/d_i and mu = lam/d_k,
  ::
  ::      4 * d_(k+1) * d_(k-1)  >=  3 * d_k^2 - 4 * lam^2
  ::
  ::  which is integral on both sides.  The d_i are strictly positive, so
  ::  the multiplication cannot flip the inequality.
  =/  lk=@s   (zat (znth lam.g1 k) (dec k))
  =/  dkm=@s  (zat d.g1 (dec k))
  =/  dk=@s   (zat d.g1 k)
  =/  dk1=@s  (zat d.g1 +(k))
  =/  lhs=@s  (pro:si --4 (pro:si dk1 dkm))
  =/  rhs=@s
    %+  dif:si
      (pro:si --3 (pro:si dk dk))
    (pro:si --4 (pro:si lk lk))
  ?:  ?!(=(-1 (cmp:si lhs rhs)))
    $(cur acc.rk, g g1, k +(k))
  %=  $
    cur  (zswap acc.rk k (dec k))
    g    (iswap d.g1 lam.g1 k n)
    k    ?:((gth k 1) (dec k) 1)
  ==
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
  (fact f lat-min)
::    +fact:  +factor with the lattice gate exposed
::
::  [f=zol lo=@ud] -> (list zol).  .lo is the smallest number of modular
::  factors at which the lattice pass runs; +factor supplies +lat-min.
::
::  EXPOSED FOR TESTING, and it has to be.  SPEC V4 means a broken
::  lattice still factors correctly -- +cand rejects its bad proposals
::  and +zass finds whatever it missed -- so a lattice that proposes
::  nothing at all is invisible to any test that only checks the answer.
::  Passing 0 forces the pass on every input, which is the only way to
::  see that it proposes the RIGHT subsets rather than none.
++  fact
  |=  [f=zol lo=@ud]
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
  =/  r=@ud          (lent gs)
  =/  ps=(list (list @ud))
    ?:  (lth r lo)  ~
    (propose f gs md)
  =/  hv  (harvest f (gulf 0 (dec r)) gs md ps ~)
  (zass rem.hv idx.hv gs md acc.hv)
--
