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
::  Recomputed from scratch wherever it is needed rather than updated in
::  place.  That is O(n) slower and very much easier to be sure of, and
::  it changes NOTHING about the output: exact rational GSO and an
::  incrementally updated one are mathematically equal, which is why SPEC
::  V2 pins the reduction sequence but not this computation.
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
::    +mu-at:  the Gram-Schmidt coefficient mu_ij
++  mu-at
  |=  [mu=(list qvec) i=@ud j=@ud]
  ^-  frac
  =/  r=qvec  (nth mu i)
  =/  k=@ud   j
  |-  ^-  frac
  ?~  r  !!
  ?:  =(0 k)  i.r
  $(r t.r, k (dec k))
::    +nrm2:  the squared norm of the i-th Gram-Schmidt vector
++  nrm2
  |=  [bs=(list qvec) i=@ud]
  ^-  frac
  =/  v=qvec  (nth bs i)
  (qdot v v)
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
  ::  size-reduce row k against k-1 .. 0, descending
  =/  red=zmat
    =/  j=@ud     (dec k)
    =/  acc=zmat  cur
    |-  ^-  zmat
    =/  g       (gso acc)
    =/  q=@s    (zround (mu-at mu.g k j))
    =/  nx=zmat
      ?:  =(--0 q)  acc
      (zput acc k (zaxpy (znth acc k) (znth acc j) q))
    ?:  =(0 j)  nx
    $(j (dec j), acc nx)
  ::  Lovasz, on the reduced basis
  =/  g2  (gso red)
  =/  m=frac  (mu-at mu.g2 k (dec k))
  =/  rhs=frac
    (mul:qq (sub:qq del (mul:qq m m)) (nrm2 bs.g2 (dec k)))
  ?:  ?!(=(%lt (cmp:qq (nrm2 bs.g2 k) rhs)))
    $(cur red, k +(k))
  $(cur (zswap red k (dec k)), k ?:((gth k 1) (dec k) 1))
--
