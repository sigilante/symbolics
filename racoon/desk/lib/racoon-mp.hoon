  ::  /lib/racoon-mp
::::  Sparse multivariate polynomials -- SPEC Milestone C, phase M
::
::  Z[x_1..x_n] and Q[x_1..x_n], sparse and canonical.
::
::  A CONSUMER of /lib/racoon, and that is FORCED rather than preferred:
::  %racoon is frozen at five arms under R6, and Q5 records why the five
::  slots were reserved up front -- adding a sixth moves the battery axes
::  of the five already there.  %zx and %qx stay frozen and gain nothing.
::
::  SPARSE, and the word is load-bearing.  A dense representation stores
::  a coefficient per monomial, which in n variables of degree d is
::  (d+1)^n slots -- exponential in the number of variables, and
::  Calhoon's towers routinely reach four or five.  Only nonzero terms
::  are stored.
::
::  REPRESENTATION IS CANONICAL: terms descending in the pinned
::  lexicographic order, no zero coefficients, uniform arity.  So
::  =(a b) decides equality and every arm is `free`.
::
::  A SORTED LIST AND NOT A MAP.  A Hoon map is canonically shaped, so
::  =(a b) would work -- but its iteration order is +mor, a hash, which
::  makes the leading term a search and every printed form arbitrary.
::  Sorted, the head IS the leading term.
::
::  ARITY IS DERIVED, not stored: it is the length of any exponent
::  vector and +canon asserts they agree.  That is Baloon's "dimensions
::  derived, not stored" applied again -- a stored arity is an invariant
::  that can desync.  The zero polynomial therefore has no arity, and
::  +arity crashes on it exactly as +deg:zx crashes on ~.
::
::  THE TERM ORDER IS PINNED ONLY SO THAT = DECIDES.  SPEC M8 fences the
::  one operation whose VALUE would depend on it -- general division with
::  remainder, unique in several variables only when dividing by a
::  Groebner basis -- so no arm here changes answer with the order.
::
::  STATUS: M0, M1, and M2 are built and verified in-ship.  M3
::  (squarefree decomposition) and M4 (multivariate rational functions)
::  are specified in SPEC M6 and not written.
::
::  +gcd is checked by its DEFINITION rather than by agreement: the
::  product divides both arguments exactly -- which +xdiv decides -- and
::  the two cofactors are coprime.  Both are exact and need no oracle.
::  Arity 1 additionally agrees with +gcd:zx arm for arm, which is the
::  strongest check available here, since %zx is already verified
::  against SymPy over the whole Milestone A corpus.
::
::  THE GCD IS PRIMITIVE, so gcd(6xy, 15y) is y and not 3y.  That is
::  SPEC M3's pinned convention and §8's univariate one, and it is
::  written here because the first test to assert otherwise was the
::  test, not the library.
::
/-  *racoon
/+  racoon
=/  nz  nz:racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
|%
+|  %types
::    $mono:  an exponent vector, one entry per variable
::
::  Position 0 is the MOST significant variable.  Every $mono in a
::  polynomial has the same length, which is that polynomial's arity.
+$  mono  (list @ud)
::    $zmt:  one term over Z
+$  zmt  [m=mono c=@s]
::    $zmp:  a polynomial in Z[x_1..x_n]
::
::  Terms descending in the pinned order, no zero coefficient, uniform
::  arity.  The zero polynomial is ~.
+$  zmp  (list zmt)
::
+|  %monomials
::    +mcmp:  the pinned term order, lexicographic
::
::  Compare left to right; the first position where the exponents differ
::  decides, larger exponent greater.  Equal-length inputs run out
::  together, which is why the null cases both produce %eq.
++  mcmp
  |=  [a=mono b=mono]
  ^-  ord
  ?~  a  %eq
  ?~  b  %eq
  ?:  (gth i.a i.b)  %gt
  ?:  (lth i.a i.b)  %lt
  $(a t.a, b t.b)
::    +mmul:  multiply monomials, which is adding exponents
++  mmul
  |=  [a=mono b=mono]
  ^-  mono
  ?~  a  ~
  ?~  b  ~
  [(add i.a i.b) $(a t.a, b t.b)]
::    +mdeg:  total degree of a monomial
++  mdeg  |=(a=mono ^-(@ud (roll a add)))
::    +mzero:  the all-zero exponent vector at this arity
++  mzero  |=(n=@ud ^-(mono (reap n 0)))
::
+|  %zp
::    +zp:  polynomials over Z
++  zp
  |%
  ::  A core opens with a chapter or with none at all: a +| after the
  ::  first unchaptered arm is a syntax error, which is worth one line
  ::  of comment because the message points at the marker rather than
  ::  at the arm that made it illegal.
  +|  %shape
  ::    +canon:  impose the canonical form
  ::
  ::  Sort descending, combine like monomials, drop zero coefficients,
  ::  assert uniform arity.  The only arm accepting anything else.
  ::
  ::  Written with +snag and +slag rather than ?~ on the accumulator:
  ::  ?~ refines it to the empty list, and the next iteration assigns a
  ::  one-element list back, which then fails to nest.
  ++  canon
    |=  a=zmp
    ^-  zmp
    ?:  =(~ a)  ~
    =/  n=@ud  (lent m:(snag 0 a))
    ?>  (levy a |=(t=zmt ^-(? =(n (lent m.t)))))
    =/  ts=zmp   (sort a |=([x=zmt y=zmt] ^-(? =(%gt (mcmp m.x m.y)))))
    =/  cur=zmp  ~
    =|  out=zmp
    |-  ^-  zmp
    =/  flush=zmp
      ?:  |(=(~ cur) =(--0 c:(snag 0 cur)))  out
      [(snag 0 cur) out]
    ?:  =(~ ts)  (flop flush)
    =/  hd=zmt  (snag 0 ts)
    ?:  =(~ cur)  $(ts (slag 1 ts), cur ~[hd])
    =/  cu=zmt  (snag 0 cur)
    ?:  =(%eq (mcmp m.cu m.hd))
      $(ts (slag 1 ts), cur ~[cu(c (sum:si c.cu c.hd))])
    $(ts (slag 1 ts), cur ~[hd], out flush)
  ::    +is-zero:  structural, since zero has one representative
  ++  is-zero  |=(a=zmp ^-(? =(~ a)))
  ::    +arity:  the number of variables; crashes on zero
  ++  arity
    |=  a=zmp
    ^-  @ud
    ?~  a  !!
    (lent m.i.a)
  ::    +same-arity:  assert two nonzero operands agree
  ++  same-arity
    |=  [a=zmp b=zmp]
    ^-  ?
    ?:  |(=(~ a) =(~ b))  %.y
    =((arity a) (arity b))
  ::    +deg:  TOTAL degree; crashes on zero
  ++  deg
    |=  a=zmp
    ^-  @ud
    ?~  a  !!
    =/  ts=zmp  a
    =/  m=@ud   0
    |-  ^-  @ud
    ?~  ts  m
    $(ts t.ts, m (max m (mdeg m.i.ts)))
  ::    +degv:  degree in one variable; crashes on zero or a bad index
  ++  degv
    |=  [a=zmp i=@ud]
    ^-  @ud
    ?~  a  !!
    ?>  (lth i (arity a))
    =/  ts=zmp  a
    =/  m=@ud   0
    |-  ^-  @ud
    ?~  ts  m
    $(ts t.ts, m (max m (snag i m.i.ts)))
  ::    +lt:  the leading term, which is the head; crashes on zero
  ++  lt
    |=  a=zmp
    ^-  zmt
    ?~  a  !!
    i.a
  ::    +lc:  the leading coefficient
  ++  lc  |=(a=zmp ^-(@s c:(lt a)))
  ::    +zero:  the zero polynomial
  ++  zero  ^-(zmp ~)
  ::    +one:  the constant 1 at this arity
  ++  one  |=(n=@ud ^-(zmp ~[[(mzero n) --1]]))
  ::    +con:  a constant at this arity
  ++  con
    |=  [c=@s n=@ud]
    ^-  zmp
    ?:  =(--0 c)  ~
    ~[[(mzero n) c]]
  ::    +var:  the generator x_i at arity n
  ::
  ::  Exposed because writing an exponent vector by hand is exactly
  ::  where a mistake goes unnoticed.
  ++  var
    |=  [i=@ud n=@ud]
    ^-  zmp
    ?>  (lth i n)
    =/  k=@ud  0
    =|  out=mono
    =/  ex=mono
      |-  ^-  mono
      ?:  =(k n)  (flop out)
      $(k +(k), out [?:(=(k i) 1 0) out])
    ~[[ex --1]]
  ::    +neg:  negation, term by term
  ++  neg
    |=  a=zmp
    ^-  zmp
    (turn a |=(t=zmt ^-(zmt t(c (dif:si --0 c.t)))))
  ::    +add:  addition
  ++  add
    |=  [a=zmp b=zmp]
    ^-  zmp
    ?>  (same-arity a b)
    (canon (weld a b))
  ::    +sub:  subtraction
  ++  sub  |=([a=zmp b=zmp] ^-(zmp (add a (neg b))))
  ::    +mul:  multiplication, every term against every term
  ++  mul
    |=  [a=zmp b=zmp]
    ^-  zmp
    ?>  (same-arity a b)
    ?:  |(=(~ a) =(~ b))  ~
    %-  canon
    %-  zing
    %+  turn  a
    |=  s=zmt
    ^-  zmp
    (turn b |=(t=zmt ^-(zmt [(mmul m.s m.t) (pro:si c.s c.t)])))
  ::    +scale:  multiply by an integer
  ++  scale
    |=  [a=zmp c=@s]
    ^-  zmp
    ?:  =(--0 c)  ~
    (turn a |=(t=zmt ^-(zmt t(c (pro:si c.t c)))))
  ::    +pow:  a whole power
  ++  pow
    |=  [a=zmp e=@ud]
    ^-  zmp
    ?:  =(0 e)  (one (arity a))
    =/  k=@ud    e
    =/  acc=zmp  a
    |-  ^-  zmp
    ?:  =(1 k)  acc
    $(k (dec k), acc (mul acc a))
  ::    +eval:  the value at an integer point
  ++  eval
    |=  [a=zmp pt=(list @s)]
    ^-  @s
    ?~  a  --0
    ?>  =((lent pt) (arity a))
    =/  ts=zmp  a
    =/  acc=@s  --0
    |-  ^-  @s
    ?~  ts  acc
    $(ts t.ts, acc (sum:si acc (pro:si c.i.ts (mval m.i.ts pt))))
  ::    +mval:  a monomial's value at a point
  ++  mval
    |=  [m=mono pt=(list @s)]
    ^-  @s
    ?~  m  --1
    ?~  pt  --1
    =/  k=@ud   i.m
    =/  acc=@s  --1
    =/  p=@s    i.pt
    =/  v=@s
      |-  ^-  @s
      ?:  =(0 k)  acc
      $(k (dec k), acc (pro:si acc p))
    ::  $ and not ^$: the |- above closed inside its own =/, so the
    ::  nearest loop in scope here is already this gate
    (pro:si v $(m t.m, pt t.pt))
  ::    +evalv:  substitute ONE variable, dropping it
  ::
  ::  The arity falls by one, which is what makes this the arm the
  ::  recursive algorithms below are built on rather than +eval.
  ++  evalv
    |=  [a=zmp i=@ud v=@s]
    ^-  zmp
    ::  =(~ a) and not ?~: ?~ refines .a to a non-empty list, and the
    ::  wet +turn below will not nest against the refined type
    ?:  =(~ a)  ~
    ?>  (lth i (arity a))
    %-  canon
    %+  turn  a
    |=  t=zmt
    ^-  zmt
    =/  e=@ud   (snag i m.t)
    =/  k=@ud   e
    =/  acc=@s  --1
    =/  p=@s
      |-  ^-  @s
      ?:  =(0 k)  acc
      $(k (dec k), acc (pro:si acc v))
    [(oust [i 1] m.t) (pro:si c.t p)]
  ::    +deriv:  the partial derivative in one variable
  ++  deriv
    |=  [a=zmp i=@ud]
    ^-  zmp
    ?:  =(~ a)  ~
    ?>  (lth i (arity a))
    %-  canon
    %+  turn  a
    |=  t=zmt
    ^-  zmt
    =/  e=@ud  (snag i m.t)
    ?:  =(0 e)  [m.t --0]
    [(snap m.t i (dec e)) (pro:si c.t (sun:si e))]
  ::
  +|  %content
  ::    +content:  the integer content, non-negative
  ::
  ::  SPEC S8's univariate convention, unchanged: content(~) = 0, and
  ::  content * pp = input exactly, so +pp carries the sign.
  ++  content
    |=  a=zmp
    ^-  @ud
    =/  ts=zmp  a
    =/  g=@ud   0
    |-  ^-  @ud
    ?~  ts  g
    $(ts t.ts, g (gcd:nz g (abs:si c.i.ts)))
  ::    +pp:  the primitive part
  ++  pp
    |=  a=zmp
    ^-  zmp
    ?:  =(~ a)  ~
    =/  g=@ud  (content a)
    (turn a |=(t=zmt ^-(zmt t(c (fra:si c.t (sun:si g))))))
  ::
  ::
  +|  %recursive
  ::    +mdiv:  divide monomials, or ~ when it does not divide
  ++  mdiv
    |=  [a=mono b=mono]
    ^-  (unit mono)
    ?~  a  `~
    ?~  b  `~
    ?:  (lth i.a i.b)  ~
    =/  rest  $(a t.a, b t.b)
    ?~  rest  ~
    ::  ^sub: inside +zp, `sub` is polynomial subtraction
    `[(^sub i.a i.b) u.rest]
  ::    +shiftv:  multiply by x_i^k
  ::
  ::  No +canon: multiplying every term by one monomial preserves the
  ::  order, so the list is still sorted.
  ++  shiftv
    |=  [a=zmp i=@ud k=@ud]
    ^-  zmp
    (turn a |=(t=zmt ^-(zmt [(snap m.t i (^add k (snag i m.t))) c.t])))
  ::    +lcv:  the leading coefficient in variable i, at the SAME arity
  ::
  ::  The x_i exponent is zeroed rather than dropped, so the product can
  ::  be multiplied straight back into a polynomial of the same arity --
  ::  which is what keeps the pseudo-remainder loop from juggling
  ::  arities on every step.
  ++  lcv
    |=  [a=zmp i=@ud]
    ^-  zmp
    ?:  =(~ a)  ~
    =/  d=@ud  (degv a i)
    %-  canon
    %+  murn  a
    |=  t=zmt
    ^-  (unit zmt)
    ?.  =(d (snag i m.t))  ~
    `[(snap m.t i 0) c.t]
  ::    +to-rec:  the recursive view -- univariate in x_0 over the rest
  ::
  ::  Index is the degree in x_0; entries have arity n-1.
  ++  to-rec
    |=  a=zmp
    ^-  (list zmp)
    ::  One pass per degree rather than one scatter per term: the
    ::  scattering form needs +snap and +snag, both wet, over a list of
    ::  lists, and the inferrer will not close on it.
    ?:  =(~ a)  ~
    =/  d=@ud  (degv a 0)
    =/  e=@ud  0
    =|  out=(list zmp)
    |-  ^-  (list zmp)
    ?:  (gth e d)  (flop out)
    =/  bucket=zmp
      %-  canon
      %+  murn  a
      |=  t=zmt
      ^-  (unit zmt)
      ?.  =(e (snag 0 m.t))  ~
      `[(slag 1 m.t) c.t]
    $(e +(e), out [bucket out])
  ::    +lift0:  raise arity n-1 to arity n, at x_0 exponent zero
  ++  lift0
    |=  a=zmp
    ^-  zmp
    (turn a |=(t=zmt ^-(zmt [(into m.t 0 0) c.t])))
  ::
  +|  %division
  ::    +xdiv:  EXACT division; crashes when the division is inexact
  ::
  ::  Repeated leading-term elimination.  It terminates because each
  ::  step strictly lowers the leading term and the order well-orders
  ::  the monomials at a fixed arity.
  ::
  ::  Only the exact case is exposed (SPEC M8): in several variables a
  ::  remainder depends on the term order AND on the order divisors are
  ::  tried, and is unique only against a Groebner basis.  The exact
  ::  quotient has neither problem.
  ++  xdiv
    |=  [a=zmp b=zmp]
    ^-  zmp
    ?~  b  !!
    ?:  =(~ a)  ~
    ?>  (same-arity a b)
    =/  lb=zmt  (lt b)
    =/  r=zmp   a
    =|  q=zmp
    |-  ^-  zmp
    ?:  =(~ r)  (canon q)
    =/  lr=zmt        (lt r)
    =/  md=(unit mono)  (mdiv m.lr m.lb)
    ?~  md  !!
    =/  cq=@s  (fra:si c.lr c.lb)
    ?>  =(c.lr (pro:si cq c.lb))
    =/  t=zmp  ~[[u.md cq]]
    $(q [[u.md cq] q], r (sub r (mul t b)))
  ::    +prem:  the pseudo-remainder in x_0
  ::
  ::  Kills the leading x_0 coefficient each step, so the degree in x_0
  ::  strictly falls and the loop terminates.  The power of the leading
  ::  coefficient it multiplied through by is not tracked, which is
  ::  sound here because every caller takes a primitive part afterwards.
  ++  prem
    |=  [a=zmp b=zmp]
    ^-  zmp
    ?~  b  !!
    =/  db=@ud  (degv b 0)
    =/  l=zmp   (lcv b 0)
    =/  r=zmp   a
    |-  ^-  zmp
    ?:  =(~ r)  ~
    =/  dr=@ud  (degv r 0)
    ?:  (lth dr db)  r
    $(r (sub (mul l r) (mul (lcv r 0) (shiftv b 0 (^sub dr db)))))
  ::
  +|  %content-and-gcd
  ::    +norm:  primitive, with a positive leading coefficient
  ::
  ::  The GCD normalization of SPEC M3, identical to §8's univariate
  ::  one -- which is what makes arity 1 agree with %zx arm for arm.
  ++  norm
    |=  a=zmp
    ^-  zmp
    ?:  =(~ a)  ~
    =/  p=zmp  (pp a)
    ?:((syn:si (lc p)) p (neg p))
  ::    +contentv:  the content in R[x_1..x_n], AT ARITY n-1
  ::
  ::  Mutually recursive with +gcd and well-founded on arity: this calls
  ::  +gcd one variable down, and +gcd bottoms out at arity 1 in %zx.
  ::
  ::  IT MUST NOT LIFT.  Returning the content already raised to arity n
  ::  reads better at the call sites and makes +gcd recurse at its own
  ::  arity forever -- the loop is silent, since every step is
  ::  well-formed and merely never smaller.  Callers lift explicitly
  ::  with +lift0 where they need to.
  ++  contentv
    |=  a=zmp
    ^-  zmp
    ?:  =(~ a)  ~
    =/  ls=(list zmp)  (to-rec a)
    =/  g=zmp  ~
    |-  ^-  zmp
    ?~  ls  g
    $(ls t.ls, g (gcd g i.ls))
  ::    +ppv:  the primitive part against that content
  ++  ppv
    |=  a=zmp
    ^-  zmp
    ?:  =(~ a)  ~
    (xdiv a (lift0 (contentv a)))
  ::    +gcd:  the greatest common divisor
  ::
  ::  Primitive with a positive leading coefficient; gcd(~, ~) = ~.
  ::
  ::  ARITY 1 DELEGATES TO +gcd:zx.  That is not a shortcut -- it is the
  ::  base case, and it means every multivariate GCD bottoms out in the
  ::  frozen library that is already verified against SymPy over the
  ::  whole Milestone A corpus.
  ::
  ::  Above that: recursive primitive PRS.  Split each argument into its
  ::  content in R and its primitive part; the GCD is the GCD of the
  ::  contents times the GCD of the primitive parts, and the second is a
  ::  Euclidean algorithm on pseudo-remainders with the primitive part
  ::  taken at every step -- which is what keeps the coefficients from
  ::  exploding.  SPEC M3 records that the reference is chosen for being
  ::  obviously correct and that a jet may use Zippel or EEZ instead.
  ++  gcd
    |=  [a=zmp b=zmp]
    ^-  zmp
    ?:  =(~ a)  (norm b)
    ?:  =(~ b)  (norm a)
    ?>  (same-arity a b)
    =/  n=@ud  (arity a)
    ?:  =(1 n)
      =/  ua=(unit zol)  (to-uni a 0)
      =/  ub=(unit zol)  (to-uni b 0)
      ?~  ua  !!
      ?~  ub  !!
      (of-uni (gcd:zx u.ua u.ub) 0 1)
    ::  the content GCD is taken one arity DOWN, then lifted
    =/  d=zmp  (lift0 (gcd (contentv a) (contentv b)))
    =/  u=zmp  (ppv a)
    =/  v=zmp  (ppv b)
    ::  the Euclidean loop wants deg_0 u >= deg_0 v, and every later
    ::  step preserves it because the remainder has strictly lower
    ::  degree than the divisor
    ?:  (lth (degv u 0) (degv v 0))  $(a b, b a)
    =/  g=zmp
      |-  ^-  zmp
      ?:  =(~ v)  u
      =/  r=zmp  (prem u v)
      ?:  =(~ r)  v
      $(u v, v (ppv r))
    (norm (mul d g))
  ::
  +|  %bridge
  ::    +to-uni:  down to %zx when only variable i occurs
  ::
  ::  ~ when any other variable appears.  The arm that lets a caller
  ::  fall back into the frozen, jetted library -- and the one SPEC M7.4
  ::  tests against, since %zx is already verified against SymPy over
  ::  the whole Milestone A corpus.
  ++  to-uni
    |=  [a=zmp i=@ud]
    ^-  (unit zol)
    ?:  =(~ a)  `~
    ?>  (lth i (arity a))
    =/  ok=?
      %+  levy  a
      |=  t=zmt
      ^-  ?
      =/  k=@ud  0
      =/  ms=mono  m.t
      |-  ^-  ?
      ?~  ms  %.y
      ?:  |(=(k i) =(0 i.ms))  $(ms t.ms, k +(k))
      %.n
    ?.  ok  ~
    =/  d=@ud  (degv a i)
    =/  out=(list @s)  (reap +(d) --0)
    =/  ts=zmp  a
    |-  ^-  (unit zol)
    ?~  ts  `(canon:zx out)
    =/  e=@ud  (snag i m.i.ts)
    $(ts t.ts, out (snap out e (sum:si (snag e out) c.i.ts)))
  ::    +of-uni:  up from %zx, placing the polynomial at variable i
  ++  of-uni
    |=  [a=zol i=@ud n=@ud]
    ^-  zmp
    ?>  (lth i n)
    =/  cs=zol  a
    =/  e=@ud   0
    =|  out=zmp
    |-  ^-  zmp
    ?~  cs  (canon out)
    ?:  =(--0 i.cs)  $(cs t.cs, e +(e))
    $(cs t.cs, e +(e), out [[(snap (mzero n) i e) i.cs] out])
  --
--
