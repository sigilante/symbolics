  ::  /lib/racoon
::::  Racoon, Real AlgebraiCs in hOON
::
::  A deterministic computer algebra kernel: exact arithmetic over Z, Q, and
::  Z/n, and univariate polynomial arithmetic over each.  This library is the
::  specification; native jets must be Kleene-equal to it on every input.
::
::  Phase 0: scalars and number theory (+nz, +qq).
::
/-  *racoon
=<  racoon
~%  %non  ..part  ~
|%
+|  %private
::    +pv:  private helpers, not part of the public API
::
::  Deliberately outside the %racoon jet core, so that the battery layout of
::  the hinted cores is unaffected by helper churn.
++  pv
  |%
  ::    +powm:  modular exponentiation
  ::
  ::  [b=@ud e=@ud m=@ud] -> @ud in [0, m).  Binary left-to-right
  ::  square-and-multiply.  0^0 = 1.  Crashes on m = 0.
  ++  powm
    |=  [b=@ud e=@ud m=@ud]
    ^-  @ud
    ?:  =(1 m)   0
    ?:  =(0 e)   (mod 1 m)
    =/  bb=@ud   (mod b m)
    =/  k=@ud    (dec (met 0 e))
    =/  acc=@ud  bb
    |-  ^-  @ud
    ?:  =(0 k)   acc
    =/  nk=@ud   (dec k)
    =/  sq=@ud   (mod (mul acc acc) m)
    %=  $
      k    nk
      acc  ?:(=(1 (cut 0 [nk 1] e)) (mod (mul sq bb) m) sq)
    ==
  ::    +ds:  split off powers of two
  ::
  ::  [n=@ud] -> [d=@ud s=@ud] with n = d * 2^s and d odd.  Diverges on n = 0.
  ++  ds
    |=  n=@ud
    ^-  [d=@ud s=@ud]
    =|  s=@ud
    |-  ^-  [d=@ud s=@ud]
    ?:  =(1 (end 0 n))  [n s]
    $(n (rsh 0 n), s +(s))
  ::    +pows:  exponentiation over Z
  ::
  ::  [b=@s e=@ud] -> @s.  Binary left-to-right square-and-multiply (SPEC
  ::  S7).  b^0 = --1 for every b, including --0.
  ++  pows
    |=  [b=@s e=@ud]
    ^-  @s
    ?:  =(0 e)  --1
    =/  k=@ud    (dec (met 0 e))
    =/  acc=@s   b
    |-  ^-  @s
    ?:  =(0 k)  acc
    =/  nk=@ud  (dec k)
    =/  sq=@s   (pro:si acc acc)
    %=  $
      k    nk
      acc  ?:(=(1 (cut 0 [nk 1] e)) (pro:si sq b) sq)
    ==
  ::    +zdiv:  exact scalar division of a Z[x] polynomial
  ::
  ::  [a=zol d=@s] -> zol.  The caller guarantees d divides every
  ::  coefficient exactly; ++fra:si truncates, so an inexact call would
  ::  silently produce a wrong answer rather than crashing.  Every use in
  ::  this library is a division the subresultant theory proves exact.
  ++  zdiv
    |=  [a=zol d=@s]
    ^-  zol
    (turn a |=(c=@s (fra:si c d)))
  ::    +zderiv:  formal derivative in Z[x]
  ::
  ::  [a=zol] -> zol.  deriv(~) = ~ and deriv(c) = ~ for constant c.  The
  ::  product stays canonical: for deg a >= 1 the top coefficient becomes
  ::  n*c_n with n >= 1 and c_n nonzero, hence nonzero over Z.
  ++  zderiv
    |=  a=zol
    ^-  zol
    ?~  a  ~
    =/  cs=zol  t.a
    =/  k=@ud   1
    =|  out=zol
    |-  ^-  zol
    ?~  cs  (flop out)
    $(cs t.cs, k +(k), out [(pro:si (sun:si k) i.cs) out])
  ::    +zmod:  reduce a Z[x] polynomial into (Z/p)[x]
  ::
  ::  [a=zol p=@ud] -> mol.  Trailing zeros are stripped, so the degree can
  ::  drop when p divides the leading coefficient.
  ::
  ::  ++dul:si is deliberately not used: it computes (sub b +.c) for a
  ::  negative operand, which underflows whenever the magnitude exceeds p.
  ++  zmod
    |=  [a=zol p=@ud]
    ^-  mol
    =/  cs=(list @ud)
      %+  turn  a
      |=  c=@s
      ^-  @ud
      =/  m=@ud  (mod (abs:si c) p)
      ?:  (syn:si c)  m
      (mod (sub p m) p)
    =/  r=(list @ud)  (flop cs)
    |-  ^-  mol
    ?~  r  ~
    ?:  =(0 i.r)  $(r t.r)
    (flop r)
  ::    +mr:  one Miller-Rabin round
  ::
  ::  [n=@ud a=@ud d=@ud s=@ud] -> ?, where n - 1 = d * 2^s, d odd, s >= 1.
  ::  Produces %.y iff n is a strong probable prime to the base a, i.e. iff
  ::  a is not a witness to n's compositeness.
  ++  mr
    |=  [n=@ud a=@ud d=@ud s=@ud]
    ^-  ?
    =/  x=@ud  (powm a d n)
    ?:  ?|(=(1 x) =(x (dec n)))  %.y
    =/  i=@ud  (dec s)
    |-  ^-  ?
    ?:  =(0 i)  %.n
    =/  y=@ud  (mod (mul x x) n)
    ?:  =(y (dec n))  %.y
    $(x y, i (dec i))
  --
+|  %public
++  racoon
  ~/  %racoon
  |%
  +|  %scalars
  ::    +nz:  integers and elementary number theory
  ::
  ::  FROZEN at the P0 gate (R6).  Arm set and order are fixed for Milestone
  ::  A; no reordering, renaming, or insertion without escalation.
  ++  nz
    ~/  %nz
    |%
    ::    +gcd:  greatest common divisor over the naturals
    ::
    ::  [a=@ud b=@ud] -> @ud.  Euclid's algorithm.  gcd(0, 0) = 0 and
    ::  gcd(a, 0) = gcd(0, a) = a.  Never crashes.
    ++  gcd
      ~/  %gcd
      |=  [a=@ud b=@ud]
      ^-  @ud
      ?:  =(0 b)  a
      $(a b, b (mod a b))
    ::    +egcd:  extended Euclidean algorithm
    ::
    ::  [a=@ud b=@ud] -> [d=@ud u=@s v=@s] with d = gcd(a, b) and
    ::  d = u*a + v*b.  Algorithm pinned: textbook EEA (vzGG Alg. 3.6), base
    ::  case egcd(a, 0) = [a --1 --0].  For a, b > 0 the cofactors satisfy
    ::  |u| <= b/(2d) and |v| <= a/(2d).  Never crashes.
    ++  egcd
      ~/  %egcd
      |=  [a=@ud b=@ud]
      ^-  [d=@ud u=@s v=@s]
      =/  r0=@ud  a    =/  r1=@ud  b
      =/  s0=@s   --1  =/  s1=@s   --0
      =/  t0=@s   --0  =/  t1=@s   --1
      |-  ^-  [d=@ud u=@s v=@s]
      ?:  =(0 r1)  [r0 s0 t0]
      =/  q=@ud   (div r0 r1)
      =/  qs=@s   (sun:si q)
      %=  $
        r0  r1
        r1  (sub r0 (mul q r1))
        s0  s1
        s1  (dif:si s0 (pro:si qs s1))
        t0  t1
        t1  (dif:si t0 (pro:si qs t1))
      ==
    ::    +isqrt:  integer square root
    ::
    ::  [a=@ud] -> @ud, the unique r with r^2 <= a < (r+1)^2.  Newton
    ::  iteration seeded above the root from the bit length, descending
    ::  monotonically.  isqrt(0) = 0.  Never crashes.
    ++  isqrt
      |=  a=@ud
      ^-  @ud
      ?:  (lth a 4)  ?:(=(0 a) 0 1)
      =/  x=@ud  (bex (div +((met 0 a)) 2))
      |-  ^-  @ud
      =/  y=@ud  (div (add x (div a x)) 2)
      ?:  (gte y x)  x
      $(x y)
    ::    +is-prime:  primality test
    ::
    ::  [n=@ud] -> ?.  Deterministic Miller-Rabin over the pinned witness
    ::  schedule [2 3 5 7 11 13 17 19 23 29 31 37], in that order.  Provably
    ::  exact for n < 3.317e24 (Sorenson-Webster); above that bound the same
    ::  schedule runs and the answer is deterministic but heuristic.
    ::  n < 2 is not prime.  Never crashes.
    ++  is-prime
      ~/  %is-prime
      |=  n=@ud
      ^-  ?
      ?:  (lth n 2)  %.n
      ::  n - 1 = d * 2^s, d odd; s >= 1 whenever +mr is reached below,
      ::  since every even n > 2 is caught by the trial division.
      =/  f  (ds:pv (dec n))
      =/  ws=(list @ud)  ~[2 3 5 7 11 13 17 19 23 29 31 37]
      |-  ^-  ?
      ?~  ws  %.y
      ?:  =(n i.ws)  %.y
      ?:  =(0 (mod n i.ws))  %.n
      ?.  (mr:pv n i.ws d.f s.f)  %.n
      $(ws t.ws)
    ::    +crt:  Chinese remainder reconstruction
    ::
    ::  [(list [r=@ud m=@ud])] -> [r=@ud m=@ud], the unique r in [0, prod m)
    ::  congruent to each r_i modulo m_i, with m the product of the moduli.
    ::  Left fold, combining pairwise through +egcd.
    ::  Crashes on the empty list, on any modulus < 2, and if the moduli are
    ::  not pairwise coprime.
    ++  crt
      ~/  %crt
      |=  rs=(list [r=@ud m=@ud])
      ^-  [r=@ud m=@ud]
      ?~  rs  !!
      ?>  (gte m.i.rs 2)
      =/  acc=[r=@ud m=@ud]  [(mod r.i.rs m.i.rs) m.i.rs]
      =/  xs=(list [r=@ud m=@ud])  t.rs
      |-  ^-  [r=@ud m=@ud]
      ?~  xs  acc
      ?>  (gte m.i.xs 2)
      =/  e   (egcd m.acc m.i.xs)
      ::  pairwise coprimality: gcd of the running product with the next
      ::  modulus is 1 exactly when the moduli are pairwise coprime.
      ?>  =(1 d.e)
      =/  m2=@ud  m.i.xs
      =/  mm=@ud  (mul m.acc m2)
      ::  u.e * m.acc = 1 mod m2; the EEA bound |u| <= m2/2 keeps +dul safe.
      =/  uu=@ud  (dul:si u.e m2)
      =/  df=@ud  (mod (sub (add (mod r.i.xs m2) m2) (mod r.acc m2)) m2)
      =/  t=@ud   (mod (mul df uu) m2)
      %=  $
        acc  [(mod (add r.acc (mul m.acc t)) mm) mm]
        xs   t.xs
      ==
    ::    +ratrec:  rational reconstruction
    ::
    ::  [u=@ud m=@ud nb=@ud db=@ud] -> (unit frac).  Recovers the p/q with
    ::  q*u = p mod m, |p| <= nb, and 0 < q <= db, when one exists.
    ::  Algorithm pinned (Wang, vzGG S5.10): run the EEA on (m, u), stop at
    ::  the first remainder <= nb, and accept iff the corresponding cofactor
    ::  satisfies |t| <= db and gcd(r, |t|) = 1.  The usual caller bound is
    ::  nb = db = isqrt((m-1)/2).
    ::  Does not crash: failure is ~, not a crash.
    ++  ratrec
      |=  [u=@ud m=@ud nb=@ud db=@ud]
      ^-  (unit frac)
      =/  r0=@ud  m
      =/  r1=@ud  u
      =/  t0=@s   --0
      =/  t1=@s   --1
      |-  ^-  (unit frac)
      ?:  (lte r1 nb)
        ?:  =(--0 t1)  ~
        =/  aq=@ud  (abs:si t1)
        ?.  (lte aq db)  ~
        ?.  =(1 (gcd r1 aq))  ~
        `[(new:si (syn:si t1) r1) aq]
      =/  q=@ud  (div r0 r1)
      =/  qs=@s  (sun:si q)
      %=  $
        r0  r1
        r1  (sub r0 (mul q r1))
        t0  t1
        t1  (dif:si t0 (pro:si qs t1))
      ==
    --
  ::    +qq:  rational scalars
  ::
  ::  Every arm produces a canonical $frac: q > 0 and gcd(|p|, q) = 1.
  ++  qq
    ~/  %qq
    |%
    ::  FROZEN at the P0 gate (R6).  Arm set and order are fixed for
    ::  Milestone A; no reordering, renaming, or insertion without escalation.
    ::
    ::    +zero:  the additive identity of Q
    ++  zero  ^-(frac [--0 1])
    ::    +one:  the multiplicative identity of Q
    ++  one   ^-(frac [--1 1])
    ::    +new:  build a canonical rational
    ::
    ::  [p=@s q=@ud] -> frac, reduced to lowest terms.  Crashes on q = 0.
    ++  new
      |=  [p=@s q=@ud]
      ^-  frac
      ?<  =(0 q)
      =/  g=@ud  (gcd:nz (abs:si p) q)
      [(fra:si p (sun:si g)) (^div q g)]
    ::    +add:  addition in Q
    ++  add
      |=  [a=frac b=frac]
      ^-  frac
      %+  new
        (sum:si (pro:si p.a (sun:si q.b)) (pro:si p.b (sun:si q.a)))
      (^mul q.a q.b)
    ::    +neg:  additive inverse in Q
    ++  neg
      |=  a=frac
      ^-  frac
      [(dif:si --0 p.a) q.a]
    ::    +sub:  subtraction in Q
    ++  sub
      |=  [a=frac b=frac]
      ^-  frac
      (add a (neg b))
    ::    +mul:  multiplication in Q
    ++  mul
      |=  [a=frac b=frac]
      ^-  frac
      (new (pro:si p.a p.b) (^mul q.a q.b))
    ::    +inv:  multiplicative inverse in Q
    ::
    ::  Crashes on zero.
    ++  inv
      |=  a=frac
      ^-  frac
      ?<  =(--0 p.a)
      (new (new:si (syn:si p.a) q.a) (abs:si p.a))
    ::    +div:  division in Q
    ::
    ::  Crashes on a zero divisor.
    ++  div
      |=  [a=frac b=frac]
      ^-  frac
      ?<  =(--0 p.b)
      (mul a (inv b))
    ::    +cmp:  total order on Q
    ::
    ::  Compares p1*q2 against p2*q1 through +cmp:si.  Never crashes.
    ++  cmp
      |=  [a=frac b=frac]
      ^-  ord
      =/  c=@s
        (cmp:si (pro:si p.a (sun:si q.b)) (pro:si p.b (sun:si q.a)))
      ?:  =(--0 c)  %eq
      ?:  (syn:si c)  %gt
      %lt
    --
  +|  %polynomials
  ::  +mx and +qx are declared empty deliberately.  Adding an arm to a core
  ::  changes the battery axes of the arms already in it, so introducing a
  ::  sub-core when its phase lands would shift the %racoon battery -- and
  ::  with it the parent axis every sub-core jet resolves against -- at each
  ::  gate.  Declaring all five arms up front fixes %racoon for the
  ::  milestone; each sub-core's own layout freezes at its own phase gate.
  ::  See SPEC-QUESTIONS Q5.
  ::
  ::    +zx:  Z[x]
  ::
  ::  Dense little-endian polynomials over the integers: index i holds the
  ::  coefficient of x^i, and the canonical form carries no trailing --0, so
  ::  the zero polynomial is ~.  Every arm requires canonical input and
  ::  produces canonical output; +canon is the sole exception (R5).
  ::
  ::  Phase 1 arithmetic below.  Phase 2 adds pdiv, content, pp, gcd, res,
  ::  disc, and mig; Phase 3 adds sqfree and factor.
  ++  zx
    ~/  %zx
    |%
    ::    +canon:  impose the canonical form
    ::
    ::  [a=zol] -> zol.  Strips every trailing zero coefficient.  The only
    ::  arm that accepts non-canonical input.  Never crashes.
    ++  canon
      |=  a=zol
      ^-  zol
      =/  r=zol  (flop a)
      |-  ^-  zol
      ?~  r  ~
      ?:  =(--0 i.r)  $(r t.r)
      (flop r)
    ::    +is-zero:  is this the zero polynomial?
    ::
    ::  [a=zol] -> ?.  Never crashes.
    ++  is-zero
      |=  a=zol
      ^-  ?
      =(~ a)
    ::    +deg:  degree
    ::
    ::  [a=zol] -> @ud, the (dec (lent a)) of SPEC S7.  Crashes on ~: the
    ::  degree of the zero polynomial is undefined (S8).
    ++  deg
      |=  a=zol
      ^-  @ud
      ?~  a  !!
      (dec (lent a))
    ::    +lc:  leading coefficient
    ::
    ::  [a=zol] -> @s, the coefficient of x^deg(a), nonzero by the canonical
    ::  form.  Crashes on ~ (S8).
    ++  lc
      |=  a=zol
      ^-  @s
      ?~  a  !!
      |-  ^-  @s
      ?~  t.a  i.a
      $(a t.a)
    ::    +pcmp:  total order on Z[x]
    ::
    ::  [a=zol b=zol] -> ord.  SPEC S7: shorter list first, so ~ is least;
    ::  at equal length compare coefficients from the highest index down
    ::  through ++cmp:si.  Never crashes.
    ++  pcmp
      |=  [a=zol b=zol]
      ^-  ord
      =/  la=@ud  (lent a)
      =/  lb=@ud  (lent b)
      ?:  (lth la lb)  %lt
      ?:  (gth la lb)  %gt
      =/  ra=zol  (flop a)
      =/  rb=zol  (flop b)
      |-  ^-  ord
      ?~  ra  %eq
      ?~  rb  %eq
      =/  c=@s  (cmp:si i.ra i.rb)
      ?:  =(--0 c)  $(ra t.ra, rb t.rb)
      ?:  (syn:si c)  %gt
      %lt
    ::    +add:  addition in Z[x]
    ::
    ::  [a=zol b=zol] -> zol.  Coefficientwise.  The sum is canonicalized:
    ::  unlike +mul, leading terms can cancel.  Never crashes.
    ++  add
      |=  [a=zol b=zol]
      ^-  zol
      %-  canon
      |-  ^-  zol
      ?~  a  b
      ?~  b  a
      [(sum:si i.a i.b) $(a t.a, b t.b)]
    ::    +neg:  additive inverse in Z[x]
    ::
    ::  [a=zol] -> zol.  Negation preserves the canonical form, so no
    ::  canonicalization is needed.  Never crashes.
    ++  neg
      |=  a=zol
      ^-  zol
      (turn a |=(c=@s (dif:si --0 c)))
    ::    +sub:  subtraction in Z[x]
    ::
    ::  [a=zol b=zol] -> zol.  Never crashes.
    ++  sub
      |=  [a=zol b=zol]
      ^-  zol
      (add a (neg b))
    ::    +mul:  multiplication in Z[x]
    ::
    ::  [a=zol b=zol] -> zol.  Classical convolution (vzGG S2), accumulated
    ::  as a sum of shifted scalar multiples of b.  Z is an integral domain,
    ::  so lc(a*b) = lc(a)*lc(b) is nonzero and the leading term cannot
    ::  cancel.  mul(~, b) = mul(a, ~) = ~.  Never crashes.
    ++  mul
      ~/  %mul
      |=  [a=zol b=zol]
      ^-  zol
      ?~  a  ~
      ?~  b  ~
      =/  xs=zol   a
      =/  acc=zol  ~
      =/  k=@ud    0
      |-  ^-  zol
      ?~  xs  acc
      %=  $
        xs   t.xs
        k    +(k)
        acc  (add acc (shift (scale b i.xs) k))
      ==
    ::    +shift:  multiply by x^k
    ::
    ::  [a=zol k=@ud] -> zol, prepending k zero coefficients.
    ::  shift(~, k) = ~, since 0 * x^k = 0.  Never crashes.
    ++  shift
      |=  [a=zol k=@ud]
      ^-  zol
      ?~  a  ~
      =/  out=zol  a
      =/  i=@ud    k
      |-  ^-  zol
      ?:  =(0 i)  out
      $(i (dec i), out [--0 out])
    ::    +scale:  multiply by a scalar
    ::
    ::  [a=zol c=@s] -> zol.  scale(a, --0) = ~.  Otherwise Z is an integral
    ::  domain, so no coefficient becomes zero and the canonical form is
    ::  preserved.  Never crashes.
    ++  scale
      |=  [a=zol c=@s]
      ^-  zol
      ?:  =(--0 c)  ~
      (turn a |=(d=@s (pro:si c d)))
    ::    +eval:  evaluate at an integer point
    ::
    ::  [a=zol x=@s] -> @s.  Horner's rule, from the highest coefficient
    ::  down.  eval(~, x) = --0.  Never crashes.
    ++  eval
      |=  [a=zol x=@s]
      ^-  @s
      =/  r=zol   (flop a)
      =/  acc=@s  --0
      |-  ^-  @s
      ?~  r  acc
      $(r t.r, acc (sum:si (pro:si acc x) i.r))
    ::    +pdiv:  pseudo-division in Z[x]
    ::
    ::  [a=zol b=zol] -> [q=zol r=zol] satisfying the pseudo-division
    ::  identity lc(b)^(deg a - deg b + 1) * a = q*b + r, with r = ~ or
    ::  deg r < deg b.  Z is not a field, so exact division is unavailable;
    ::  premultiplying by that power of lc(b) makes every step divisible.
    ::
    ::  The exponent is pinned to exactly (deg a - deg b + 1) (SPEC S9), and
    ::  the identity then determines q and r uniquely, which is what makes
    ::  the arm `free` despite the pinned scaling.
    ::
    ::  For deg a < deg b the exponent is 0, so the identity reads a = r and
    ::  the product is [~ a].
    ::
    ::  Crashes on b = ~ (SPEC S8).
    ++  pdiv
      ~/  %pdiv
      |=  [a=zol b=zol]
      ^-  [q=zol r=zol]
      ?~  b  !!
      =/  db=@ud  (deg b)
      =/  lb=@s   (lc b)
      ?~  a  [~ ~]
      =/  da=@ud  (deg a)
      ?:  (lth da db)  [~ a]
      ::  premultiply once, up front, by the pinned power
      =/  e=@ud   +((^sub da db))
      =/  q=zol   ~
      =/  r=zol   (scale a (pows:pv lb e))
      =/  i=@ud   e
      |-  ^-  [q=zol r=zol]
      ?~  r  [q ~]
      =/  dr=@ud  (deg r)
      ?:  (lth dr db)  [q r]
      ::  every coefficient of r still carries a factor of lb^i, so this
      ::  division is exact; the loop runs at most e times
      ?:  =(0 i)  [q r]
      =/  k=@ud   (^sub dr db)
      =/  c=@s    (fra:si (lc r) lb)
      %=  $
        i  (dec i)
        q  (add q (shift ~[c] k))
        r  (sub r (shift (scale b c) k))
      ==
    ::    +content:  the content of a Z[x] polynomial
    ::
    ::  [a=zol] -> @ud.  SPEC S7: content(~) = 0; otherwise the gcd of the
    ::  absolute values of the coefficients, always >= 0.  Never crashes.
    ++  content
      |=  a=zol
      ^-  @ud
      =/  cs=zol  a
      =/  g=@ud   0
      |-  ^-  @ud
      ?~  cs  g
      $(cs t.cs, g (gcd:nz g (abs:si i.cs)))
    ::    +pp:  the primitive part of a Z[x] polynomial
    ::
    ::  [a=zol] -> zol.  SPEC S7: pp(~) = ~, and content * pp = input
    ::  exactly, so pp carries the input's sign.  Never crashes.
    ++  pp
      |=  a=zol
      ^-  zol
      ?~  a  ~
      (zdiv:pv a (sun:si (content a)))
    ::    +gcd:  greatest common divisor in Z[x]
    ::
    ::  [a=zol b=zol] -> zol.  SPEC S7: gcd(cont a, cont b) * G, where G is
    ::  the primitive gcd with positive leading coefficient.  gcd(~, ~) = ~;
    ::  gcd(a, ~) = a normalized to positive lc.
    ::
    ::  Spec procedure pinned by SPEC S9 (modular, small-primes / Brown):
    ::  strip content, scan odd primes ascending skipping those dividing
    ::  lc(a')*lc(b'), take the monic image gcd in +mx p, track minimal
    ::  degree and restart accumulation on a strictly smaller one, CRT
    ::  coefficientwise with a symmetric lift, scale to gcd(lc a', lc b')
    ::  before lifting (Brown's correction), take pp, force lc > 0.
    ::
    ::  The result is CERTIFIED by trial division into both primitive parts,
    ::  looping with more primes until it divides both.  Certification is
    ::  what makes this `free` rather than pinned: the product is the true
    ::  gcd regardless of which primes a jet happens to choose.
    ++  gcd
      ~/  %gcd
      |=  [a=zol b=zol]
      ^-  zol
      ::  The zero polynomial is the additive identity of the gcd.  SPEC S7
      ::  fixes gcd(a, ~) = a normalized to positive lc -- the WHOLE
      ::  polynomial, not its primitive part: content(~) = 0, so
      ::  gcd(cont a, 0) = cont a, and cont a * pp a is a again.
      ?~  a
        ?~  b  ~
        ?:((syn:si (lc b)) b (neg b))
      ?~  b
        ?:((syn:si (lc a)) a (neg a))
      =/  ca=@ud  (content a)
      =/  cb=@ud  (content b)
      =/  cg=@ud  (gcd:nz ca cb)
      =/  ap=zol  (pp a)
      =/  bp=zol  (pp b)
      =/  la=@s   (lc ap)
      =/  lb=@s   (lc bp)
      ::  Brown's leading-coefficient correction target
      =/  lg=@ud  (gcd:nz (abs:si la) (abs:si lb))
      =/  bound=@ud  (min (deg ap) (deg bp))
      ::  accumulator: CRT modulus, the lifted candidate, and its degree
      =/  m=@ud      0
      =/  acc=zol    ~
      =/  best=@ud   +(bound)
      =/  p=@ud      3
      |-  ^-  zol
      ::  a gcd of degree 0 is a unit, so the answer is the content alone
      ?:  ?&(!=(0 m) =(0 best))  (scale ~[--1] (sun:si cg))
      ?.  (is-prime:nz p)  $(p (^add p 2))
      ?:  =(0 (mod (abs:si (pro:si la lb)) p))  $(p (^add p 2))
      =/  dr  ~(. mx p)
      =/  ga=mol  (zmod:pv ap p)
      =/  gb=mol  (zmod:pv bp p)
      =/  gi=mol  (gcd:dr ga gb)
      ::  an image gcd of ~ cannot happen: both images are nonzero here
      ?~  gi  $(p (^add p 2))
      =/  di=@ud  (dec (lent gi))
      ::  scale the monic image to Brown's target leading coefficient
      =/  gs=mol  (scale:dr gi (mod lg p))
      ?:  (gth di best)
        ::  unlucky prime: its image degree is too large, discard it
        $(p (^add p 2))
      =/  nm=@ud   ?:((lth di best) p (^mul m p))
      =/  na=zol   ?:((lth di best) (lift gs p) (crt-lift acc m gs p))
      =/  cand=zol
        =/  q=zol  (pp na)
        ?:((syn:si (lc q)) q (neg q))
      ?:  ?&  ?!(=(~ cand))
              =(~ r:(pdiv ap cand))
              =(~ r:(pdiv bp cand))
          ==
        (scale cand (sun:si cg))
      $(p (^add p 2), m nm, acc na, best di)
    ::    +lift:  symmetric lift of a (Z/m)[x] polynomial into Z[x]
    ::
    ::  [a=mol m=@ud] -> zol, each coefficient mapped into (-m/2, m/2].
    ++  lift
      |=  [a=mol m=@ud]
      ^-  zol
      %-  canon
      %+  turn  a
      |=  c=@ud
      ^-  @s
      ?:  (gth (^mul 2 c) m)  (dif:si --0 (sun:si (^sub m c)))
      (sun:si c)
    ::    +crt-lift:  merge a new image into the CRT accumulator
    ::
    ::  [acc=zol m=@ud gs=mol p=@ud] -> zol, the symmetric lift of the
    ::  coefficientwise CRT of .acc modulo .m with .gs modulo .p.
    ++  crt-lift
      |=  [acc=zol m=@ud gs=mol p=@ud]
      ^-  zol
      =/  mm=@ud  (^mul m p)
      =/  xs=zol  acc
      =/  ys=mol  gs
      =|  out=zol
      |-  ^-  zol
      ?:  ?&(=(~ xs) =(~ ys))  (canon (flop out))
      =/  x=@s    ?~(xs --0 i.xs)
      =/  y=@ud   ?~(ys 0 i.ys)
      ::  reduce the accumulated coefficient into [0, m) before combining
      =/  xr=@ud
        =/  v=@ud  (mod (abs:si x) m)
        ?:((syn:si x) v (mod (^sub m v) m))
      =/  c  (crt:nz ~[[xr m] [y p]])
      =/  z=@s
        ?:  (gth (^mul 2 r.c) mm)  (dif:si --0 (sun:si (^sub mm r.c)))
        (sun:si r.c)
      $(xs ?~(xs ~ t.xs), ys ?~(ys ~ t.ys), out [z out])
    ::    +res:  resultant in Z[x]
    ::
    ::  [a=zol b=zol] -> @s.  Subresultant PRS (vzGG S6.10-6.11).
    ::  SPEC S9: res is --0 if either argument is ~; for deg a = 0 the
    ::  convention res(a, b) = lc(a)^(deg b) is pinned, and symmetrically.
    ::  Never crashes.
    ++  res
      ~/  %res
      |=  [a=zol b=zol]
      ^-  @s
      ?~  a  --0
      ?~  b  --0
      =/  da=@ud  (deg a)
      =/  db=@ud  (deg b)
      ?:  =(0 da)  (pows:pv (lc a) db)
      ?:  =(0 db)  (pows:pv (lc b) da)
      ::  The subresultant recurrence below requires deg r0 >= deg r1, which
      ::  the loop then maintains.  Restore it here with the Sylvester
      ::  identity res(a, b) = (-1)^(deg a * deg b) * res(b, a); the sign is
      ::  -1 exactly when both degrees are odd.
      ::
      ::  NOTE: sympy.resultant does NOT satisfy this -- it normalizes its
      ::  arguments by degree, so it returns res(b, a) unchanged when
      ::  deg a < deg b.  The Sylvester determinant is the definition and is
      ::  what tools/genvec.py uses.
      ?:  (lth da db)
        =/  r=@s  $(a b, b a)
        ?:  ?&(=(1 (mod da 2)) =(1 (mod db 2)))  (dif:si --0 r)
        r
      =/  r0=zol  a
      =/  r1=zol  b
      =/  g=@s    --1
      =/  h=@s    --1
      =/  s=@s    --1
      |-  ^-  @s
      =/  d0=@ud  (deg r0)
      =/  d1=@ud  (deg r1)
      =/  k=@ud   (^sub d0 d1)
      ::  sign flip from swapping the arguments, per the Euclidean identity
      =/  sn=@s
        ?:  ?&(=(1 (mod d0 2)) =(1 (mod d1 2)))  (dif:si --0 s)
        s
      =/  pr  (pdiv r0 r1)
      =/  r2=zol  r.pr
      ?~  r2  --0
      =/  d2=@ud  (deg r2)
      ::  subresultant reduction: divide out g*h^k, exact by the theory
      =/  den=@s  (pro:si g (pows:pv h k))
      =/  r3=zol  (zdiv:pv r2 den)
      =/  ng=@s   (lc r1)
      =/  nh=@s
        ?:  =(0 k)  h
        (fra:si (pows:pv ng k) (pows:pv h (dec k)))
      ?:  =(0 d2)
        ::  the last nonzero remainder is a constant: finish the recurrence
        =/  e=@ud  d1
        =/  c=@s   (lc r3)
        ?:  =(1 e)  (pro:si sn c)
        (pro:si sn (fra:si (pows:pv c e) (pows:pv nh (dec e))))
      %=  $
        r0  r1
        r1  r3
        g   ng
        h   nh
        s   sn
      ==
    ::    +disc:  discriminant in Z[x]
    ::
    ::  [a=zol] -> @s, equal to (-1)^(n(n-1)/2) * res(a, a') / lc(a) with
    ::  n = deg a.  The division is exact.  Crashes on deg a < 1 (SPEC S9),
    ::  which includes the zero polynomial through +deg.
    ++  disc
      |=  a=zol
      ^-  @s
      =/  n=@ud  (deg a)
      ?>  (gte n 1)
      =/  r=@s   (res a (zderiv:pv a))
      =/  q=@s   (fra:si r (lc a))
      ?:  =(0 (mod (^div (^mul n (dec n)) 2) 2))  q
      (dif:si --0 q)
    ::    +mig:  Landau-Mignotte factor-coefficient bound
    ::
    ::  [a=zol] -> @ud.  Pinned formula (SPEC S7): for f of degree n with
    ::  maximum absolute coefficient A, B(f) = 2^n * (isqrt(n+1) + 1) * A.
    ::  Sufficient, not tight.  mig(~) = 0.
    ++  mig
      |=  a=zol
      ^-  @ud
      ?~  a  0
      =/  n=@ud  (deg a)
      =/  m=@ud
        =/  cs=zol  a
        =/  x=@ud   0
        |-  ^-  @ud
        ?~  cs  x
        $(cs t.cs, x (max x (abs:si i.cs)))
      (^mul (^mul (bex n) +((isqrt:nz +(n)))) m)
    --
  ::    +mx:  (Z/n)[x] and Z/n scalars; a door on the modulus
  ::
  ::  Scalars are @ud in [0, n); polynomials are dense little-endian with no
  ::  trailing zero coefficient.  One door serves both Z/n and F_p; the
  ::  field-only arms of Phase 3 assert primality at runtime.
  ::
  ::  Precondition n >= 2 on every arm.  Per SPEC S2.6 and S8 this is NOT
  ::  asserted: n < 2 is outside the supported domain, where the Hoon
  ::  computes whatever it deterministically computes and a Milestone B jet
  ::  detects the violation and falls back.
  ::
  ::  Z/n is NOT an integral domain for composite n, so unlike +zx a product
  ::  of nonzero values can be zero -- 2 * 3 = 0 mod 6.  Every arm that
  ::  multiplies must therefore canonicalize its product.  This is the one
  ::  place where the +zx and +mx implementations genuinely differ, rather
  ::  than differing only in coefficient type.
  ::
  ::  Phase 1 arithmetic below.  Phase 2 adds divmod, gcd, egcd, and powmod;
  ::  Phase 3 adds sqfree, ddf, edf, and factor.
  ++  mx
    ~/  %mx
    |_  n=@ud
    ::    +cadd:  addition in Z/n
    ::
    ::  [a=@ud b=@ud] -> @ud in [0, n).  Never crashes.
    ++  cadd
      |=  [a=@ud b=@ud]
      ^-  @ud
      (mod (^add a b) n)
    ::    +csub:  subtraction in Z/n
    ::
    ::  [a=@ud b=@ud] -> @ud in [0, n).  Adds n before subtracting, so the
    ::  intermediate never underflows for canonical inputs.  Never crashes.
    ++  csub
      |=  [a=@ud b=@ud]
      ^-  @ud
      (mod (^sub (^add a n) b) n)
    ::    +cmul:  multiplication in Z/n
    ::
    ::  [a=@ud b=@ud] -> @ud in [0, n).  Never crashes.
    ++  cmul
      |=  [a=@ud b=@ud]
      ^-  @ud
      (mod (^mul a b) n)
    ::    +cneg:  additive inverse in Z/n
    ::
    ::  [a=@ud] -> @ud in [0, n).  cneg(0) = 0.  Never crashes.
    ++  cneg
      |=  a=@ud
      ^-  @ud
      (mod (^sub n a) n)
    ::    +cinv:  multiplicative inverse in Z/n
    ::
    ::  [a=@ud] -> @ud in [0, n), the unique b with a*b = 1 mod n.
    ::  Crashes on a non-unit, which includes 0 (SPEC S8): +egcd produces
    ::  d = n for a = 0, and n >= 2, so the unit check rejects it.
    ++  cinv
      |=  a=@ud
      ^-  @ud
      =/  e  (egcd:nz a n)
      ?>  =(1 d.e)
      ::  u*a = 1 mod n; the EEA bound |u| <= n/2 keeps +dul safe
      (dul:si u.e n)
    ::    +cpow:  exponentiation in Z/n
    ::
    ::  [a=@ud e=@ud] -> @ud in [0, n).  Binary left-to-right
    ::  square-and-multiply (S7).  0^0 = 1, pinned, no crash (S8).
    ++  cpow
      |=  [a=@ud e=@ud]
      ^-  @ud
      (powm:pv a e n)
    ::    +canon:  impose the canonical form
    ::
    ::  [a=mol] -> mol.  Strips every trailing zero coefficient.  The only
    ::  arm that accepts non-canonical input.  Never crashes.
    ++  canon
      |=  a=mol
      ^-  mol
      =/  r=mol  (flop a)
      |-  ^-  mol
      ?~  r  ~
      ?:  =(0 i.r)  $(r t.r)
      (flop r)
    ::    +is-zero:  is this the zero polynomial?
    ::
    ::  [a=mol] -> ?.  Never crashes.
    ++  is-zero
      |=  a=mol
      ^-  ?
      =(~ a)
    ::    +deg:  degree
    ::
    ::  [a=mol] -> @ud.  Crashes on ~ (SPEC S8).
    ++  deg
      |=  a=mol
      ^-  @ud
      ?~  a  !!
      (dec (lent a))
    ::    +lc:  leading coefficient
    ::
    ::  [a=mol] -> @ud, nonzero by the canonical form.  Crashes on ~ (S8).
    ++  lc
      |=  a=mol
      ^-  @ud
      ?~  a  !!
      |-  ^-  @ud
      ?~  t.a  i.a
      $(a t.a)
    ::    +pcmp:  total order on (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> ord.  SPEC S7: shorter list first, so ~ is least;
    ::  at equal length compare coefficients numerically from the highest
    ::  index down.  Never crashes.
    ++  pcmp
      |=  [a=mol b=mol]
      ^-  ord
      =/  la=@ud  (lent a)
      =/  lb=@ud  (lent b)
      ?:  (lth la lb)  %lt
      ?:  (gth la lb)  %gt
      =/  ra=mol  (flop a)
      =/  rb=mol  (flop b)
      |-  ^-  ord
      ?~  ra  %eq
      ?~  rb  %eq
      ?:  (lth i.ra i.rb)  %lt
      ?:  (gth i.ra i.rb)  %gt
      $(ra t.ra, rb t.rb)
    ::    +add:  addition in (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> mol.  Coefficientwise; canonicalized, since leading
    ::  terms can cancel.  Never crashes.
    ++  add
      |=  [a=mol b=mol]
      ^-  mol
      %-  canon
      |-  ^-  mol
      ?~  a  b
      ?~  b  a
      [(cadd i.a i.b) $(a t.a, b t.b)]
    ::    +neg:  additive inverse in (Z/n)[x]
    ::
    ::  [a=mol] -> mol.  For canonical input the leading coefficient is in
    ::  (0, n), so its negation is too, and the canonical form is preserved.
    ::  Never crashes.
    ++  neg
      |=  a=mol
      ^-  mol
      (turn a |=(c=@ud (cneg c)))
    ::    +sub:  subtraction in (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> mol.  Never crashes.
    ++  sub
      |=  [a=mol b=mol]
      ^-  mol
      (add a (neg b))
    ::    +mul:  multiplication in (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> mol.  Classical convolution, as a sum of shifted
    ::  scalar multiples of b.  Unlike +mul:zx the product MUST be
    ::  canonicalized: for composite n the leading coefficient can vanish,
    ::  as (2x)(3x) = 0 mod 6.  +add and +scale each canonicalize, so the
    ::  accumulator is canonical at every step.
    ::  mul(~, b) = mul(a, ~) = ~.  Never crashes.
    ++  mul
      ~/  %mul
      |=  [a=mol b=mol]
      ^-  mol
      ?~  a  ~
      ?~  b  ~
      =/  xs=mol   a
      =/  acc=mol  ~
      =/  k=@ud    0
      |-  ^-  mol
      ?~  xs  acc
      %=  $
        xs   t.xs
        k    +(k)
        acc  (add acc (shift (scale b i.xs) k))
      ==
    ::    +shift:  multiply by x^k
    ::
    ::  [a=mol k=@ud] -> mol, prepending k zero coefficients.
    ::  shift(~, k) = ~.  Never crashes.
    ++  shift
      |=  [a=mol k=@ud]
      ^-  mol
      ?~  a  ~
      =/  out=mol  a
      =/  i=@ud    k
      |-  ^-  mol
      ?:  =(0 i)  out
      $(i (dec i), out [0 out])
    ::    +scale:  multiply by a scalar
    ::
    ::  [a=mol c=@ud] -> mol.  Canonicalized: c = 0 collapses to ~, and for
    ::  composite n a nonzero c can still annihilate the leading
    ::  coefficient.  Never crashes.
    ++  scale
      |=  [a=mol c=@ud]
      ^-  mol
      ?:  =(0 c)  ~
      %-  canon
      (turn a |=(d=@ud (cmul c d)))
    ::    +eval:  evaluate at a point of Z/n
    ::
    ::  [a=mol x=@ud] -> @ud in [0, n).  Horner's rule, from the highest
    ::  coefficient down.  eval(~, x) = 0.  Never crashes.
    ++  eval
      |=  [a=mol x=@ud]
      ^-  @ud
      =/  r=mol    (flop a)
      =/  acc=@ud  0
      |-  ^-  @ud
      ?~  r  acc
      $(r t.r, acc (cadd (cmul acc x) i.r))
    ::    +divmod:  division with remainder in (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> [q=mol r=mol] with a = q*b + r and either r = ~ or
    ::  deg r < deg b.  Schoolbook division, scaling through cinv(lc b).
    ::
    ::  Crashes on b = ~, and on lc(b) not a unit mod n (SPEC S8).  The
    ::  second crash is +cinv's, and it is taken BEFORE the early return for
    ::  deg a < deg b, so that a non-unit divisor crashes unconditionally
    ::  rather than only when the division would do work.
    ::
    ::  Termination: the scaling factor is lc(r)*cinv(lc b), so the leading
    ::  terms cancel exactly and deg r strictly decreases each round.  That
    ::  factor is never 0 -- cinv(lc b) is a unit, so lc(r)*cinv(lc b) = 0
    ::  would force lc(r) = 0, which the canonical form forbids.
    ++  divmod
      ~/  %divmod
      |=  [a=mol b=mol]
      ^-  [q=mol r=mol]
      ?~  b  !!
      =/  bi=@ud  (cinv (lc b))
      =/  db=@ud  (deg b)
      =/  q=mol   ~
      =/  r=mol   a
      |-  ^-  [q=mol r=mol]
      ?~  r  [q ~]
      =/  dr=@ud  (deg r)
      ?:  (lth dr db)  [q r]
      ::  ^sub: bare `sub` is this core's polynomial subtraction
      =/  k=@ud   (^sub dr db)
      =/  c=@ud   (cmul (lc r) bi)
      %=  $
        q  (add q (shift ~[c] k))
        r  (sub r (shift (scale b c) k))
      ==
    ::    +gcd:  greatest common divisor in (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> mol.  Euclid, with monic normalization at the end.
    ::  SPEC S7: gcd(~, ~) = ~ and gcd(a, ~) = monic(a).
    ::
    ::  Well defined over a field.  For composite n the Euclidean algorithm
    ::  is not: it crashes through +divmod as soon as a remainder has a
    ::  non-unit leading coefficient.
    ++  gcd
      ~/  %gcd
      |=  [a=mol b=mol]
      ^-  mol
      =/  x=mol  a
      =/  y=mol  b
      |-  ^-  mol
      ?~  y
        ?~  x  ~
        (scale x (cinv (lc x)))
      $(x y, y r:(divmod x y))
    ::    +egcd:  extended Euclidean algorithm in (Z/n)[x]
    ::
    ::  [a=mol b=mol] -> [g=mol u=mol v=mol] with g = u*a + v*b, g monic.
    ::  Algorithm pinned (SPEC S7): textbook EEA, with the cofactors scaled
    ::  by the inverse of the final remainder's leading coefficient.
    ::
    ::  egcd(~, ~) = [~ ~[1] ~]: there is no final remainder to invert, so
    ::  the cofactors are left unscaled.  The identity still holds.
    ++  egcd
      ~/  %egcd
      |=  [a=mol b=mol]
      ^-  [g=mol u=mol v=mol]
      =/  r0=mol  a     =/  r1=mol  b
      =/  s0=mol  ~[1]  =/  s1=mol  ~
      =/  t0=mol  ~     =/  t1=mol  ~[1]
      |-  ^-  [g=mol u=mol v=mol]
      ?^  r1
        =/  dm  (divmod r0 r1)
        %=  $
          r0  r1
          r1  r.dm
          s0  s1
          s1  (sub s0 (mul q.dm s1))
          t0  t1
          t1  (sub t0 (mul q.dm t1))
        ==
      ?~  r0  [~ s0 t0]
      =/  c=@ud  (cinv (lc r0))
      [(scale r0 c) (scale s0 c) (scale t0 c)]
    ::    +powmod:  modular exponentiation in (Z/n)[x]
    ::
    ::  [a=mol e=@ud f=mol] -> mol, the class of a^e modulo f.  Reduces a
    ::  mod f first, then squares and multiplies with a reduction at every
    ::  step, so intermediate degrees stay below deg f.
    ::
    ::  Crashes on f = ~ and on deg f < 1 (SPEC S8).
    ++  powmod
      ~/  %powmod
      |=  [a=mol e=@ud f=mol]
      ^-  mol
      ?~  f  !!
      ?>  (gte (deg f) 1)
      =/  bb=mol  r:(divmod a f)
      ?:  =(0 e)  r:(divmod ~[1] f)
      =/  k=@ud    (dec (met 0 e))
      =/  acc=mol  bb
      |-  ^-  mol
      ?:  =(0 k)  acc
      =/  nk=@ud  (dec k)
      =/  sq=mol  r:(divmod (mul acc acc) f)
      %=  $
        k    nk
        acc  ?:(=(1 (cut 0 [nk 1] e)) r:(divmod (mul sq bb) f) sq)
      ==
    --
  ::    +qx:  Q[x]
  ::
  ::  Dense little-endian polynomials over the rationals, coefficients
  ::  canonical $frac, no trailing zero coefficient.  Q is a field, so
  ::  division is exact and +gcd is monic.
  ::
  ::  Phase 2.  Where SPEC S9 allows it, the heavy arms clear denominators
  ::  and delegate to +zx rather than running Euclid over $frac directly:
  ::  rational coefficient swell is the classic failure mode, and +gcd:zx
  ::  is modular and certified.
  ++  qx
    ~/  %qx
    |%
    ::    +canon:  impose the canonical form
    ::
    ::  [a=qol] -> qol.  Strips every trailing zero coefficient.  The only
    ::  arm that accepts non-canonical input.  Never crashes.
    ++  canon
      |=  a=qol
      ^-  qol
      =/  r=qol  (flop a)
      |-  ^-  qol
      ?~  r  ~
      ?:  =(--0 p.i.r)  $(r t.r)
      (flop r)
    ::    +is-zero:  is this the zero polynomial?
    ++  is-zero
      |=  a=qol
      ^-  ?
      =(~ a)
    ::    +deg:  degree.  Crashes on ~ (SPEC S8).
    ++  deg
      |=  a=qol
      ^-  @ud
      ?~  a  !!
      (dec (lent a))
    ::    +lc:  leading coefficient.  Crashes on ~ (SPEC S8).
    ++  lc
      |=  a=qol
      ^-  frac
      ?~  a  !!
      |-  ^-  frac
      ?~  t.a  i.a
      $(a t.a)
    ::    +pcmp:  total order on Q[x]
    ::
    ::  [a=qol b=qol] -> ord.  SPEC S7: shorter list first, so ~ is least;
    ::  at equal length compare from the highest index down, delegating to
    ::  +cmp:qq rather than reimplementing the cross-multiplication.
    ++  pcmp
      |=  [a=qol b=qol]
      ^-  ord
      =/  la=@ud  (lent a)
      =/  lb=@ud  (lent b)
      ?:  (lth la lb)  %lt
      ?:  (gth la lb)  %gt
      =/  ra=qol  (flop a)
      =/  rb=qol  (flop b)
      |-  ^-  ord
      ?~  ra  %eq
      ?~  rb  %eq
      =/  c=ord  (cmp:qq i.ra i.rb)
      ?:  =(%eq c)  $(ra t.ra, rb t.rb)
      c
    ::    +add:  addition in Q[x].  Canonicalized: terms can cancel.
    ++  add
      |=  [a=qol b=qol]
      ^-  qol
      %-  canon
      |-  ^-  qol
      ?~  a  b
      ?~  b  a
      [(add:qq i.a i.b) $(a t.a, b t.b)]
    ::    +neg:  additive inverse in Q[x]
    ::
    ::  Negation preserves the canonical form: a nonzero frac negates to a
    ::  nonzero frac.
    ++  neg
      |=  a=qol
      ^-  qol
      (turn a neg:qq)
    ::    +sub:  subtraction in Q[x]
    ++  sub
      |=  [a=qol b=qol]
      ^-  qol
      (add a (neg b))
    ::    +mul:  multiplication in Q[x]
    ::
    ::  Classical convolution.  Q is a field, hence an integral domain, so
    ::  the leading term cannot cancel and no canonicalization is needed --
    ::  as in +zx, and unlike +mx over composite n.
    ++  mul
      ~/  %mul
      |=  [a=qol b=qol]
      ^-  qol
      ?~  a  ~
      ?~  b  ~
      =/  xs=qol   a
      =/  acc=qol  ~
      =/  k=@ud    0
      |-  ^-  qol
      ?~  xs  acc
      %=  $
        xs   t.xs
        k    +(k)
        acc  (add acc (shift (scale b i.xs) k))
      ==
    ::    +shift:  multiply by x^k
    ++  shift
      |=  [a=qol k=@ud]
      ^-  qol
      ?~  a  ~
      =/  out=qol  a
      =/  i=@ud    k
      |-  ^-  qol
      ?:  =(0 i)  out
      $(i (dec i), out [zero:qq out])
    ::    +scale:  multiply by a scalar.  scale(a, 0) = ~.
    ++  scale
      |=  [a=qol c=frac]
      ^-  qol
      ?:  =(--0 p.c)  ~
      (turn a |=(d=frac (mul:qq c d)))
    ::    +eval:  evaluate at a rational point, by Horner's rule
    ++  eval
      |=  [a=qol x=frac]
      ^-  frac
      =/  r=qol     (flop a)
      =/  acc=frac  zero:qq
      |-  ^-  frac
      ?~  r  acc
      $(r t.r, acc (add:qq (mul:qq acc x) i.r))
    ::    +divmod:  division with remainder in Q[x]
    ::
    ::  [a=qol b=qol] -> [q=qol r=qol] with a = q*b + r and r = ~ or
    ::  deg r < deg b.  Schoolbook, dividing through by lc(b), which is
    ::  always invertible since Q is a field.
    ::
    ::  Crashes on b = ~ (SPEC S8), through +lc.
    ++  divmod
      ~/  %divmod
      |=  [a=qol b=qol]
      ^-  [q=qol r=qol]
      ?~  b  !!
      =/  bi=frac  (inv:qq (lc b))
      =/  db=@ud   (deg b)
      =/  q=qol    ~
      =/  r=qol    a
      |-  ^-  [q=qol r=qol]
      ?~  r  [q ~]
      =/  dr=@ud  (deg r)
      ?:  (lth dr db)  [q r]
      =/  k=@ud    (^sub dr db)
      =/  c=frac   (mul:qq (lc r) bi)
      %=  $
        q  (add q (shift ~[c] k))
        r  (sub r (shift (scale b c) k))
      ==
    ::    +gcd:  greatest common divisor in Q[x]
    ::
    ::  [a=qol b=qol] -> qol, monic.  SPEC S7/S9: clear denominators, reduce
    ::  to the primitive gcd in Z[x], and rescale to monic.
    ::
    ::  Delegating to +gcd:zx rather than running Euclid over $frac is the
    ::  point: the Z[x] gcd is modular and trial-division certified, so this
    ::  arm inherits both the certification and the control over coefficient
    ::  swell.  gcd(~, ~) = ~.
    ++  gcd
      ~/  %gcd
      |=  [a=qol b=qol]
      ^-  qol
      ?:  ?&(=(~ a) =(~ b))  ~
      =/  g=zol  (gcd:zx (clear a) (clear b))
      ?~  g  ~
      =/  q=qol  (embed g)
      (scale q (inv:qq (lc q)))
    ::    +clear:  clear denominators, mapping Q[x] into Z[x]
    ::
    ::  [a=qol] -> zol.  Multiplies through by the lcm of the denominators.
    ::  The scaling factor is discarded, which is exactly right for +gcd:
    ::  the product is used only up to a rational unit, and the caller
    ::  rescales to monic.
    ++  clear
      |=  a=qol
      ^-  zol
      ?~  a  ~
      =/  l=@ud
        =/  cs=qol  a
        =/  x=@ud   1
        |-  ^-  @ud
        ?~  cs  x
        $(cs t.cs, x (^div (^mul x q.i.cs) (gcd:nz x q.i.cs)))
      %-  canon:zx
      %+  turn  a
      |=  c=frac
      ^-  @s
      (pro:si p.c (sun:si (^div l q.c)))
    ::    +embed:  the canonical injection of Z[x] into Q[x]
    ++  embed
      |=  a=zol
      ^-  qol
      (turn a |=(c=@s ^-(frac [c 1])))
    --
  --
--
