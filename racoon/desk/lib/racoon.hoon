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
    --
  ::    +qx:  Q[x].  Phase 2.
  ++  qx
    ~/  %qx
    |%
    --
  --
--
