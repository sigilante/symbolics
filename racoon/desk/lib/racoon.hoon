  ::  /lib/racoon
::::  Racoon, Real AlgebraiCs in hOON
::
::  A deterministic computer algebra kernel: exact arithmetic over Z, Q, and
::  Z/n, and univariate polynomial arithmetic over each.  This library is the
::  specification; native jets must be Kleene-equal to it on every input.
::
::  Phase 0: scalars and number theory (+nz, +qq).
::
::  Jet registration mirrors urbit/numerics /lib/math.hoon: the root ~% nests
::  under %non, each sub-core carries ~/ with its own name, and the arms
::  listed in SPEC S10 carry per-arm ~/ hints.
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
    ?:  =(1 m)  0
    ?:  =(0 e)  (mod 1 m)
    =/  bb=@ud   (mod b m)
    =/  k=@ud    (dec (met 0 e))
    =/  acc=@ud  bb
    |-  ^-  @ud
    ?:  =(0 k)  acc
    =/  nk=@ud  (dec k)
    =/  sq=@ud  (mod (mul acc acc) m)
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
    =/  s=@ud  0
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
  --
--
