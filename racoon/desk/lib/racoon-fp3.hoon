  ::  /lib/racoon-fp3
::::  Extension fields F_p[x]/(m), on Racoon
::
::  Arithmetic in a finite field built as a quotient of the polynomial ring
::  over F_p by a monic irreducible modulus.  The motivating case is the
::  cubic F_p[x]/(x^3 - x - 1) over the Goldilocks prime, which is what
::  Nockchain's $felt is -- hence the file name -- but the door is general
::  in the modulus and works at any degree.
::
::  The Nockchain instance:
::
::      =gl3  %~  .  fp3
::            :-  18.446.744.069.414.584.321
::            ~[18.446.744.069.414.584.320 18.446.744.069.414.584.320 0 1]
::
::  that modulus being x^3 - x - 1 written little-endian with -1 reduced
::  into [0, p).  Its irreducibility over Goldilocks was verified, not
::  assumed; +irreducible re-checks it in-ship.
::
::  This is a CONSUMER of /lib/racoon, not part of it.  Racoon has no
::  extension fields by design: +mx is Z/n, and F_p only when n is prime.
::  That is the gap this fills, and it fills it the way the frozen
::  interface intends -- from outside, with +mx polynomial arithmetic.
::
::  ELEMENTS ARE POLYNOMIALS of degree below deg(m), little-endian, with
::  coefficients in [0, p) -- that is, canonical $mol.  The zero element is
::  ~ and the one element is ~[1].  An element whose degree reaches deg(m)
::  is outside the supported domain; +canon is the one arm that reduces.
::
::  PRECONDITIONS, not asserted per-arm: p prime, m monic and IRREDUCIBLE
::  over F_p, deg(m) >= 1.  Reducibility is the dangerous one -- the
::  quotient is then a ring with zero divisors rather than a field, and
::  +inv will crash on those divisors instead of misbehaving silently,
::  which is the honest failure but not a diagnosis.  +irreducible below
::  checks it when a caller wants certainty.
::
/-  *racoon
/+  racoon
=/  nz  nz:racoon
=/  mx  mx:racoon
|_  [p=@ud m=mol]
::    +d:  Racoon's modular polynomial core at the base field
++  d  ~(. mx p)
::    +rank:  the degree of the extension over F_p
++  rank  (deg:d m)
::
::  Constants and coercion.
::
::    +zero:  the additive identity
++  zero  `mol`~
::    +one:  the multiplicative identity
++  one  `mol`~[1]
::    +emb:  embed a base field element
++  emb
  |=  c=@ud
  ^-  mol
  (canon ~[c])
::    +canon:  reduce an arbitrary polynomial into the field
::
::  The only arm accepting arbitrary input.  Everything else assumes its
::  arguments are already field elements.
::
::  Reduces in BOTH senses, and deliberately more than +canon:mx does:
::  coefficients are folded into [0, p) and then the degree is brought
::  below deg(m).  Racoon takes coefficient range as a precondition of the
::  $mol form and its +canon only strips trailing zeros; here this arm is
::  the boundary where outside data enters the field, so it does the whole
::  job rather than half of it.
++  canon
  |=  a=mol
  ^-  mol
  =/  c=mol  (canon:d (turn a |=(x=@ud (mod x p))))
  r:(divmod:d c m)
::    +is-zero:  is this the additive identity?
++  is-zero
  |=  a=mol
  ^-  ?
  =(~ a)
::
::  Field operations.
::
::    +add:  addition
::
::  Degrees never grow, so no reduction is needed -- the sum of two
::  polynomials below degree deg(m) is below degree deg(m).
++  add
  |=  [a=mol b=mol]
  ^-  mol
  (add:d a b)
::    +neg:  additive inverse
++  neg
  |=  a=mol
  ^-  mol
  (neg:d a)
::    +sub:  subtraction
++  sub
  |=  [a=mol b=mol]
  ^-  mol
  (sub:d a b)
::    +mul:  multiplication
::
::  Multiply in F_p[x], then reduce modulo m.  This is the only place the
::  modulus enters the arithmetic, and it is why m must be irreducible: a
::  reducible m would let two nonzero elements multiply to zero.
++  mul
  |=  [a=mol b=mol]
  ^-  mol
  r:(divmod:d (mul:d a b) m)
::    +sqr:  squaring
++  sqr
  |=  a=mol
  ^-  mol
  (mul a a)
::    +scal:  multiply by a base field scalar
++  scal
  |=  [a=mol c=@ud]
  ^-  mol
  (scale:d a (mod c p))
::    +pow:  exponentiation by a natural
::
::  Binary square-and-multiply, reducing at every step.  a^0 is one, for
::  every a including zero.
++  pow
  |=  [a=mol e=@ud]
  ^-  mol
  ?:  =(0 e)  one
  =/  k=@ud    (dec (met 0 e))
  =/  acc=mol  a
  |-  ^-  mol
  ?:  =(0 k)  acc
  =/  nk=@ud  (dec k)
  =/  sq=mol  (mul acc acc)
  %=  $
    k    nk
    acc  ?:(=(1 (cut 0 [nk 1] e)) (mul sq a) sq)
  ==
::    +inv:  multiplicative inverse
::
::  Crashes on zero, which has none.
::
::  By the extended Euclidean algorithm: for a nonzero a of degree below
::  deg(m) and m irreducible, gcd(a, m) = 1, so +egcd:mx yields cofactors
::  with u*a + v*m = 1 and therefore u*a = 1 modulo m.
::
::  Note this uses Racoon's +egcd:mx unchanged and run to COMPLETION --
::  the opposite of /lib/racoon-rs, whose key equation needed the same
::  algorithm stopped early.  Between them the two consumers exercise both
::  halves of that arm's behavior.
++  inv
  |=  a=mol
  ^-  mol
  ?<  =(~ a)
  =/  e  (egcd:d a m)
  ::  irreducible m makes this gcd 1; a composite modulus can fail here,
  ::  which is the honest way to discover a non-unit
  ?>  =(~[1] g.e)
  r:(divmod:d u.e m)
::    +div:  division
::
::  Crashes on a zero divisor.
++  div
  |=  [a=mol b=mol]
  ^-  mol
  (mul a (inv b))
::
::  Field structure.
::
::    +frob:  the Frobenius automorphism, a -> a^p
::
::  Fixes exactly the base field, and its rank-fold composition is the
::  identity -- both checked as properties rather than assumed.
++  frob
  |=  a=mol
  ^-  mol
  (pow a p)
::    +norm:  the field norm down to F_p
::
::  N(a) = a^((p^rank - 1) / (p - 1)), the product of a with all its
::  conjugates.  Multiplicative, and lands in the base field, so the
::  product is a single base field element rather than an extension one.
++  norm
  |=  a=mol
  ^-  @ud
  ?:  =(~ a)  0
  =/  q=@ud
    =/  i=@ud    0
    =/  acc=@ud  0
    |-  ^-  @ud
    ::  ^add and ^mul: the bare names are this door's own field arithmetic
    ?:  =(i rank)  acc
    $(i +(i), acc (^add (^mul acc p) 1))
  =/  r=mol  (pow a q)
  ?~  r  0
  i.r
::    +irreducible:  is the modulus irreducible over F_p?
::
::  Not called by the arithmetic -- irreducibility is a precondition, and
::  checking it on every operation would be absurd.  Exposed so that a
::  caller instantiating a new modulus can verify it once, up front.
::  Delegates to Racoon's certified factorization.
++  irreducible
  ^-  ?
  ?:  (lth rank 1)  %.n
  ?.  (is-prime:nz p)  %.n
  =/  fc  (factor:d m)
  ?~  fs.fc  %.n
  ?.  =(~ t.fs.fc)  %.n
  =(rank (deg:d p.i.fs.fc))
--
