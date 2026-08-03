  ::  /lib/racoon-zfac
::::  Integer factorization, and what it unlocks
::
::  Racoon factors POLYNOMIALS but not integers: +nz is gcd, egcd, isqrt,
::  is-prime, crt, ratrec, and nothing else.  That gap blocks the
::  multiplicative order of a unit, primitive roots, Euler's totient, and
::  the divisor set -- all of which are downstream of a factorization and
::  none of which are expressible without one.
::
::  This is a CONSUMER of /lib/racoon, not part of it.  +nz froze at six
::  arms under R6, and adding a seventh would move the battery axes of the
::  five that Milestone B jets resolve against.  Nothing inside the frozen
::  library calls this, so nothing needs it there; the pattern is
::  /lib/racoon-rs and /lib/racoon-fp3, and Baloon's resolved question B2.
::  Promote it into +nz if a Racoon Milestone C escalation ever opens that
::  core for a batch of changes -- not before, and not for this alone.
::
::  EVERY ARM HERE IS `free`.  A factorization into primes is unique, so
::  the sorted output is canonical no matter how it was found, and a jet
::  may use Brent, ECM, quadratic sieve, or anything else.  Only the
::  SEARCH is pinned, and only because Hoon has no randomness: Pollard's
::  rho is run with c = 1, 2, 3, ... in order, which makes an unlucky
::  first attempt reproducible rather than merely unlikely.
::
::  TERMINATION IS GUARANTEED, not probabilistic.  Rho may fail on any
::  particular c, so after +tries attempts the search falls back to trial
::  division, which cannot fail on a composite.  A caller waits longer; it
::  never gets a wrong answer or a crash.
::
/-  *racoon
/+  racoon
=/  nz  nz:racoon
=/  mx  mx:racoon
|%
+|  %private
::    +cap:  trial-division bound, pinned
::
::  Every prime below this is stripped by division before rho is tried,
::  which is both faster than rho at that size and what makes the rho
::  stage safe: its cofactor has no small factor, so the degenerate cases
::  (4, 8, and the like) cannot reach it.
++  cap  65.536
::    +tries:  how many rho parameters to try before falling back, pinned
++  tries  32
::    +rho:  Pollard's rho, one attempt at parameter c
::
::  [n=@ud c=@ud] -> (unit @ud), a nontrivial factor of n or ~.
::
::  Floyd cycle detection on x <- x^2 + c mod n.  When the tortoise and
::  the hare meet, the cycle has closed with no factor found and this
::  attempt has failed -- that is the ~, and it is why +split retries with
::  a different c rather than treating ~ as "n is prime".
++  rho
  |=  [n=@ud c=@ud]
  ^-  (unit @ud)
  =/  x=@ud  2
  =/  y=@ud  2
  |-  ^-  (unit @ud)
  =/  nx=@ud  (mod (add (mul x x) c) n)
  =/  ny=@ud
    =/  t=@ud  (mod (add (mul y y) c) n)
    (mod (add (mul t t) c) n)
  ::  the cycle closed without splitting n
  ?:  =(nx ny)  ~
  =/  df=@ud  ?:((gte nx ny) (sub nx ny) (sub ny nx))
  =/  g=@ud   (gcd:nz df n)
  ?:  =(n g)     ~
  ?:  (gth g 1)  `g
  $(x nx, y ny)
::    +grind:  trial division above +cap, the fallback that cannot fail
::
::  [n=@ud] -> @ud.  Returns a proper divisor of a composite n, or n
::  itself when n is prime.  Callers reach it only with a composite.
++  grind
  |=  n=@ud
  ^-  @ud
  =/  d=@ud  ?:(=(0 (mod cap 2)) +(cap) cap)
  |-  ^-  @ud
  ?:  (gth (mul d d) n)  n
  ?:  =(0 (mod n d))     d
  $(d (add d 2))
::    +split:  a nontrivial factor of a composite with no small primes
++  split
  |=  n=@ud
  ^-  @ud
  =/  c=@ud  1
  |-  ^-  @ud
  ?:  (gth c tries)  (grind n)
  =/  r  (rho n c)
  ?~  r  $(c +(c))
  u.r
::    +trial:  strip every prime factor at or below +cap
::
::  [n=@ud] -> [fs=(list @ud) rest=@ud], the factors found in ascending
::  order with multiplicity, and the unfactored cofactor.  rest is 1 when
::  n was fully resolved here.
++  trial
  |=  n=@ud
  ^-  [fs=(list @ud) rest=@ud]
  =/  rest=@ud  n
  =/  d=@ud     2
  =|  fs=(list @ud)
  |-  ^-  [fs=(list @ud) rest=@ud]
  ?:  =(1 rest)          [(flop fs) 1]
  ::  d^2 > rest with nothing found means rest is prime
  ?:  (gth (mul d d) rest)  [(flop [rest fs]) 1]
  ?:  (gth d cap)        [(flop fs) rest]
  ?:  =(0 (mod rest d))  $(rest (div rest d), fs [d fs])
  $(d ?:(=(2 d) 3 (add d 2)))
::    +crack:  the prime factors of a cofactor with no small primes
::
::  Splits and recurses.  +is-prime:nz is Miller-Rabin with a pinned
::  witness schedule, so this terminates on a definite answer at every
::  level rather than on a probabilistic one.
++  crack
  |=  n=@ud
  ^-  (list @ud)
  ?:  =(1 n)            ~
  ?:  (is-prime:nz n)   ~[n]
  =/  d=@ud  (split n)
  (weld (crack d) (crack (div n d)))
::    +group:  a sorted prime list to prime/multiplicity pairs
++  group
  |=  ps=(list @ud)
  ^-  (list [p=@ud m=@ud])
  =|  out=(list [p=@ud m=@ud])
  |-  ^-  (list [p=@ud m=@ud])
  ?~  ps  (flop out)
  ?~  out  $(ps t.ps, out ~[[i.ps 1]])
  ?:  =(p.i.out i.ps)
    $(ps t.ps, out [[p.i.out +(m.i.out)] t.out])
  $(ps t.ps, out [[i.ps 1] out])
::    +expand:  multiply a divisor list by every power of p up to m
++  expand
  |=  [ds=(list @ud) p=@ud m=@ud]
  ^-  (list @ud)
  =/  k=@ud   0
  =/  pw=@ud  1
  =|  acc=(list @ud)
  |-  ^-  (list @ud)
  ?:  (gth k m)  acc
  %=  $
    k    +(k)
    pw   (mul pw p)
    acc  (weld acc (turn ds |=(d=@ud (mul d pw))))
  ==
::
+|  %public
::    +factor:  the prime factorization
::
::  [n=@ud] -> (list [p=@ud m=@ud]), primes strictly ascending with
::  multiplicity at least 1.  Canonical, by unique factorization.
::
::  factor(1) is ~, the empty product, which is the right answer and not
::  an edge case.  factor(0) CRASHES: every prime divides zero, so there
::  is no factorization to return and no sentinel that would not be a lie.
++  factor
  |=  n=@ud
  ^-  (list [p=@ud m=@ud])
  ?<  =(0 n)
  ?:  =(1 n)  ~
  =/  t   (trial n)
  %-  group
  %+  sort  (weld fs.t (crack rest.t))
  lth
::    +is-prime-power:  is n exactly one prime to a positive power?
++  is-prime-power
  |=  n=@ud
  ^-  ?
  ?:  (lth n 2)  %.n
  =(1 (lent (factor n)))
::    +radical:  the product of the distinct prime factors
::
::  radical(1) is 1, the empty product.  Crashes on 0, through +factor.
++  radical
  |=  n=@ud
  ^-  @ud
  =/  fs   (factor n)
  =/  acc=@ud  1
  |-  ^-  @ud
  ?~  fs  acc
  $(fs t.fs, acc (mul acc p.i.fs))
::    +totient:  Euler's totient, the count of units mod n
::
::  phi(n) = prod p^(m-1) * (p - 1) over the factorization.  phi(1) = 1.
::  Crashes on 0, through +factor.
++  totient
  |=  n=@ud
  ^-  @ud
  =/  fs   (factor n)
  =/  acc=@ud  1
  |-  ^-  @ud
  ?~  fs  acc
  =/  q=@ud  (mul (pow p.i.fs (dec m.i.fs)) (dec p.i.fs))
  $(fs t.fs, acc (mul acc q))
::    +divisors:  every divisor, ascending
::
::  divisors(1) is ~[1].  The count is prod (m + 1), which is what the
::  tests check it against.  Crashes on 0, through +factor.
++  divisors
  |=  n=@ud
  ^-  (list @ud)
  =/  fs=(list [p=@ud m=@ud])  (factor n)
  =/  ds=(list @ud)            ~[1]
  |-  ^-  (list @ud)
  ?~  fs  (sort ds lth)
  $(fs t.fs, ds (expand ds p.i.fs m.i.fs))
::    +order:  the multiplicative order of a unit mod n
::
::  [a=@ud n=@ud] -> @ud, the least e > 0 with a^e = 1 mod n.  Requires
::  n >= 2 and gcd(a, n) = 1, both asserted: a non-unit has no order at
::  all, and returning 0 or crashing later would both be worse than
::  saying so here.
::
::  Starts from phi(n), which every order divides, and divides out each
::  prime of phi(n) as far as the power still comes back 1.  That is why
::  this arm needs +factor and could not be written before it: it factors
::  phi(n), not n.
++  order
  |=  [a=@ud n=@ud]
  ^-  @ud
  ?>  (gte n 2)
  =/  b=@ud  (mod a n)
  ?>  =(1 (gcd:nz b n))
  =/  d      ~(. mx n)
  =/  e=@ud  (totient n)
  =/  qs     (factor e)
  |-  ^-  @ud
  ?~  qs  e
  =/  ne=@ud
    =/  cur=@ud  e
    |-  ^-  @ud
    ?.  =(0 (mod cur p.i.qs))                 cur
    ?.  =(1 (cpow:d b (div cur p.i.qs)))      cur
    $(cur (div cur p.i.qs))
  ::  $ and not ^$: the inner loop closed inside its own =/, so the
  ::  nearest |- in scope here is already the outer one
  $(qs t.qs, e ne)
::    +primitive-root:  the least primitive root mod n, if one exists
::
::  [n=@ud] -> (unit @ud).  A generator of the unit group, that is a unit
::  whose order is phi(n).  Produces ~ when the group is not cyclic --
::  which is most n, the cyclic ones being 1, 2, 4, p^k and 2p^k for odd
::  prime p -- rather than crashing, since "there is none" is an ordinary
::  answer here and not a violation.
::
::  Searched ascending, so the product is the LEAST primitive root and is
::  canonical.  Requires n >= 2.
++  primitive-root
  |=  n=@ud
  ^-  (unit @ud)
  ?>  (gte n 2)
  =/  e=@ud  (totient n)
  =/  g=@ud  1
  |-  ^-  (unit @ud)
  ?:  (gte g n)  ~
  ?.  =(1 (gcd:nz g n))    $(g +(g))
  ?:  =(e (order g n))     `g
  $(g +(g))
--
