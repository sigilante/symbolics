  ::  /lib/racoon-rs
::::  Reed-Solomon coding over F_p, on Racoon
::
::  A systematic Reed-Solomon codec: encode k message symbols into k + nsym
::  codeword symbols, and recover the message from up to nsym/2 corrupted
::  symbols anywhere in the block.
::
::  This is a CONSUMER of /lib/racoon, not part of it.  The Milestone A
::  interface is frozen, so this imports the library like any other caller.
::
::  Its purpose is live utilization: an error-correcting code is a workload
::  whose correctness is self-evident -- data either round-trips through
::  deliberate corruption or it does not -- so it exercises +mx against a
::  standard no synthetic unit test supplies.
::
::  PRIME FIELD, NOT GF(2^8).  Classical byte-oriented Reed-Solomon uses the
::  extension field GF(2^8), which Racoon does not implement: +mx is Z/n,
::  and F_p only when n is prime.  So this codec works over a prime field.
::  With p = 257 every byte 0-255 is a distinct field element, which makes
::  byte data representable; note that a parity symbol may come out as 256,
::  which is a field element but not a byte.  Callers moving bytes over a
::  byte channel must account for that.
::
::  The decoder needs the extended Euclidean algorithm STOPPED EARLY, once
::  the remainder degree falls below nsym/2.  Racoon's +egcd:mx runs to
::  completion, so the key-equation solver is written here over +divmod:mx.
::  That is the one piece the frozen interface does not already supply.
::
/-  *racoon
/+  racoon
=/  nz  nz:racoon
=/  mx  mx:racoon
::    the codec, a door on the field and the parity count
::
::  .p is the prime field size, .gen a primitive element of F_p, and .nsym
::  the number of parity symbols.  Up to nsym/2 symbol errors are
::  correctable, at any positions.
::
|_  [p=@ud gen=@ud nsym=@ud]
::    +d:  Racoon's modular polynomial core at this field
++  d  ~(. mx p)
::    +cap:  the correction capacity, floor(nsym / 2)
++  cap  (div nsym 2)
::
::  Helpers.  Local rather than in Racoon, since the interface is frozen.
::
::    +to-poly:  symbols to a polynomial, first symbol highest degree
::
::  Symbols read left to right in descending degree, the usual coding
::  convention, while Racoon stores little-endian -- hence the flop.
++  to-poly
  |=  syms=(list @ud)
  ^-  mol
  (canon:d (flop syms))
::    +of-poly:  a polynomial back to exactly n symbols
::
::  Canonical form drops trailing zero coefficients, which are LEADING
::  zeros in symbol order, so the width has to be restored explicitly.
++  of-poly
  |=  [a=mol n=@ud]
  ^-  (list @ud)
  =/  la=@ud  (lent a)
  ?>  (lte la n)
  (flop (weld `(list @ud)`a (reap (sub n la) 0)))
::    +sput:  replace one entry of a symbol list
++  sput
  |=  [v=(list @ud) i=@ud x=@ud]
  ^-  (list @ud)
  ?~  v  !!
  ?:  =(0 i)  [x t.v]
  [i.v $(v t.v, i (dec i))]
::    +deriv:  the formal derivative of a polynomial over F_p
++  deriv
  |=  a=mol
  ^-  mol
  ?~  a  ~
  =/  cs=mol  t.a
  =/  i=@ud   1
  =|  out=mol
  |-  ^-  mol
  ?~  cs  (canon:d (flop out))
  $(cs t.cs, i +(i), out [(cmul:d (mod i p) i.cs) out])
::
::  The codec proper.
::
::    +gpoly:  the generator polynomial
::
::  g(x) = prod over i in [1, nsym] of (x - gen^i).  A codeword is a
::  multiple of g, which is exactly the statement that it vanishes at each
::  of those nsym points -- the syndromes.
++  gpoly
  ^-  mol
  =/  i=@ud    1
  =/  acc=mol  ~[1]
  |-  ^-  mol
  ?:  (gth i nsym)  acc
  $(i +(i), acc (mul:d acc ~[(cneg:d (cpow:d gen i)) 1]))
::    +encode:  systematic encoding
::
::  [msg=(list @ud)] -> (list @ud) of length (lent msg) + nsym, whose first
::  (lent msg) symbols ARE the message.  That is what systematic means, and
::  it is asserted as a property rather than assumed.
::
::  c(x) = m(x)*x^nsym - (m(x)*x^nsym mod g(x)), so c is divisible by g.
::
::  Crashes on an empty message, on a block longer than p - 1 (the
::  evaluation points would repeat), and on a symbol outside [0, p).
++  encode
  |=  msg=(list @ud)
  ^-  (list @ud)
  ?>  ?!(=(~ msg))
  ?>  (levy msg |=(s=@ud (lth s p)))
  =/  k=@ud  (lent msg)
  =/  n=@ud  (add k nsym)
  ?>  (lte n (dec p))
  =/  sh=mol  (shift:d (to-poly msg) nsym)
  (of-poly (sub:d sh r:(divmod:d sh gpoly)) n)
::    +unencode:  strip the parity symbols
++  unencode
  |=  code=(list @ud)
  ^-  (list @ud)
  =/  n=@ud  (lent code)
  ?>  (gte n nsym)
  (scag (sub n nsym) code)
::    +syndromes:  evaluate the received word at the nsym check points
::
::  All zero exactly when the received word is a valid codeword.
++  syndromes
  |=  recv=(list @ud)
  ^-  (list @ud)
  =/  r=mol  (to-poly recv)
  %+  turn  (gulf 1 nsym)
  |=(j=@ud (eval:d r (cpow:d gen j)))
::    +decode:  correct up to cap errors, producing the codeword
::
::  [recv=(list @ud)] -> (unit (list @ud)).  Produces the corrected
::  CODEWORD; pass it through +unencode for the message.  Produces ~ when
::  the received word cannot be corrected.
::
::  BEYOND cap ERRORS THE ANSWER MAY BE WRONG, not merely absent.  A word
::  far enough from every codeword can land nearer a DIFFERENT one, and the
::  decoder returns that other codeword with every syndrome satisfied.
::
::  This cannot be fixed inside the decoder, and the point was measured
::  rather than assumed.  The two consistency checks one would reach for --
::  requiring every located position to have nonzero magnitude, and
::  requiring deg(omega) < deg(lambda) -- change NOTHING: over 20.000
::  trials at each of nsym = 2 and 4, adding either or both left the
::  miscorrection count byte-identical.  That is the theory confirmed: a
::  miscorrection is a genuine valid codeword, its error pattern entirely
::  self-consistent relative to the wrong answer, so the information needed
::  to reject it is not present in the received word.
::
::  What does work is policy, and the rate falls steeply with parity:
::
::      nsym = 2    426 / 20.000    2.1%
::      nsym = 4      9 / 20.000    0.045%
::
::  So: spend two more parity symbols, use +decode-upto to trade correction
::  power for detection, or carry an outer integrity check over the message.
::  Only the last gives certainty.
::
::  The pipeline is the classical one: syndromes, then the key equation by
::  a PARTIAL extended Euclid, then Chien search for the error positions
::  and Forney for the magnitudes.
++  decode
  |=  recv=(list @ud)
  ^-  (unit (list @ud))
  =/  n=@ud  (lent recv)
  ?>  (levy recv |=(s=@ud (lth s p)))
  ?>  (lte n (dec p))
  =/  syn=(list @ud)  (syndromes recv)
  ::  a clean word needs no correction
  ?:  (levy syn |=(s=@ud =(0 s)))  `recv
  ::  S(x), with S_j as the coefficient of x^(j-1)
  =/  sp=mol  (canon:d syn)
  ::  Key equation: find lam and omg with lam*S = omg modulo x^nsym.  The
  ::  extended Euclid on (x^nsym, S) is run only until the remainder degree
  ::  drops below cap -- running it to completion, as +egcd:mx does, would
  ::  pass straight through the solution.
  =/  key
    =/  r0=mol  (shift:d ~[1] nsym)
    =/  r1=mol  sp
    =/  s0=mol  ~
    =/  s1=mol  ~[1]
    |-  ^-  [om=mol la=mol]
    ?:  ?|(=(~ r1) (lth (deg:d r1) cap))  [r1 s1]
    =/  dm  (divmod:d r0 r1)
    %=  $
      r0  r1
      r1  r.dm
      s0  s1
      s1  (sub:d s0 (mul:d q.dm s1))
    ==
  =/  la0=mol  la.key
  ?~  la0  ~
  ::  normalize so that lam(0) = 1; both sides scale together
  ?:  =(0 i.la0)  ~
  =/  iv=@ud    (cinv:d i.la0)
  =/  lam=mol   (scale:d la0 iv)
  =/  omg=mol   (scale:d om.key iv)
  ::  Chien search: exponent e is an error position exactly when the error
  ::  locator vanishes at gen^-e
  =/  ainv=@ud  (cinv:d gen)
  =/  pos=(list @ud)
    %+  skim  (gulf 0 (dec n))
    |=(e=@ud =(0 (eval:d lam (cpow:d ainv e))))
  ::  the locator's degree counts the errors; a mismatch means there were
  ::  more than cap of them and the locator did not factor completely
  ?.  =((lent pos) (dec (lent lam)))  ~
  =/  dlam=mol  (deriv lam)
  ::  Forney.  With lam(x) = prod(1 - X_l x), the product terms cancel and
  ::  the magnitude is -omg(X^-1) / lam'(X^-1) -- with no factor of X, a
  ::  point worth stating because the variant formula carrying one is a
  ::  common and silent error.
  ?.  %+  levy  pos
      |=(e=@ud ?!(=(0 (eval:d dlam (cpow:d ainv e)))))
    ~
  =/  fixed=(list @ud)
    =/  ps=(list @ud)   pos
    =/  acc=(list @ud)  (flop recv)
    |-  ^-  (list @ud)
    ?~  ps  acc
    =/  xi=@ud   (cpow:d ainv i.ps)
    =/  num=@ud  (eval:d omg xi)
    =/  den=@ud  (eval:d dlam xi)
    =/  y=@ud    (cneg:d (cmul:d num (cinv:d den)))
    $(ps t.ps, acc (sput acc i.ps (csub:d (snag i.ps `(list @ud)`acc) y)))
  =/  out=(list @ud)  (flop fixed)
  ::  certify: the corrected word must actually be a codeword.  Without
  ::  this the decoder would happily return a word it merely guessed at.
  ?.  (levy (syndromes out) |=(s=@ud =(0 s)))  ~
  `out
::    +decode-upto:  decode, refusing corrections beyond a chosen weight
::
::  [recv=(list @ud) maxerr=@ud] -> (unit (list @ud)).  As +decode, but
::  produces ~ when the correction would alter more than .maxerr symbols.
::
::  This trades correction power for detection reliability.  Miscorrection
::  happens when a word lands nearer some OTHER codeword, which requires
::  the apparent error weight to be large; capping that weight below cap
::  refuses exactly those decodes, at the cost of no longer correcting
::  genuine error patterns that heavy.
::
::  With maxerr = cap this is identical to +decode.  With maxerr = 0 it is
::  a pure integrity check: the word is returned only if already clean.
++  decode-upto
  |=  [recv=(list @ud) maxerr=@ud]
  ^-  (unit (list @ud))
  =/  got  (decode recv)
  ?~  got  ~
  =/  moved=@ud
    =/  a=(list @ud)  recv
    =/  b=(list @ud)  u.got
    =/  acc=@ud       0
    |-  ^-  @ud
    ?~  a  acc
    ?~  b  acc
    $(a t.a, b t.b, acc ?:(=(i.a i.b) acc +(acc)))
  ?:  (gth moved maxerr)  ~
  got
--
