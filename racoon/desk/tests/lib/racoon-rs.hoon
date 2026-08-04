  ::  /tests/lib/racoon
::::  Racoon test suite
::
::  Phase 0: scalars and elementary number theory (+nz, +qq).
::
::  Naming: ++test-p0-* for Phase 0.  Every crash row in SPEC S8 that names a
::  Phase 0 arm has a dedicated ++test-p0-crash-* arm.  Property tests drive
::  ++og from the pinned literal seeds recorded below.
::
/-  *racoon
/+  *test, racoon, vec=racoon-vectors, fmt=racoon-fmt, rs=racoon-rs
/+  fp=racoon-fp3
/+  zf=racoon-zfac
/+  rr=racoon-roots
/+  al=racoon-alg
=/  nz  nz:racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  mx  mx:racoon
=/  qx  qx:racoon
::  doors at primes, a composite, and the smallest modulus
=/  m7   ~(. mx 7)
=/  m6   ~(. mx 6)
=/  m3   ~(. mx 3)
=/  m2   ~(. mx 2)
::  and at the Goldilocks prime, for the extension field tests
=/  mgl  ~(. mx 18.446.744.069.414.584.321)
|%
++  seed-rs  0x5eed.5010.0000.0001
::
::    +rng:  a bounded stream of naturals from a pinned seed
::
::  [seed=@ n=@ud hi=@ud] -> (list @ud), n values each in [0, hi).
::  Sizes stay small so the interpreted suite runs in tolerable time.
++  rng
  |=  [seed=@ n=@ud hi=@ud]
  ^-  (list @ud)
  =/  gen  ~(. og seed)
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  =(0 n)  (flop out)
  =^  r  gen  (rads:gen hi)
  $(n (dec n), out [r out])
::    +pairs:  zip a flat list into pairs
++  pairs
  |=  a=(list @ud)
  ^-  (list [@ud @ud])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.t.a)]
::    +divides:  does a divide b?
++  divides
  |=  [a=@ud b=@ud]
  ^-  ?
  ?:  =(0 a)  =(0 b)
  =(0 (mod b a))
::    +to-zol:  build a canonical zol from a list of naturals
::
::  The top coefficient is forced nonzero, so the result is canonical by
::  construction.  Deliberately does NOT call +canon:zx: property tests must
::  not depend on the arm they would otherwise be exercising.
++  to-zol
  |=  cs=(list @ud)
  ^-  zol
  =/  ss=zol
    %+  turn  cs
    |=(c=@ud ^-(@s (dif:si (sun:si (mod c 41)) --20)))
  =/  rs=zol  (flop ss)
  ?~  rs  ~
  (flop [?:(=(--0 i.rs) --1 i.rs) t.rs])
::    +to-mol:  reduce a zol into a canonical mol modulo n
::
::  Note that ++dul:si is NOT usable here: it computes (sub b +.c) for a
::  negative operand, which underflows whenever the magnitude exceeds n, and
::  the supply below reaches 20 against moduli as small as 2.  Reducing the
::  magnitude first is what makes this total.
::
::  Trailing zeros are dropped locally rather than through +canon:mx, so the
::  property tests do not depend on the arm they would be exercising.
++  to-mol
  |=  [a=zol n=@ud]
  ^-  mol
  =/  cs=(list @ud)
    %+  turn  a
    |=  c=@s
    ^-  @ud
    =/  m=@ud  (mod (abs:si c) n)
    ?:  (syn:si c)  m
    (mod (sub n m) n)
  =/  r=(list @ud)  (flop cs)
  |-  ^-  mol
  ?~  r  ~
  ?:  =(0 i.r)  $(r t.r)
  (flop r)
::    +tderiv:  formal derivative over Z, for the test suite
::
::  The library's +zderiv lives in the private +pv core and is not reachable
::  from here.  Recomputing it independently is the right thing anyway: a
::  squarefreeness check that borrowed the library's own derivative would be
::  checking less than it appears to.
++  tderiv
  |=  a=zol
  ^-  zol
  ?~  a  ~
  =/  cs=zol  t.a
  =/  k=@ud   1
  =|  out=zol
  |-  ^-  zol
  ?~  cs  (flop out)
  $(cs t.cs, k +(k), out [(pro:si (sun:si k) i.cs) out])
::    +ipow:  integer power, for checking the pseudo-division identity
::
::  The library's own +pows lives in the private +pv core, which is not
::  reachable from here -- correctly, since it is not public API.  Repeated
::  multiplication is the honest check anyway: it shares no code with the
::  square-and-multiply the library uses.
++  ipow
  |=  [b=@s e=@ud]
  ^-  @s
  ?:  =(0 e)  --1
  (pro:si b $(e (dec e)))
::    +to-qol:  embed a zol into Q[x] with varied denominators
::
::  Denominators are derived from the coefficient index, so the supply
::  exercises genuine fractions rather than integers-as-rationals.  Uses
::  +new:qq to canonicalize, which is a Phase 0 arm and so not under test
::  here; trailing zeros are dropped locally rather than via +canon:qx.
++  to-qol
  |=  a=zol
  ^-  qol
  =/  cs=(list frac)
    =/  xs=zol  a
    =/  i=@ud   1
    =|  out=(list frac)
    |-  ^-  (list frac)
    ?~  xs  (flop out)
    $(xs t.xs, i +(i), out [(new:qq i.xs (add 1 (mod i 5))) out])
  =/  r=(list frac)  (flop cs)
  |-  ^-  qol
  ?~  r  ~
  ?:  =(--0 p.i.r)  $(r t.r)
  (flop r)
::    +zols:  a deterministic supply of canonical polynomials
++  zols
  |=  [seed=@ count=@ud]
  ^-  (list zol)
  =/  ns=(list @ud)  (rng seed (mul count 6) 100)
  =|  out=(list zol)
  =/  i=@ud  0
  |-  ^-  (list zol)
  ?:  =(i count)  (flop out)
  $(i +(i), ns (slag 6 ns), out [(to-zol (scag +((mod i 5)) ns)) out])
::    +zpairs:  sliding window of consecutive pairs
++  zpairs
  |=  a=(list zol)
  ^-  (list [zol zol])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.a)]
::    +ztriples:  sliding window of consecutive triples
++  ztriples
  |=  a=(list zol)
  ^-  (list [zol zol zol])
  ?~  a  ~
  ?~  t.a  ~
  ?~  t.t.a  ~
  [[i.a i.t.a i.t.t.a] $(a t.a)]
::  Vector-driven arms below all follow one shape: +skip the cases whose
::  computed value matches the oracle's, then expect the empty list.  A
::  regression therefore names every failing case, rather than stopping at
::  the first one.
::
::  Reed-Solomon coding (/lib/racoon-rs).  This is the live-utilization
::  workload: an error-correcting code either round-trips data through
::  deliberate corruption or it does not, so its correctness criterion is
::  self-evident and does not depend on matching another implementation.
::
::  All cases use p = 257 with primitive element 3.  Every byte 0-255 is a
::  distinct element of F_257, which is what makes byte data representable
::  without an extension field -- Racoon has none.
::
++  rs4  ~(. rs [257 3 4])
++  rs2  ~(. rs [257 3 2])
++  rs6  ~(. rs [257 3 6])
::
++  test-rs-generator
  ;:  weld
    ::  g(x) = prod (x - 3^i) for i in 1..4
    %+  expect-eq  !>(`mol`~[196 138 169 137 1])  !>(gpoly:rs4)
    ::  degree is exactly nsym, so the coefficient list has nsym + 1 entries
    %+  expect-eq  !>(`@ud`3)  !>((lent gpoly:rs2))
    %+  expect-eq  !>(`@ud`5)  !>((lent gpoly:rs4))
    %+  expect-eq  !>(`@ud`7)  !>((lent gpoly:rs6))
    ::  and it is monic
    %+  expect-eq  !>(`@ud`1)  !>((rear gpoly:rs4))
  ==
++  test-rs-encode
  ;:  weld
    %+  expect-eq
      !>(`(list @ud)`~[1 2 3 122 50 19 138])
    !>((encode:rs4 ~[1 2 3]))
    %+  expect-eq  !>(`(list @ud)`~[5 197 135])  !>((encode:rs2 ~[5]))
    ::  systematic: the message occupies the leading positions untouched
    %+  expect-eq
      !>(`(list @ud)`~[1 2 3])
    !>((unencode:rs4 (encode:rs4 ~[1 2 3])))
    ::  an all-zero message encodes to all zeros
    %+  expect-eq
      !>(`(list @ud)`~[0 0 0 0 0])
    !>((encode:rs2 ~[0 0 0]))
  ==
::  A codeword is a multiple of the generator, which is exactly the
::  statement that every syndrome vanishes.
++  test-rs-syndromes
  ;:  weld
    %+  expect-eq
      !>(`(list @ud)`~[0 0 0 0])
    !>((syndromes:rs4 (encode:rs4 ~[1 2 3])))
    %+  expect-eq
      !>(`(list @ud)`~[0 0])
    !>((syndromes:rs2 (encode:rs2 ~[9 8 7])))
    ::  a corrupted word has at least one nonzero syndrome
    %+  expect-eq
      !>(%.n)
    !>((levy (syndromes:rs4 ~[8 2 3 122 50 19 138]) |=(s=@ud =(0 s))))
  ==
++  test-rs-decode-known
  =/  cw=(list @ud)  ~[1 2 3 122 50 19 138]
  ;:  weld
    ::  a clean word passes through unchanged
    %+  expect-eq  !>(`(unit (list @ud))`[~ cw])  !>((decode:rs4 cw))
    ::  one error, in the message part
    %+  expect-eq
      !>(`(unit (list @ud))`[~ cw])
    !>((decode:rs4 ~[1 7 3 122 50 19 138]))
    ::  two errors, one in the message and one in the parity -- at the
    ::  full correction capacity for nsym = 4
    %+  expect-eq
      !>(`(unit (list @ud))`[~ cw])
    !>((decode:rs4 ~[8 2 3 222 50 19 138]))
  ==
::  THE load-bearing test: encode, corrupt up to cap symbols at arbitrary
::  positions, decode, and require the original codeword back exactly.
::  Nothing here compares against a reference implementation; the property
::  is the specification.
++  test-rs-roundtrip
  =/  ns=(list @ud)  (rng seed-rs 600 257)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 0 39)
  |=  trial=@ud
  =/  base=@ud  (mul trial 15)
  =/  k=@ud     +((mod trial 6))
  =/  msg=(list @ud)
    %+  turn  (gulf 0 (dec k))
    |=(i=@ud (mod (snag (mod (add base i) 600) ns) 257))
  =/  code  (encode:rs4 msg)
  =/  n=@ud  (lent code)
  ::  corrupt 0, 1, or 2 symbols -- at most cap = 2 for nsym = 4
  =/  nerr=@ud  (mod trial 3)
  =/  recv=(list @ud)
    =/  i=@ud           0
    =/  acc=(list @ud)  code
    |-  ^-  (list @ud)
    ?:  (gte i nerr)  acc
    =/  pos=@ud    (mod (add (mul trial 7) (mul i 3)) n)
    =/  bump=@ud   +((mod (snag (mod (add base i) 600) ns) 256))
    =/  was=@ud    (snag pos `(list @ud)`acc)
    $(i +(i), acc (sput:rs4 acc pos (mod (add was bump) 257)))
  =/  got  (decode:rs4 recv)
  ?&  ?!(=(~ got))
      =(code +:got)
      ::  and the message itself comes back
      =(msg (unencode:rs4 +:got))
  ==
::  The same property at nsym = 6, correcting up to three errors.
++  test-rs-roundtrip-6
  =/  ns=(list @ud)  (rng seed-rs 400 257)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 0 23)
  |=  trial=@ud
  =/  base=@ud  (mul trial 13)
  =/  k=@ud     +((mod trial 5))
  =/  msg=(list @ud)
    %+  turn  (gulf 0 (dec k))
    |=(i=@ud (mod (snag (mod (add base i) 400) ns) 257))
  =/  code   (encode:rs6 msg)
  =/  n=@ud  (lent code)
  =/  nerr=@ud  (mod trial 4)
  =/  recv=(list @ud)
    =/  i=@ud           0
    =/  acc=(list @ud)  code
    |-  ^-  (list @ud)
    ?:  (gte i nerr)  acc
    =/  pos=@ud   (mod (add (mul trial 5) (mul i 2)) n)
    =/  bump=@ud  +((mod (snag (mod (add base i) 400) ns) 256))
    =/  was=@ud   (snag pos `(list @ud)`acc)
    $(i +(i), acc (sput:rs6 acc pos (mod (add was bump) 257)))
  =/  got  (decode:rs6 recv)
  ?&(?!(=(~ got)) =(code +:got))
::  Property: corruption in EVERY position is correctable, one at a time.
::  A decoder can be subtly wrong only at the ends -- position 0 or n-1 --
::  because of an off-by-one in the Chien search, so every position is
::  swept rather than sampled.
++  test-rs-every-position
  =/  msg=(list @ud)  ~[11 22 33 44]
  =/  code  (encode:rs4 msg)
  =/  n=@ud  (lent code)
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 0 (dec n))
  |=  pos=@ud
  =/  was=@ud  (snag pos `(list @ud)`code)
  =/  recv  (sput:rs4 code pos (mod (add was 137) 257))
  =/  got  (decode:rs4 recv)
  ?&(?!(=(~ got)) =(code +:got))
::  Property: every PAIR of positions is correctable at nsym = 4, which is
::  the capacity.  This is the case a decoder that only ever handled a
::  single error would pass the previous test and fail here.
++  test-rs-every-pair
  =/  msg=(list @ud)  ~[11 22 33]
  =/  code  (encode:rs4 msg)
  =/  n=@ud  (lent code)
  ::  every ordered pair, as a single indexed pass -- a nested +turn under
  ::  +zing does not infer here, both being wet
  =/  pairs=(list [a=@ud b=@ud])
    %+  turn  (gulf 0 (dec (mul n n)))
    |=  k=@ud
    ^-  [a=@ud b=@ud]
    [(div k n) (mod k n)]
  %+  expect-eq  !>(~)
  !>  ^-  (list [a=@ud b=@ud])
  %+  skip  pairs
  |=  [a=@ud b=@ud]
  ?:  =(a b)  %.y
  =/  w1=@ud  (snag a `(list @ud)`code)
  =/  r1  (sput:rs4 code a (mod (add w1 91) 257))
  =/  w2=@ud  (snag b `(list @ud)`r1)
  =/  r2  (sput:rs4 r1 b (mod (add w2 173) 257))
  =/  got  (decode:rs4 r2)
  ?&(?!(=(~ got)) =(code +:got))
::  Crash rows.
++  test-rs-crashes
  ;:  weld
    ::  an empty message has nothing to encode
    (expect-fail |.((encode:rs4 ~)))
    ::  a symbol outside the field
    (expect-fail |.((encode:rs4 ~[257])))
    (expect-fail |.((encode:rs4 ~[300 1])))
    (expect-fail |.((decode:rs4 ~[1 2 3 4 5 6 999])))
    ::  a block longer than p - 1 would repeat evaluation points
    (expect-fail |.((encode:rs4 (reap 260 1))))
  ==
::  +decode-upto trades correction power for detection reliability.  This
::  is the only lever that reduces miscorrection without adding parity --
::  the consistency checks one would reach for provably do not help, since
::  a miscorrection is a genuine valid codeword.
++  test-rs-decode-upto
  =/  cw=(list @ud)  ~[1 2 3 122 50 19 138]
  =/  one=(list @ud)  ~[1 7 3 122 50 19 138]
  =/  two=(list @ud)  ~[8 2 3 222 50 19 138]
  ;:  weld
    ::  at maxerr = cap it agrees with +decode exactly
    %+  expect-eq  !>((decode:rs4 two))  !>((decode-upto:rs4 two 2))
    %+  expect-eq  !>((decode:rs4 one))  !>((decode-upto:rs4 one 2))
    ::  capped below the weight of the correction, it refuses
    %+  expect-eq  !>(`(unit (list @ud))`~)  !>((decode-upto:rs4 two 1))
    ::  but still accepts a lighter one
    %+  expect-eq
      !>(`(unit (list @ud))`[~ cw])
    !>((decode-upto:rs4 one 1))
    ::  maxerr = 0 is a pure integrity check: clean words only
    %+  expect-eq  !>(`(unit (list @ud))`[~ cw])  !>((decode-upto:rs4 cw 0))
    %+  expect-eq  !>(`(unit (list @ud))`~)  !>((decode-upto:rs4 one 0))
  ==
++  test-rs-nocrash
  ;:  weld
    ::  a single-symbol message is fine
    (expect-success |.((encode:rs4 ~[0])))
    (expect-success |.((encode:rs4 ~[256])))
    ::  an uncorrectable word produces ~ rather than crashing
    (expect-success |.((decode:rs2 ~[9 9 9 9 9])))
    (expect-success |.((syndromes:rs4 ~[1 2 3 4 5 6 7])))
  ==
::
::  Extension fields (/lib/racoon-fp3).  The second live-utilization
::  client: F_p[x]/(m) built entirely out of +mx polynomial arithmetic,
::  with the Nockchain Goldilocks cubic as the motivating instance.
::
::  Goldilocks vectors were computed independently in Python and are
::  transcribed here, exactly as the Reed-Solomon vectors were.  The small
::  fields F_27 and F_49 are checked EXHAUSTIVELY instead -- 27 and 49
::  elements are few enough that sampling would be a worse test than
::  simply trying everything.
::
::    +gl3:  F_p[x]/(x^3 - x - 1) at the Goldilocks prime, Nockchain's field
++  gl3  ~(. fp [18.446.744.069.414.584.321 ~[18.446.744.069.414.584.320 18.446.744.069.414.584.320 0 1]])
::    +f27:  F_3[x]/(x^3 - x - 1), the same cubic over the smallest prime
::  where it stays irreducible
++  f27  ~(. fp [3 ~[2 2 0 1]])
::    +f49:  F_7[x]/(x^2 + 1), a QUADRATIC -- the door is not cubic-only
++  f49  ~(. fp [7 ~[1 0 1]])
::    +f7x:  the same cubic over F_7, where it is REDUCIBLE (5 is a root).
::  Present only so that +irreducible has a negative case.
++  f7x  ~(. fp [7 ~[6 6 0 1]])
::    +els:  every element of an extension of degree k over F_pr
::
::  Index i in [0, pr^k) written in base pr, little-endian.  Trailing zero
::  coefficients make these non-canonical, so callers reduce them through
::  the field's own +canon -- which also exercises that arm 27 or 49 times.
++  els
  |=  [pr=@ud k=@ud]
  ^-  (list mol)
  =/  tot=@ud  (pow pr k)
  =/  i=@ud    0
  =|  out=(list mol)
  |-  ^-  (list mol)
  ?:  =(i tot)  (flop out)
  =/  e=mol
    =/  j=@ud  0
    =/  v=@ud  i
    =|  cs=mol
    |-  ^-  mol
    ?:  =(j k)  (flop cs)
    $(j +(j), v (div v pr), cs [(mod v pr) cs])
  $(i +(i), out [e out])
::
::    +vecs-fp3:  the Goldilocks operand pairs, for the structural tests
::
::  Same six pairs the vector tests use, so a structural law and a
::  transcribed value are always checked against the same inputs.
++  vecs-fp3
  ^-  (list [mol mol])
  :~
    [~[17.485.029.721.327.973.432 7.283.207.964.119.141.687 890.727.360.438.182.992] ~[15.149.836.622.520.594.227 1.736.392.818.365.009.963 10.750.541.312.280.087.032]]
    [~[16.781.078.052.021.535.861 3.960.482.443.532.127.989 1.585.446.675.937.841.368] ~[7.713.914.763.314.685.786 4.439.448.776.366.754.703 10.165.027.665.383.847.897]]
    [~[1.090.396.360.377.453.094 10.430.779.633.273.967.791 17.477.362.246.067.780.643] ~[11.632.994.891.556.335.705 10.754.394.637.803.157.173 1.141.153.371.300.629.929]]
    [~[10.801.332.806.156.616.911 914.761.360.679.426.580 4.078.239.883.182.463.692] ~[10.268.654.918.125.279.152 2.456.641.775.679.608.523 7.731.750.658.069.747.094]]
    [~[9.973.894.190.648.387.236 10.531.498.782.278.263.232 10.334.922.596.725.336.632] ~[12.580.729.232.405.932.079 1.901.042.282.212.365.707 10.536.861.175.493.410.705]]
    [~[3.465.608.723.044.488.519 1.797.276.903.956.378.115 13.136.125.050.165.459.753] ~[10.410.757.471.710.933.047 11.418.711.589.407.294.900 9.157.231.070.389.319.135]]
  ==
::
--
