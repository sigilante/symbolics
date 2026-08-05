  ::  /lib/tip5
::::  Tip5, expressed in exact algebra -- an independent witness
::
::  Tip5 is the algebraic sponge hash Nockchain uses for commitments,
::  Merkle trees, and transaction IDs.  It already has an authoritative
::  Hoon implementation (nockchain-official, hoon/common/ztd/three.hoon)
::  and a Rust jet.  THIS IS A SECOND ONE, AND SECOND IS THE POINT.
::
::  WHAT IT IS FOR.  Nockchain's Hoon and its Rust jet share a lineage:
::  the same reading of the same paper produced both, so their agreeing
::  mostly confirms that the transcription was consistent with itself.
::  An implementation built from different primitives agrees for a
::  different reason -- or disagrees, which is the more useful outcome.
::  That is the deliverable.  It is a WITNESS, not a hash to call.
::
::  WHAT IT IS BUILT ON.  Racoon and Baloon do the arithmetic:
::
::      field scalars     +cadd +csub +cmul +cpow +cinv on ~(. mx p)
::      the MDS layer     +mul on ~(. mm p), a 16x16 by 16x1 product
::      the lookup table  +cpow and +csub at modulus 257
::
::  So the witness is two-sided.  A digest matching Nockchain's is
::  evidence about Tip5 AND about Racoon's modular arithmetic and
::  Baloon's matrices: a fault in either would have to conspire with a
::  fault in the transcription to stay hidden.
::
::  WHAT IS DERIVED AND WHAT IS NOT.  A witness that copies its inputs
::  is not a witness, so everything derivable is derived here:
::
::      lookup-table   256 entries, from x -> (x+1)^3 - 1 mod 257
::      mds            256 entries, circulant from 16
::      r, r-inv       from p
::      init states    from the domain
::
::  What cannot be derived is Tip5's design constants -- the MDS
::  matrix's first column and the round-constant schedules.  Those live
::  in /lib/tip5-constants, mechanically extracted rather than typed.
::  That is the exact boundary of this file's independence, stated here
::  rather than left to be discovered.
::
::  MONTGOMERY FORM IS PART OF THE SPECIFICATION, not an optimization.
::  +split-and-lookup reads the BYTES of a state element, so it sees the
::  representative rather than the field element, and a Tip5 that
::  skipped the transform would compute a different function.  Here it
::  is derived from its definition -- montify is multiplication by
::  r = 2^64 mod p = 2^32 - 1, demontify by its inverse -- where
::  Nockchain's +mont-reduction is hand-derived bit manipulation.  Those
::  two agreeing is among the more interesting things the vectors check,
::  and they do: the golden KAT publishes both forms of its round
::  constants and this file's montify carries one to the other.
::
::  "TIP5 WITH 5 ROUNDS" NAMES TWO DIFFERENT FUNCTIONS in
::  nockchain-official, which is the first thing writing this witness
::  turned up.  ztd/three.hoon's +round-constants selects an 80-constant
::  block when num-rounds is 5, while the ai-pow-zk golden KAT's
::  5-round permutation uses the FIRST 80 OF THE CANONICAL 112.  They
::  are not the same numbers and not the same hash.  Both are carried
::  (+rc-alt5 and +rc-canon) so that both sets of published vectors can
::  be checked, and the round constants are therefore a door SAMPLE
::  rather than a constant -- which is the honest shape given that.
::
::  ARMS ARE PINNED, ALL OF THEM.  Tip5's output is defined by its
::  procedure; there is no canonical mathematical object to name, the
::  way there is for +det or +gcd.  This inverts Racoon's usual
::  disposition, where `pinned` is the rare exception, and is the
::  clearest sign that this is an example rather than algebra.
::
::  IT IS SLOW, DELIBERATELY.  Racoon's +cmul canonicalizes on every
::  operation and has no Montgomery multiplication; Nockchain's runs on
::  raw @ arithmetic with a hand-derived reduction and a Rust jet under
::  it.  Do not call this to hash anything whose latency matters.  Call
::  it to find out whether the fast one is right.
::
::  COVERAGE, STATED PLAINLY.  Every published vector is at 5 rounds, so
::  that is what is verified: 100 +hash-10 and 100 +hash-varlen vectors
::  against +rc-alt5, and 100 permutation vectors against the first 80
::  of +rc-canon.  The canonical 7-round path is the same code with 32
::  more constants and is UNVERIFIED -- no vectors for it are published.
::  Do not read a green suite as covering it.
::
/-  *racoon, *baloon
/+  racoon, baloon, con=tip5-constants
=/  mx  mx:racoon
=/  mm  mm:baloon
=<  ~(. tip5 [7 rc-canon:con])
|%
::    +tip5:  the hash, as a door over its round schedule
::
::  .rounds and .rc travel together because they are not independent:
::  the schedule must hold rounds * 16 constants, which +permute
::  asserts.  Nockchain's door takes only the count and picks the block
::  internally; that is what hides the collision described in the header.
++  tip5
  |_  [rounds=@ud rc=(list @ud)]
  +|  %parameters
  ::    +p:  the Goldilocks prime, 2^64 - 2^32 + 1
  ++  p  ^~((sub (bex 64) (sub (bex 32) 1)))
  ::    +fd:  Racoon's modular arithmetic at the base field
  ++  fd  ~(. mx p)
  ::    +mt:  Baloon's matrices at the base field
  ++  mt  ~(. mm p)
  ::    +state-size:  the permutation width
  ++  state-size  16
  ::    +rate:  elements absorbed per permutation
  ++  rate  10
  ::    +capacity:  elements never directly exposed; rate + capacity = 16
  ++  capacity  6
  ::    +digest-length:  elements squeezed out
  ++  digest-length  5
  ::    +num-lookup:  state elements taking the table S-box, not x^7
  ++  num-lookup  4
  ::    +based:  is this a field element?
  ++  based  |=(x=@ud ^-(? (lth x p)))
  ::
  +|  %montgomery
  ::    +r:  the Montgomery radix 2^64, reduced
  ::
  ::  2^64 = p + 2^32 - 1, so r is 2^32 - 1.  Derived rather than
  ::  written down, which also makes the identity below checkable.
  ++  r  ^~((mod (bex 64) p))
  ::    +r-inv:  the inverse of r in the field
  ++  r-inv  ^~((cinv:fd r))
  ::    +cube-r:  is r^3 = 1?  The identity the x^7 S-box rests on
  ::
  ::  m^7 = (br)^7 = b^7 r^7 = b^7 r (r^3)^2, which is (b^7)r exactly
  ::  when r^3 = 1 -- so four PLAIN multiplications of Montgomery
  ::  representatives land back in Montgomery space.  This is specific
  ::  to Goldilocks, and is the one step that would silently compute the
  ::  wrong thing on another field.  Asserted in the test suite.
  ++  cube-r  ^~(=(1 (cpow:fd r 3)))
  ::    +montify:  into Montgomery space, x -> xr
  ++  montify  |=(x=@ud ^-(@ud (cmul:fd x r)))
  ::    +demontify:  out of it
  ++  demontify  |=(x=@ud ^-(@ud (cmul:fd x r-inv)))
  ::
  +|  %derived-constants
  ::    +mds:  the 16x16 circulant MDS matrix, as a list of rows
  ::
  ::  Row i is the flopped column rotated i+1 times, which is what
  ::  "circulant" means, and is 240 constants not transcribed.
  ++  mds
    ^~  ^-  mmat
    =/  acc  (flop mds-column:con)
    =/  i=@ud  0
    =|  out=mmat
    |-  ^-  mmat
    ?:  =(i state-size)  (flop out)
    =/  nex=(list @ud)  [(rear acc) (snip acc)]
    $(i +(i), acc nex, out [nex out])
  ::    +lookup-table:  the byte substitution of the first S-box
  ::
  ::  DERIVED from x -> (x+1)^3 - 1 mod 257, restricted to bytes.  257
  ::  is prime and 3 does not divide 256, so cubing is a bijection on
  ::  the nonzero residues; that is why the result is a permutation of
  ::  the bytes, and why (x+1)^3 mod 257 is never 0 and the answer
  ::  always fits back into a byte.
  ++  lookup-table
    ^~  ^-  (list @ud)
    =/  fs  ~(. mx 257)
    =/  x=@ud  0
    =|  out=(list @ud)
    |-  ^-  (list @ud)
    ?:  =(x 256)  (flop out)
    $(x +(x), out [(csub:fs (cpow:fs +(x) 3) 1) out])
  ::    +rc-m:  the round constants, montified, as the layer wants them
  ++  rc-m  ^~((turn rc montify))
  ::
  +|  %permutation
  ::    +split-and-lookup:  the byte-wise S-box
  ::
  ::  Eight little-endian bytes of the Montgomery representative, each
  ::  through the table, recombined.  +rip drops leading zero bytes, so
  ::  padding back to eight is not cosmetic: without it a small
  ::  representative would substitute fewer bytes than a large one and
  ::  the map would not even be well defined.
  ++  split-and-lookup
    |=  m=@ud
    ^-  @ud
    =/  bs=(list @ud)  (rip 3 m)
    =.  bs  (weld bs (reap (sub 8 (lent bs)) 0))
    (rep 3 (turn bs |=(b=@ud (snag b lookup-table))))
  ::    +sbox:  the S-box layer
  ::
  ::  First four elements by table, the other twelve by x^7 in four
  ::  multiplications -- valid on representatives by +cube-r.
  ++  sbox
    |=  s=(list @ud)
    ^-  (list @ud)
    %+  weld
      (turn (scag num-lookup s) split-and-lookup)
    %+  turn  (slag num-lookup s)
    |=  m=@ud
    ^-  @ud
    =/  sq  (cmul:fd m m)
    =/  qu  (cmul:fd sq sq)
    (cmul:fd m (cmul:fd sq qu))
  ::    +mds-layer:  linear diffusion, as a matrix-vector product
  ::
  ::  Baloon does the work: the state becomes a 16x1 matrix over Z/p and
  ::  this is +mul:mm.  A Montgomery representative times a PLAIN MDS
  ::  constant is again a representative -- (ar)b = (ab)r -- which is
  ::  why these constants are not montified and the layer needs no
  ::  correction afterwards.
  ++  mds-layer
    |=  s=(list @ud)
    ^-  (list @ud)
    =/  col=mmat  (turn s |=(x=@ud ^-((list @ud) ~[x])))
    (turn (mul:mt mds col) |=(v=(list @ud) ^-(@ud (rear v))))
  ::    +round:  S-box, diffuse, add this round's constants
  ++  round
    |=  [s=(list @ud) i=@ud]
    ^-  (list @ud)
    =/  v=(list @ud)  (mds-layer (sbox s))
    =/  cs=(list @ud)  (scag state-size (slag (mul i state-size) rc-m))
    =/  out=(list @ud)  ~
    |-  ^-  (list @ud)
    ?~  v  (flop out)
    ?~  cs  !!
    $(v t.v, cs t.cs, out [(cadd:fd i.v i.cs) out])
  ::    +permute:  the full permutation
  ++  permute
    |=  s=(list @ud)
    ^-  (list @ud)
    ?>  =(state-size (lent s))
    ?>  =((mul rounds state-size) (lent rc))
    =/  i=@ud  0
    |-  ^-  (list @ud)
    ?:  =(i rounds)  s
    $(i +(i), s (round s i))
  ::
  +|  %sponge
  ::    +init:  the initial state
  ::
  ::  Variable-length starts at zero throughout.  Fixed-length puts a
  ::  montified 1 in every capacity slot, which is the domain separation
  ::  that keeps +hash-10 of ten elements distinct from +hash-varlen of
  ::  those same ten.
  ++  init
    |=  dom=?(%variable %fixed)
    ^-  (list @ud)
    ?-  dom
      %variable  (reap state-size 0)
      %fixed     (weld (reap rate 0) (reap capacity (montify 1)))
    ==
  ::    +hash-10:  hash exactly ten field elements to five
  ++  hash-10
    |=  in=(list @ud)
    ^-  (list @ud)
    ?>  =(rate (lent in))
    ?>  (levy in based)
    =/  s=(list @ud)
      (permute (weld (turn in montify) (slag rate (init %fixed))))
    (turn (scag digest-length s) demontify)
  ::    +hash-varlen:  hash any number of field elements to five
  ::
  ::  Pad with [1 0 0 ...] to a multiple of the rate -- ALWAYS, including
  ::  when the length already divides evenly, since a padding that
  ::  sometimes does nothing is not injective and two inputs would
  ::  collide by construction.  Then absorb rate-sized blocks,
  ::  OVERWRITING the rate portion rather than adding into it, and
  ::  squeeze once.
  ++  hash-varlen
    |=  in=(list @ud)
    ^-  (list @ud)
    ?>  (levy in based)
    =/  gap=@ud  (sub rate (mod (lent in) rate))
    =/  ms=(list @ud)  (turn (weld in [1 (reap (dec gap) 0)]) montify)
    =/  s=(list @ud)  (init %variable)
    |-  ^-  (list @ud)
    ::  =(~ ms) and not ?~: ?~ REFINES .ms to a non-empty list inside
    ::  this branch, and +slag's product is a plain (list @ud), which
    ::  then fails to nest when %= assigns it back
    ?:  =(~ ms)  (scag digest-length (turn (scag rate s) demontify))
    $(ms (slag rate ms), s (permute (weld (scag rate ms) (slag rate s))))
  --
--
