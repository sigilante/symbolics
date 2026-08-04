  ::  /gen/baloon-lll-bench
::::  Time +lll:vh on a van Hoeij-shaped lattice -- SPEC V0, V7
::
::  Usage:  +baloon-lll-bench 9 1 136
::          +baloon-lll-bench 17 1 136
::
::  Arguments are [r=@ud m=@ud bits=@ud]: r modular factors, m power-sum
::  columns, and a lift modulus of 2^bits.  Builds the lattice SPEC V3
::  reduces,
::
::      [  I_r        C   ]
::      [  0     p^a I_m  ]
::
::  with C pseudo-random in [0, p^a), and times ONLY the reduction --
::  construction happens outside the ~>(%bout ...) so it is not charged,
::  and the product is consumed by +reduced so it cannot be elided.
::
::  The VALUES in C are arbitrary; a real C holds scaled power sums.  What
::  the timing is representative of is the SHAPE: +lll's cost is driven by
::  the dimension and the operand size, both of which are the real ones.
::
::  WHY THIS EXISTS.  SPEC V0 measured Zassenhaus at 204 s on SD_5, which
::  is the number phase V1 has to beat, and SD_5 gives r = 16 -- so the
::  lattice van Hoeij needs reduced is dimension 17 and up.  Measured
::  2026.8.4 at m=1, bits=136 (the SD_5 lift target, from +mig:zx):
::
::      dim  5      9.7 s
::      dim  7     61.4 s
::      dim  9    314.7 s
::
::  That is ~n^6.5, putting dim 17 near 5.5 hours: 97x over the budget it
::  must beat, so +lll as written cannot deliver V1.  The cost is +gso,
::  recomputed from scratch inside the size-reduction loop.  SPEC V2 pins
::  the reduction SEQUENCE but explicitly NOT the method of computing the
::  Gram-Schmidt data, so hoisting +gso out of the loop with an
::  incremental mu update, or moving to an integer-preserving LLL, is
::  permitted without escalation.  Re-run this to measure any such change.
::
/-  *baloon, *racoon
/+  baloon, vh=vanhoeij
=/  zm  zm:baloon
:-  %say
|=  [* [r=@ud m=@ud bits=@ud ~] ~]
:-  %tang
|^  ^-  tang
    ?:  |(=(0 r) =(0 m) =(0 bits))
      ~[leaf+"r, m, and bits must all be nonzero"]
    =/  b=zmat  build
    =/  d=@ud   (lent b)
    ::  block triangular with unit and p^a diagonals, so this cannot fail;
    ::  asserted anyway because +lll asserts it and a silent shape bug here
    ::  would surface as a crash inside the timed region
    ?.  =(d (rank:zm b))
      ~[leaf+"lattice is not full rank -- construction is wrong"]
    =/  red=zmat  ~>(%bout (lll:vh b))
    :~  leaf+"dim {<d>}  bits {<bits>}  reduced {<(reduced:vh red)>}"
    ==
::    +rng:  one step of a linear congruential generator, modulo 2^64
::
::  Knuth's MMIX constants.  The quality of the stream does not matter --
::  these are lattice entries, not a statistical sample -- but determinism
::  does, so the seed below is fixed and the numbers are reproducible.
++  rng
  |=  x=@ud
  ^-  @ud
  %+  mod
    (add (mul x 6.364.136.223.846.793.005) 1.442.695.040.888.963.407)
  (bex 64)
::    +draw:  a pseudo-random value in [0, md), with the next state
::
::  Three LCG steps concatenated, so the value is up to 192 bits before
::  the reduction -- enough to fill a 136-bit modulus without the top of
::  the range going unused.
++  draw
  |=  [x=@ud md=@ud]
  ^-  [v=@ud s=@ud]
  =/  a=@ud  (rng x)
  =/  b=@ud  (rng a)
  =/  c=@ud  (rng b)
  :_  c
  %+  mod
    :(add (mul a (bex 128)) (mul b (bex 64)) c)
  md
::    +spike:  a length-n row holding v at index i and --0 elsewhere
++  spike
  |=  [i=@ud n=@ud v=@s]
  ^-  zvec
  =/  k=@ud  0
  =|  out=zvec
  |-  ^-  zvec
  ?:  =(k n)  (flop out)
  $(k +(k), out [?:(=(k i) v --0) out])
::    +cols:  m pseudo-random entries in [0, md), with the next state
++  cols
  |=  [s=@ud md=@ud]
  ^-  [v=zvec s=@ud]
  =/  k=@ud   0
  =/  st=@ud  s
  =|  out=zvec
  |-  ^-  [v=zvec s=@ud]
  ?:  =(k m)  [(flop out) st]
  =/  d  (draw st md)
  $(k +(k), st s.d, out [(sun:si v.d) out])
::    +build:  the van Hoeij lattice at these parameters
++  build
  ^-  zmat
  =/  md=@ud  (bex bits)
  =/  i=@ud   0
  =/  st=@ud  20.260.804
  =|  top=zmat
  |-  ^-  zmat
  ?.  =(i r)
    =/  c  (cols st md)
    %=  $
      i    +(i)
      st   s.c
      top  [(weld (spike i r --1) v.c) top]
    ==
  ::  the p^a I_m block, beneath r columns of zeros
  =/  j=@ud  0
  =|  low=zmat
  |-  ^-  zmat
  ?:  =(j m)  (weld (flop top) (flop low))
  =/  row=zvec  (weld `zvec`(reap r --0) (spike j m (sun:si md)))
  $(j +(j), low [row low])
--
