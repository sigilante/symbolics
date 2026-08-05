  ::  /gen/baloon-lll-bench
::::  Time +lll:vh on a van Hoeij-shaped lattice -- SPEC V0, V7
::
::  Usage:  +baloon-lll-bench 8 1 136        dim 9
::          +baloon-lll-bench 16 1 136       dim 17
::
::  The DIMENSION is r + m, so the first argument is one less than the
::  row of the table below.  The usage line here said 9 and 17 for a
::  while, which is dim 10 and dim 18 -- caught by scripts/bench.sh
::  reading 60% over the recorded figures until the arguments were
::  lined up.
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
::  lattice van Hoeij needs reduced is dimension 17 and up.  All at m=1
::  unless noted, bits=136 (the SD_5 lift target, from +mig:zx):
::
::                  +gso from     once per    maintained    INTEGRAL
::                  scratch       iteration
::      dim  5         9.7 s        3.8 s       0.97 s      0.035 s
::      dim  7        61.4 s       20.0 s       2.54 s      0.083 s
::      dim  9       314.7 s       52.1 s       3.44 s      0.135 s
::      dim 17            --           --      12.0 s      0.641 s
::      dim 18 (m=2)      --           --          --      0.936 s
::      dim 20 (m=4)      --           --     221.7 s      2.298 s
::      dim 33            --           --      49.1 s      3.776 s
::
::  Dimension 9 is 2336x faster than where this started, and none of the
::  four versions changed the output by a single bit.
::
::  THE COLUMN COUNT IS WHY THIS MATTERED.  LLL's cost tracks big-entry
::  columns rather than dimension, so on the rational Gram-Schmidt four
::  trace columns at r=16 cost 221.7 s -- more than the 197.9 s
::  enumeration they were meant to replace.  The budget was therefore two
::  columns, and two cannot separate the Swinnerton-Dyer family.  At
::  2.3 s the budget is eight, eight separates, and SD_5 factors in 9.6 s
::  against 197.9 s.  See baloon/SPEC-QUESTIONS V1.
::
::  SPEC V2 pins the reduction SEQUENCE but explicitly NOT the method of
::  computing the Gram-Schmidt data, which is what licenses all of this.
::  Re-run to measure any further change; /gen/lllfp in the scratch pier
::  is what checks the output is still bit-identical.
::
/-  *baloon, *racoon
/+  baloon, vh=vanhoeij, cas=baloon-cases
=/  zm  zm:baloon
:-  %say
|=  [* [r=@ud m=@ud bits=@ud ~] ~]
:-  %tang
|^  ^-  tang
    ?:  |(=(0 r) =(0 m) =(0 bits))
      ~[leaf+"r, m, and bits must all be nonzero"]
    =/  b=zmat  (lattice:cas r m bits)
    =/  d=@ud   (lent b)
    ::  block triangular with unit and p^a diagonals, so this cannot fail;
    ::  asserted anyway because +lll asserts it and a silent shape bug here
    ::  would surface as a crash inside the timed region
    ?.  =(d (rank:zm b))
      ~[leaf+"lattice is not full rank -- construction is wrong"]
    =/  red=zmat  ~>(%bout (lll:vh b))
    :~  leaf+"dim {<d>}  bits {<bits>}  reduced {<(reduced:vh red)>}"
    ==
--
