  ::  /lib/baloon-cases
::::  The benchmark inputs, in one place
::
::  Shared by the human surface and the machine surface: /gen/baloon-*-bench
::  print numbers for a reader, /ted/baloon-bench returns them as data for
::  scripts/bench.sh, and both have to be measuring the SAME THING or the
::  recorded table means nothing.
::
::  It exists because the alternative is two copies of a Swinnerton-Dyer
::  polynomial.  Four coefficients of these were wrong the first time they
::  were written out, and a second copy is a second chance to be wrong in
::  only one of them -- which would show up as a benchmark that quietly
::  measures a different input than the table it feeds.
::
::  No timing here.  These arms build inputs and nothing else, so that a
::  caller can construct outside its own timed region.
::
/-  *baloon, *racoon
/+  baloon
=/  zm  zm:baloon
|%
::    +sd:  the Swinnerton-Dyer polynomial of index k
::
::  The minimal polynomial of sqrt 2 + sqrt 3 + ... over the first k
::  primes, degree 2^k.  Generated and checked with SymPy rather than
::  written out by hand.
::
::  These are the adversarial case for recombination: irreducible over Z
::  yet split into pieces of degree at most 2 modulo EVERY prime, so
::  Zassenhaus must reject every proper subset before concluding.  The
::  modular factor count is 2^(k-1), which is what both costs track.
++  sd
  |=  k=@ud
  ^-  zol
  ?+  k  ~|(%sd-range !!)
    %2  ~[--1 --0 -10 --0 --1]
    %3  ~[--576 --0 -960 --0 --352 --0 -40 --0 --1]
      %4
    :~  --46.225  --0  -5.596.840  --0  --13.950.764  --0  -7.453.176
        --0  --1.513.334  --0  -141.912  --0  --6.476  --0  -136  --0
        --1
    ==
      %5
    :~  --2.000.989.041.197.056  --0  -44.660.812.492.570.624  --0
        --183.876.928.237.731.840  --0  -255.690.851.718.529.024  --0
        --172.580.952.324.702.208  --0  -65.892.492.886.671.360  --0
        --15.459.151.516.270.592  --0  -2.349.014.746.136.576  --0
        --239.210.760.462.336  --0  -16.665.641.517.056  --0
        --801.918.722.048  --0  -26.625.650.688  --0  --602.397.952
        --0  -9.028.096  --0  --84.864  --0  -448  --0  --1
    ==
  ==
::    +lattice:  the van Hoeij-shaped lattice at [r m bits]
::
::  [  I_r        C   ]     C the r x m block of scaled power sums,
::  [  0     p^a I_m  ]     here pseudo-random in [0, 2^bits)
::
::  The VALUES in C are arbitrary; a real C holds power sums.  What the
::  timing is representative of is the SHAPE -- +lll's cost is driven by
::  the dimension and the operand size, and both of those are the real
::  ones.
::
::  Deterministic: the seed below is fixed, so two runs reduce the same
::  lattice and two measurements are comparable.
++  lattice
  |=  [r=@ud m=@ud bits=@ud]
  ^-  zmat
  ?>  ?&(?!(=(0 r)) ?!(=(0 m)) ?!(=(0 bits)))
  =/  md=@ud  (bex bits)
  =/  i=@ud   0
  =/  st=@ud  20.260.804
  =|  top=zmat
  |-  ^-  zmat
  ?.  =(i r)
    =/  c  (cols st md m)
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
::
::  Below: the pseudo-random block, private to +lattice.
::
::    +rng:  one step of a linear congruential generator, modulo 2^64
::
::  Knuth's MMIX constants.  The quality of the stream does not matter --
::  these are lattice entries, not a statistical sample -- but determinism
::  does.
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
  |=  [s=@ud md=@ud m=@ud]
  ^-  [v=zvec s=@ud]
  =/  k=@ud   0
  =/  st=@ud  s
  =|  out=zvec
  |-  ^-  [v=zvec s=@ud]
  ?:  =(k m)  [(flop out) st]
  =/  d  (draw st md)
  $(k +(k), st s.d, out [(sun:si v.d) out])
--
