  ::  /gen/baloon-vh-bench
::::  van Hoeij against Zassenhaus on the same input -- SPEC V7.5
::
::  Usage:  +baloon-vh-bench 3 0     Zassenhaus on SD_3
::          +baloon-vh-bench 3 1     van Hoeij on SD_3
::
::  Arguments are [k=@ud side=@ud]: the Swinnerton-Dyer index, 2 through
::  5, and which algorithm to time.  Both are run on the same polynomial
::  and both are correct; SPEC V7.3 makes +firr:zx the oracle, since it
::  is already verified against SymPy over the Milestone A corpus.
::
::  ONE TIMED ARM PER RUN, deliberately.  Two ~>(%bout ...) in a single
::  event produce two slog lines that cannot be told apart afterwards,
::  and the pair is what a reader wants to compare.  So the side is an
::  argument and the caller runs it twice.
::
::  THE VAN HOEIJ SIDE FORCES THE LATTICE.  +fact:vh with lo=0 runs the
::  lattice pass at every r, where +factor supplies +lat-min = 16 and
::  would fall through to plain Zassenhaus on SD_3 and SD_4 -- which
::  would measure Zassenhaus twice and report it as a comparison.
::
::  SD_5 is the target: SPEC V0 measured 204 s of Zassenhaus there and
::  named it the number phase V1 has to beat.  It is slow to run BOTH
::  ways, by construction.
::
::  MEASURED.  Vere 4.6, %zuse 409, fake ~zod, --loom 33, Darwin arm64,
::  best of two:
::
::                zassenhaus     van hoeij
::      SD_3          22.4 ms       42.5 ms
::      SD_4         298.7 ms      459.7 ms
::      SD_5         202.5 s         9.42 s     <- 21.5x
::
::  The crossover sits between r = 8 and r = 16, which is what +lat-min
::  encodes.  See baloon/README.md and baloon/SPEC-QUESTIONS.md V1.
::
/-  *baloon, *racoon
/+  baloon, racoon, vh=vanhoeij
=/  zx  zx:racoon
:-  %say
|=  [* [k=@ud side=@ud ~] ~]
:-  %tang
|^  ^-  tang
    ?:  |((lth k 2) (gth k 5))
      ~[leaf+"the Swinnerton-Dyer index runs 2 through 5"]
    =/  f=zol  (sd k)
    ::  the modular factor count is what both costs are driven by, so it
    ::  is printed rather than left to be inferred from the degree
    =/  hd  (hdata:zx f)
    =/  r=@ud  ?~(hd 1 (lent gs.u.hd))
    =/  got=(list zol)
      ?:  =(0 side)  ~>(%bout (firr:zx f))
      ~>(%bout (fact:vh f 0))
    %-  flop
    %+  turn
      :~  "SD_{<k>}  deg={<(deg:zx f)>}  r={<r>}  {?:(=(0 side) "zassenhaus" "vanhoeij")}"
          "   factors={<(lent got)>}"
      ==
    |=(t=tape ^-(tank leaf+t))
::    +sd:  the Swinnerton-Dyer polynomial of index k
::
::  The minimal polynomial of sqrt 2 + sqrt 3 + ... over the first k
::  primes, degree 2^k.  Generated and checked with SymPy rather than
::  written out by hand -- four of these coefficients were wrong the
::  first time they were typed.
++  sd
  |=  k=@ud
  ^-  zol
  ?+  k  !!
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
--
