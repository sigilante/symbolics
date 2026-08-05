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
/+  baloon, racoon, vh=vanhoeij, cas=baloon-cases
=/  zx  zx:racoon
:-  %say
|=  [* [k=@ud side=@ud ~] ~]
:-  %tang
|^  ^-  tang
    ?:  |((lth k 2) (gth k 5))
      ~[leaf+"the Swinnerton-Dyer index runs 2 through 5"]
    =/  f=zol  (sd:cas k)
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
--
