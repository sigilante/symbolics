  ::  /gen/baloon-bench
::::  Baloon benchmark generator
::
::  Usage:  +baloon-bench
::
::  Prints a plain table of timings.  There are NO performance gates in
::  Milestone A (SPEC S11.5): the numbers exist to be recorded in README.md
::  as the denominator for Milestone B speedup claims.
::
::  Method matches Racoon's: each row wraps the work in ~>(%bout ...), which
::  slogs "took ..." and returns a value.  Inputs are built outside the
::  timed region so that construction is not charged to the arm, and the
::  result is consumed so nothing is elided.
::
/-  *baloon, *racoon
/+  baloon, racoon
=/  qq  qq:racoon
=/  qm  qm:baloon
:-  %say
|=  *
:-  %noun
|^  ^-  ~
    ~&  '::'
    ~&  '::  baloon-bench -- Milestone A baselines, no gates'
    ~&  '::'
    =/  a  (bench-mul 4)
    =/  b  (bench-mul 8)
    =/  c  (bench-mul 16)
    ~&  '::'
    =/  d  (bench-det 4)
    =/  e  (bench-det 8)
    =/  f  (bench-det 16)
    ~&  '::'
    =/  g  (bench-rref 4)
    =/  h  (bench-rref 8)
    =/  i  (bench-rref 16)
    ~&  '::'
    =/  j  (bench-inv 4)
    =/  k  (bench-inv 8)
    =/  l  (bench-inv 16)
    ~&  '::'
    =/  m  (bench-charpoly 8)
    ~&  '::'
    ~&  [%checksum :(add a b c d e f g h i j k l m)]
    ~
::
::  Input supply, built outside the timed regions.
::
++  seed  0xba10.0f00.beef.0001
::    +mk:  a deterministic n x n matrix of small rationals
::
::  Diagonally dominant, so it is invertible and its RREF does real work
::  rather than terminating early on a singular column.
++  mk
  |=  [n=@ud off=@ud]
  ^-  qmat
  =/  gen  ~(. og (add seed off))
  =|  rows=qmat
  =/  i=@ud  0
  |-  ^-  qmat
  ?:  =(i n)  (flop rows)
  =^  rr  gen  (rads:gen 1.000)
  =/  row=qvec
    %+  turn  (gulf 0 (dec n))
    |=  j=@ud
    ^-  frac
    =/  v=@ud  (mod (add (mul +(i) 37) (mul +(j) 91)) 17)
    =/  base=@s  (dif:si (sun:si v) --8)
    ?:  =(i j)  (new:qq (sum:si base (sun:si (mul 4 n))) +((mod j 3)))
    (new:qq base +((mod (add i j) 4)))
  $(i +(i), rows [row rows])
::
++  bench-mul
  |=  n=@ud
  ^-  @
  =/  a  (mk n 0)
  =/  b  (mk n 7)
  ~&  ['  mul:qm      ' n]
  ~>  %bout
  (lent (mul:qm a b))
::
++  bench-det
  |=  n=@ud
  ^-  @
  =/  a  (mk n 0)
  ~&  ['  det:qm      ' n]
  ~>  %bout
  q:(det:qm a)
::
++  bench-rref
  |=  n=@ud
  ^-  @
  =/  a  (mk n 3)
  ~&  ['  rref:qm     ' n]
  ~>  %bout
  (lent piv:(rref:qm a))
::
++  bench-inv
  |=  n=@ud
  ^-  @
  =/  a  (mk n 3)
  ~&  ['  inv:qm      ' n]
  ~>  %bout
  (lent (inv:qm a))
::
++  bench-charpoly
  |=  n=@ud
  ^-  @
  =/  a  (mk n 5)
  ~&  ['  charpoly:qm ' n]
  ~>  %bout
  (lent (charpoly:qm a))
--
