  ::  /gen/baloon-det
::::  Inspect a matrix from the dojo
::
::  Usage:  +baloon-det '[[1 2] [3 4]]'
::          +baloon-det '[[1, 2], [3, 4]]'
::          +baloon-det '[[1/2 1/3] [1/4 1/5]]'
::
::  Parses the matrix, prints it aligned, and reports its dimensions, rank,
::  determinant where square, and rational eigenvalues where any exist.
::
/-  *baloon, *racoon
/+  baloon, racoon, fmt=baloon-fmt
=/  qq  qq:racoon
=/  qm  qm:baloon
:-  %say
|=  [* [txt=@t ~] ~]
:-  %noun
^-  tape
=/  parsed  (redm:fmt txt)
?~  parsed  "parse error, or a ragged matrix"
=/  m=qmat  u.parsed
~&  '::'
=/  lines  (shom:fmt m)
|-
?^  lines
  ~&  i.lines
  $(lines t.lines)
~&  '::'
~&  (weld "dims  " (shod:fmt m))
~&  (weld "rank  " (dot:fmt (rank:qm m)))
?.  (is-square:qm m)
  "not square, so no determinant or spectrum"
~&  (weld "det   " (shof:fmt (det:qm m)))
=/  evs  (eigen:qm m)
?~  evs  "no rational eigenvalues"
%-  weld
:-  "eigen "
=/  es=(list [val=frac mult=@ud])  evs
|-  ^-  tape
?~  es  ""
=/  one=tape
  ?:  =(1 mult.i.es)  (shof:fmt val.i.es)
  :(weld (shof:fmt val.i.es) " (x" (dot:fmt mult.i.es) ")")
?~  t.es  one
:(weld one "  " $(es t.es))
