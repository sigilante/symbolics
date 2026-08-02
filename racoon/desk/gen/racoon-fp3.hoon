  ::  /gen/racoon-fp3
::::  Exercise the Goldilocks extension field
::
::  Usage:
::
::      +racoon-fp3 [3 4 5]
::
::  Takes an element of F_p[x]/(x^3 - x - 1) as three base field
::  coefficients, little-endian -- [3 4 5] is 3 + 4x + 5x^2 -- and prints
::  its arithmetic: inverse, Frobenius image, norm, and the identity each
::  is supposed to satisfy.
::
/-  *racoon
/+  racoon, fp=racoon-fp3
=/  gl3
  %~  .  fp
  :-  18.446.744.069.414.584.321
  ~[18.446.744.069.414.584.320 18.446.744.069.414.584.320 0 1]
:-  %say
|=  [^ [c=[a=@ud b=@ud c=@ud] ~] ~]
=/  x=mol  (canon:gl3 ~[a.c b.c c.c])
=/  xi=mol  ?:(=(~ x) ~ (inv:gl3 x))
:-  %tang
%-  flop
^-  tang
:~  leaf+"field:    F_p[x]/(x^3 - x - 1), p = 2^64 - 2^32 + 1"
    leaf+"rank:     {<rank:gl3>}"
    leaf+"|F|:      p^3 = {<(pow 18.446.744.069.414.584.321 3)>}"
    leaf+"irred:    {<irreducible:gl3>}"
    leaf+""
    leaf+"a:        {<x>}"
    leaf+"a^-1:     {<xi>}"
    leaf+"a a^-1:   {<?:(=(~ x) *mol (mul:gl3 x xi))>}"
    leaf+"a^2:      {<(sqr:gl3 x)>}"
    leaf+"a^p:      {<(frob:gl3 x)>}"
    leaf+"a^(p^3):  {<(frob:gl3 (frob:gl3 (frob:gl3 x)))>}"
    leaf+"N(a):     {<(norm:gl3 x)>}"
==
