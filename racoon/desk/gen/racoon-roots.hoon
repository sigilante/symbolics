  ::  /gen/racoon-roots
::::  Isolate the real roots of an integer polynomial
::
::  Usage:  +racoon-roots 'x^2 - 2'
::          +racoon-roots 'x^3 - x'
::          +racoon-roots 'x^8 - 40x^6 + 352x^4 - 960x^2 + 576'
::
::  Each root comes back as an exact object: a rational root is printed
::  exactly, and an irrational one as a decimal approximation alongside
::  the canonical interval that isolates it.  Nothing here is floating
::  point -- the decimals are exact digits of an exact rational.
::
/-  *racoon
/+  racoon, rr=racoon-roots, fmt=racoon-fmt
=/  zx  zx:racoon
=/  qq  qq:racoon
:-  %say
|=  [* [txt=@t ~] ~]
:-  %tang
=/  parsed=(unit zol)  (redz:fmt txt)
?~  parsed  ~[leaf+"parse error"]
=/  p=zol  u.parsed
?~  p  ~[leaf+"the zero polynomial has every real as a root"]
=/  rs  (roots:rr p)
%-  flop
^-  tang
:-  leaf+"{(shoz:fmt p)}"
%+  weld
  :~  leaf+""
      leaf+"degree            {(dot:fmt (deg:zx p))}"
      leaf+"distinct real     {(dot:fmt (nroots:rr p))}"
      leaf+"rational among    {(dot:fmt (lent (rational-roots:rr p)))}"
      leaf+"squarefree        {<(is-squarefree:rr p)>}"
      leaf+"Cauchy bound      {(shof:fmt (bound:rr p))}"
      leaf+""
  ==
?:  =(~ rs)  ~[leaf+"no real roots"]
%+  turn  rs
|=  r=rrt:rr
^-  tank
=/  mul=tape  ?:(=(1 m.r) "" "  (multiplicity {(dot:fmt m.r)})")
?:  =(lo.iv.r hi.iv.r)
  leaf+"  {(shof:fmt lo.iv.r)}   exact{mul}"
::  +shoapp refines until both endpoints truncate alike, so every digit
::  it prints is right -- the canonical interval itself is wide, being the
::  shallowest node that isolates rather than a tight one
leaf+"  {(shoapp:fmt p iv.r 12)}...  in {(shoiv:fmt iv.r)}{mul}"
