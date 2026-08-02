  ::  /gen/racoon-factor
::::  Factor a polynomial from the dojo
::
::  Usage:  +racoon-factor 'x^2 - 1'
::          +racoon-factor 'x^4 - 1'
::          +racoon-factor 'x^8 - 40x^6 + 352x^4 - 960x^2 + 576'
::
::  Optionally over F_p, by supplying a prime:
::          +racoon-factor 'x^2 + 1', p=7
::
::  Coefficients are integers; whitespace is ignored; terms may repeat or
::  appear out of order.  Produces the factorization in readable form.
::
/-  *racoon
/+  racoon, fmt=racoon-fmt
=/  zx  zx:racoon
=/  mx  mx:racoon
:-  %say
|=  [* [txt=@t ~] [p=@ud ~]]
:-  %noun
^-  tape
=/  parsed=(unit zol)  (redz:fmt txt)
?~  parsed  "parse error"
=/  a=zol  u.parsed
?~  a  "cannot factor zero"
?:  =(0 p)
  ::  over Z
  :(weld (shoz:fmt a) "  =  " (shozf:fmt (factor:zx a)))
::  over F_p
=/  d  ~(. mx p)
=/  m=mol
  %-  canon:d
  %+  turn  a
  |=  c=@s
  ^-  @ud
  =/  v=@ud  (mod (abs:si c) p)
  ?:((syn:si c) v (mod (sub p v) p))
?~  m  "cannot factor zero"
:(weld (shom:fmt m) "  =  " (shomf:fmt (factor:d m)) "   (mod " (dot:fmt p) ")")
