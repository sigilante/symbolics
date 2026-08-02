  ::  /gen/racoon-gcd
::::  Greatest common divisor of two polynomials, from the dojo
::
::  Usage:  +racoon-gcd 'x^2 - 1' 'x - 1'
::          +racoon-gcd 'x^4 - 1' 'x^2 - 1'
::
::  Computes over Z, where the result is the content gcd times the primitive
::  gcd with positive leading coefficient.  The modular algorithm behind it
::  certifies its own answer by trial division, so what comes back is the
::  true gcd rather than a candidate.
::
/-  *racoon
/+  racoon, fmt=racoon-fmt
=/  zx  zx:racoon
:-  %say
|=  [* [one=@t two=@t ~] ~]
:-  %noun
^-  tape
=/  pa=(unit zol)  (redz:fmt one)
=/  pb=(unit zol)  (redz:fmt two)
?~  pa  "parse error in first argument"
?~  pb  "parse error in second argument"
=/  g=zol  (gcd:zx u.pa u.pb)
:(weld "gcd(" (shoz:fmt u.pa) ", " (shoz:fmt u.pb) ")  =  " (shoz:fmt g))
