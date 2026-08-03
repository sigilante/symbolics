  ::  /gen/racoon-alg
::::  Arithmetic on two real algebraic numbers
::
::  Usage:  +racoon-alg 'x^2 - 2' 'x^2 - 3'
::          +racoon-alg 'x^2 - 2' 'x^2 - 2'
::          +racoon-alg 'x^2 - x - 1' 'x^3 - 2'
::
::  Two positional arguments, space separated -- NOT a cell.
::
::  Takes two integer polynomials and uses the LARGEST real root of each,
::  so 'x^2 - 2' means the positive square root of 2.  Prints the sum,
::  difference, product, and quotient, each with the minimal polynomial
::  the arithmetic produced -- which is the interesting part: the degree
::  of a product is not the product of the degrees.
::
/-  *racoon
/+  racoon, rr=racoon-roots, al=racoon-alg, fmt=racoon-fmt
=/  zx  zx:racoon
:-  %say
|=  [* [ta=@t tb=@t ~] ~]
:-  %tang
=/  pa=(unit zol)  (redz:fmt ta)
=/  pb=(unit zol)  (redz:fmt tb)
?~  pa  ~[leaf+"parse error in the first polynomial"]
?~  pb  ~[leaf+"parse error in the second polynomial"]
=/  ia  (isolate:rr u.pa)
=/  ib  (isolate:rr u.pb)
?~  ia  ~[leaf+"the first polynomial has no real roots"]
?~  ib  ~[leaf+"the second polynomial has no real roots"]
::  the largest real root of each: +isolate produces them ascending
=/  a  (make:al u.pa (rear ia))
=/  b  (make:al u.pb (rear ib))
=/  k=@ud  12
::    +line:  one labelled algebraic number
=/  line
  |=  [lab=tape v=anum:al]
  ^-  tank
  leaf+"{lab}  {(shoan:fmt v k)}"
%-  flop
^-  tang
:~  (line "a      " a)
    (line "b      " b)
    leaf+""
    (line "a + b  " (add:al a b))
    (line "a - b  " (sub:al a b))
    (line "a * b  " (mul:al a b))
    (line "a / b  " (div:al a b))
    leaf+""
    (line "-a     " (neg:al a))
    (line "1/a    " (inv:al a))
    (line "a^2    " (pow:al a --2))
    leaf+""
    leaf+"deg a {(dot:fmt (deg:al a))}   deg b {(dot:fmt (deg:al b))}"
    leaf+"deg a*b {(dot:fmt (deg:al (mul:al a b)))} -- not the product"
    leaf+"a vs b: {<(cmp:al a b)>}"
==
