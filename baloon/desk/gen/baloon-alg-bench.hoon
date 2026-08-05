  ::  /gen/baloon-alg-bench
::::  /gen/racoon-alg-bench's other column -- SPEC A8, V1
::
::  Usage:  +baloon-alg-bench 'x^4 - 10x^2 + 1' 'x^4 - 24x^2 + 4'
::
::  Identical to /gen/racoon-alg-bench except for the import: that one
::  goes through /lib/racoon-alg, whose default recombination is
::  +firr:zx, and this one through /lib/baloon-alg, which is the same
::  door with +factor:vh bound in.
::
::  IT IS A SECOND FILE RATHER THAN A FLAG because racoon/desk builds
::  from Racoon alone and this side needs Baloon.  A `side` argument
::  like /gen/baloon-vh-bench's would have to import both, which would
::  put the dependency back exactly where it was just removed.
::
::  MEASURED.  Vere 4.6, %zuse 409, fake ~zod, --loom 33, Darwin arm64:
::
::                                        deg      firr:zx   van hoeij
::    (sqrt2+sqrt3) + (sqrt5+sqrt7)      4 + 4      3.34 s     3.34 s
::    (SD_4's root)  + sqrt11           16 + 2    281.9 s     90.4 s
::
::  The first row is not a typo.  At degree 16 the factorization is
::  0.3 s of the 3.34 s and the bivariate resultant is the rest, so
::  there is nothing there for van Hoeij to win -- and at r = 8 it
::  falls through +lat-min to +firr:zx anyway.  See /gen/racoon-alg-bench
::  for the argument syntax and the SD_4 literal.
::
/-  *racoon
/+  racoon, rr=racoon-roots, ba=baloon-alg, fmt=racoon-fmt
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
::  +isolate produces roots ascending, so +rear is the largest
=/  a  (make:ba u.pa (rear ia))
=/  b  (make:ba u.pb (rear ib))
=/  s  ~>(%bout (add:ba a b))
:~  leaf+"deg a {<(deg:ba a)>}  deg b {<(deg:ba b)>}  deg a+b {<(deg:ba s)>}"
    leaf+"m(a+b) = {(shoz:fmt m.s)}"
==
