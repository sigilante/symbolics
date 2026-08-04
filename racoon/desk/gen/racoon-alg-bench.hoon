  ::  /gen/racoon-alg-bench
::::  What arithmetic on algebraic numbers costs -- SPEC A7.5, A8
::
::  Usage:  +racoon-alg-bench 'x^4 - 10x^2 + 1' 'x^4 - 24x^2 + 4'
::
::  Takes the LARGEST real root of each argument and times the SUM, which
::  is where the cost lives: Res_y(p(y), q(x-y)) has degree deg p * deg q,
::  and the minimal polynomial is the irreducible factor of it that
::  vanishes at the answer.  So one run charges one bivariate resultant --
::  deg p * deg q + 1 univariate resultants and an interpolation -- plus
::  one factorization of its product.
::
::  Both operands are canonicalized OUTSIDE the timed region, so what is
::  charged is the operation and not the parsing and isolation.
::
::  MEASURED.  Vere 4.6, %zuse 409, fake ~zod, --loom 33, Darwin arm64.
::  "before" is +factor:zx, "after" is van Hoeij through +facz:
::
::                                        deg     before      after
::    (sqrt2+sqrt3) + (sqrt5+sqrt7)      4 + 4     3.34 s     3.34 s
::    (SD_4's root)  + sqrt11           16 + 2   281.9 s     90.4 s
::
::  The first sum's minimal polynomial is SD_4 and the second's is SD_5,
::  so these are the two rungs SPEC A8 is about.
::
::  READ THE FIRST ROW.  At degree 16 the factorization is 0.3 s of the
::  3.34 s and the BIVARIATE RESULTANT is the whole cost, so van Hoeij
::  changes nothing -- it also falls through the +lat-min gate to the
::  same enumeration at r = 8.  At degree 32 it inverts: 202.5 s of the
::  281.9 s was Zassenhaus and van Hoeij does it in 9.4 s, which leaves
::  the resultant as ~90% of what remains.  A8 named factorization as
::  the wall; at the rung A8 was actually describing, it is not.
::
::  The second argument is written out because the parser takes no
::  exponent above what it can read literally:
::
::    +racoon-alg-bench 'x^16 - 136x^14 + 6476x^12 - 141912x^10 +
::      1513334x^8 - 7453176x^6 + 13950764x^4 - 5596840x^2 + 46225'
::      'x^2 - 11'
::
::  (on one line -- SD_4, whose largest real root is sqrt2 + sqrt3 +
::  sqrt5 + sqrt7).
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
::  +isolate produces roots ascending, so +rear is the largest
=/  a  (make:al u.pa (rear ia))
=/  b  (make:al u.pb (rear ib))
=/  s  ~>(%bout (add:al a b))
:~  leaf+"deg a {<(deg:al a)>}  deg b {<(deg:al b)>}  deg a+b {<(deg:al s)>}"
    leaf+"m(a+b) = {(shoz:fmt m.s)}"
==
