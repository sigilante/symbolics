  ::  /gen/racoon-zfac
::::  Factor an integer, and everything downstream of that
::
::  Usage:  +racoon-zfac 360
::          +racoon-zfac 600.851.475.143
::          +racoon-zfac 1
::
::  The divisor set, Euler's totient, the radical, and the least
::  primitive root are all consequences of the factorization, which is
::  why /lib/racoon-zfac computes them and +nz cannot.
::
/-  *racoon
/+  racoon, zf=racoon-zfac, fmt=racoon-fmt
=/  nz  nz:racoon
::    +shods:  a divisor list, space separated
=/  shods
  |=  ds=(list @ud)
  ^-  tape
  ?~  ds  ""
  ?~  t.ds  (dot:fmt i.ds)
  :(weld (dot:fmt i.ds) " " $(ds t.ds))
:-  %say
|=  [* [n=@ud ~] ~]
:-  %tang
?:  =(0 n)
  ~[leaf+"0 has no factorization: every prime divides it"]
=/  fs  (factor:zf n)
=/  ds  (divisors:zf n)
=/  pr  (primitive-root:zf n)
%-  flop
^-  tang
:~  leaf+"{(dot:fmt n)}  =  {(shonf:fmt fs)}"
    leaf+""
    leaf+"prime          {<(is-prime:nz n)>}"
    leaf+"prime power    {<(is-prime-power:zf n)>}"
    leaf+"radical        {(dot:fmt (radical:zf n))}"
    leaf+"totient        {(dot:fmt (totient:zf n))}"
    leaf+"divisors       {(dot:fmt (lent ds))}"
    leaf+"primitive root {?~(pr "none (not cyclic)" (dot:fmt u.pr))}"
    leaf+""
    leaf+"divisors       {?:((gth (lent ds) 24) "(not listed)" (shods ds))}"
==
