  ::  /lib/racoon-fmt
::::  Human-readable rendering and parsing for Racoon
::
::  Racoon stores polynomials little-endian as raw nouns, which is right for
::  computation and unreadable for people: x^2 - 1 is ~[-1 --0 --1].  This
::  library renders those forms as conventional mathematical notation and
::  parses the notation back.
::
::  It is a CONSUMER of /lib/racoon, not part of it.  The Milestone A
::  interface is frozen under R6, and %racoon itself is frozen at five arms
::  (see Q5), so nothing may be added to those cores.  Everything here sits
::  outside them and imports the library like any other caller.
::
::  Rendering is descending by degree, the conventional reading order, even
::  though storage ascends.  Numbers print as plain digits rather than
::  through +scow, which would dot-group them: 1.000 reads as a decimal to
::  anyone doing mathematics, which is exactly the wrong signal here.
::
/-  *racoon
/+  racoon
=/  nz  nz:racoon
=/  qq  qq:racoon
=/  zx  zx:racoon
=/  qx  qx:racoon
|%
+|  %numbers
::    +dot:  a natural as plain decimal digits
::
::  Deliberately not +scow: dot-grouping renders 1000 as "1.000", which in a
::  computer algebra context reads as a decimal fraction.
++  dot
  |=  n=@ud
  ^-  tape
  ?:  =(0 n)  "0"
  =|  out=tape
  |-  ^-  tape
  ?:  =(0 n)  out
  $(n (div n 10), out [(add '0' (mod n 10)) out])
::    +sig:  a signed integer as plain digits with a leading minus
++  sig
  |=  n=@s
  ^-  tape
  ?:  (syn:si n)  (dot (abs:si n))
  ['-' (dot (abs:si n))]
::    +shof:  a rational as "p/q", or "p" when the denominator is 1
++  shof
  |=  f=frac
  ^-  tape
  ?:  =(1 q.f)  (sig p.f)
  :(weld (sig p.f) "/" (dot q.f))
::
+|  %polynomials
::    +mono:  render one term, given its magnitude and exponent
::
::  The coefficient 1 is elided except in the constant term, and the
::  exponent 1 is elided, so x^1 prints as x and 1*x^2 as x^2.
++  mono
  |=  [mag=tape e=@ud unit=?]
  ^-  tape
  ?:  =(0 e)  mag
  =/  base=tape  ?:(=(1 e) "x" (weld "x^" (dot e)))
  ?:(unit base (weld mag base))
::    +join:  splice rendered terms together with their signs
::
::  Takes terms already ordered by descending degree, each as a sign and a
::  body.  The leading term takes a bare "-" if negative; the rest take
::  " + " or " - ", so nothing ever renders as "+ -".
++  join
  |=  ts=(list [neg=? body=tape])
  ^-  tape
  ?~  ts  "0"
  =/  hed=tape  ?:(neg.i.ts ['-' body.i.ts] body.i.ts)
  =/  rest=(list [neg=? body=tape])  t.ts
  |-  ^-  tape
  ?~  rest  hed
  %=  $
    rest  t.rest
    hed   :(weld hed ?:(neg.i.rest " - " " + ") body.i.rest)
  ==
::    +shoz:  render a Z[x] polynomial
::
::  The zero polynomial renders as "0".
++  shoz
  |=  a=zol
  ^-  tape
  ?~  a  "0"
  =/  e=@ud   (dec (lent a))
  =/  cs=zol  (flop a)
  =|  ts=(list [neg=? body=tape])
  |-  ^-  tape
  ?~  cs  (join (flop ts))
  =/  nx=@ud  ?:(=(0 e) 0 (dec e))
  ?:  =(--0 i.cs)  $(cs t.cs, e nx)
  =/  m=@ud   (abs:si i.cs)
  %=  $
    cs  t.cs
    e   nx
    ts  [[?!((syn:si i.cs)) (mono (dot m) e =(1 m))] ts]
  ==
::    +shom:  render a (Z/n)[x] polynomial
::
::  Coefficients are already reduced into [0, n), so nothing is ever
::  negative; the modulus is the caller's context and is not printed.
++  shom
  |=  a=mol
  ^-  tape
  ?~  a  "0"
  =/  e=@ud   (dec (lent a))
  =/  cs=mol  (flop a)
  =|  ts=(list [neg=? body=tape])
  |-  ^-  tape
  ?~  cs  (join (flop ts))
  =/  nx=@ud  ?:(=(0 e) 0 (dec e))
  ?:  =(0 i.cs)  $(cs t.cs, e nx)
  %=  $
    cs  t.cs
    e   nx
    ts  [[%.n (mono (dot i.cs) e =(1 i.cs))] ts]
  ==
::    +shoq:  render a Q[x] polynomial
::
::  A non-integer coefficient is parenthesized when it carries an x, so
::  (1/2)x^2 cannot be misread as 1/(2x^2).
++  shoq
  |=  a=qol
  ^-  tape
  ?~  a  "0"
  =/  e=@ud   (dec (lent a))
  =/  cs=qol  (flop a)
  =|  ts=(list [neg=? body=tape])
  |-  ^-  tape
  ?~  cs  (join (flop ts))
  =/  nx=@ud  ?:(=(0 e) 0 (dec e))
  ?:  =(--0 p.i.cs)  $(cs t.cs, e nx)
  =/  m=frac  [(new:si %.y (abs:si p.i.cs)) q.i.cs]
  =/  mag=tape
    ?:  |(=(0 e) =(1 q.m))  (shof m)
    :(weld "(" (shof m) ")")
  %=  $
    cs  t.cs
    e   nx
    ts  [[?!((syn:si p.i.cs)) (mono mag e ?&(=(1 q.m) =(--1 p.m)))] ts]
  ==
::
+|  %factorizations
::    +chain:  splice rendered factors with " * "
::
::  Takes an UNREFINED list: the callers guard on emptiness first, and a
::  ?~ inside the loop would then be vain against the refined type.
++  chain
  |=  ls=(list tape)
  ^-  tape
  ?~  ls  ""
  ?~  t.ls  i.ls
  :(weld i.ls " * " $(ls t.ls))
::    +wrap:  parenthesize a factor unless it is a bare power of x
++  wrap
  |=  [body=tape m=@ud]
  ^-  tape
  =/  base=tape  :(weld "(" body ")")
  ?:(=(1 m) base :(weld base "^" (dot m)))
::    +shozf:  render a factorization over Z
::
::  Renders as c * (f1)^m1 * (f2)^m2, with the leading constant elided when
::  it is 1 and rendered alone when there are no factors.
++  shozf
  |=  f=zfac
  ^-  tape
  =/  ps=(list tape)
    %+  turn  fs.f
    |=([p=zol m=@ud] (wrap (shoz p) m))
  ?~  ps  (sig c.f)
  =/  body=tape  (chain ps)
  ?:(=(--1 c.f) body :(weld (sig c.f) " * " body))
::    +shomf:  render a factorization over F_p
++  shomf
  |=  f=mfac
  ^-  tape
  =/  ps=(list tape)
    %+  turn  fs.f
    |=([p=mol m=@ud] (wrap (shom p) m))
  ?~  ps  (dot c.f)
  =/  body=tape  (chain ps)
  ?:(=(1 c.f) body :(weld (dot c.f) " * " body))
::
+|  %parsing
::    +xpow:  "x" or "x^k", producing the exponent
::
::  Note ;~ rather than a bare (pose a b): ++pose takes an edge and a rule,
::  so it composes as ;~ glue but cannot be applied to two rules directly.
++  xpow
  ;~  pose
    ;~(pfix (jest 'x^') dem)
    (cold 1 (just 'x'))
  ==
::    +trm:  one unsigned term, producing [magnitude exponent]
::
::  Ordered so that "3x^2" is tried before "x^2" before "3": a bare
::  coefficient must be the last alternative, or it would swallow the 3 of
::  3x^2 and then choke on the x.
++  trm
  ;~  pose
    ;~(plug dem xpow)
    (cook |=(e=@ud ^-([@ud @ud] [1 e])) xpow)
    (cook |=(c=@ud ^-([@ud @ud] [c 0])) dem)
  ==
::    +hed:  the leading term, whose sign is optional
++  hed
  ;~  pose
    (cook |=(t=[@ud @ud] ^-([? @ud @ud] [%.n t])) ;~(pfix (just '-') trm))
    (cook |=(t=[@ud @ud] ^-([? @ud @ud] [%.y t])) ;~(pfix (just '+') trm))
    (cook |=(t=[@ud @ud] ^-([? @ud @ud] [%.y t])) trm)
  ==
::    +tal:  a subsequent term, whose sign is required
++  tal
  ;~  pose
    (cook |=(t=[@ud @ud] ^-([? @ud @ud] [%.n t])) ;~(pfix (just '-') trm))
    (cook |=(t=[@ud @ud] ^-([? @ud @ud] [%.y t])) ;~(pfix (just '+') trm))
  ==
::    +bldz:  assemble parsed terms into a canonical zol
::
::  Terms are summed through +add:zx rather than placed by index, so a
::  repeated or out-of-order exponent combines correctly: "x + x" parses to
::  2x, and "1 + x^2 + x" to the same value as "x^2 + x + 1".
++  bldz
  |=  [a=[s=? c=@ud e=@ud] b=(list [s=? c=@ud e=@ud])]
  ^-  zol
  =/  ts=(list [s=? c=@ud e=@ud])  [a b]
  =|  acc=zol
  |-  ^-  zol
  ?~  ts  acc
  =/  cf=@s     (new:si s.i.ts c.i.ts)
  =/  mn=zol    (shift:zx (canon:zx ~[cf]) e.i.ts)
  $(ts t.ts, acc (add:zx acc mn))
::    +zpoly:  the Z[x] rule
++  zpoly  (cook bldz ;~(plug hed (star tal)))
::    +redz:  parse a Z[x] polynomial
::
::  Whitespace is stripped before parsing rather than threaded through the
::  grammar, which keeps the rules readable.  Produces ~ on a parse failure
::  rather than crashing, so a caller can report the error.
++  redz
  |=  txt=@t
  ^-  (unit zol)
  =/  s=tape  (skip (trip txt) |=(c=@t ?|(=(' ' c) =('\09' c))))
  ?~  s  `~
  (rust s zpoly)
::    +redq:  parse a Q[x] polynomial
::
::  Accepts the same syntax as +redz plus "p/q" coefficients.
++  redq
  |=  txt=@t
  ^-  (unit qol)
  =/  s=tape  (skip (trip txt) |=(c=@t ?|(=(' ' c) =('\09' c))))
  ?~  s  `~
  (rust s qpoly)
::    +qcoef:  an unsigned rational coefficient, as [numerator denominator]
::
::  Parentheses are accepted because +shoq emits them: (1/2)x is written
::  that way precisely so it cannot be read as 1/(2x), and the round-trip
::  property test is what caught the parser not accepting its own output.
++  qcoef
  ;~  pose
    %+  ifix  [(just '(') (just ')')]
    ;~(plug dem ;~(pfix (just '/') dem))
    ;~(plug dem ;~(pfix (just '/') dem))
    (cook |=(n=@ud ^-([@ud @ud] [n 1])) dem)
  ==
::    +qtrm:  one unsigned rational term, as [numerator denominator exponent]
++  qtrm
  ;~  pose
    %+  cook  |=([c=[@ud @ud] e=@ud] ^-([@ud @ud @ud] [-.c +.c e]))
    ;~(plug qcoef xpow)
    (cook |=(e=@ud ^-([@ud @ud @ud] [1 1 e])) xpow)
    (cook |=(c=[@ud @ud] ^-([@ud @ud @ud] [-.c +.c 0])) qcoef)
  ==
++  qhed
  ;~  pose
    %+  cook  |=(t=[@ud @ud @ud] ^-([? @ud @ud @ud] [%.n t]))
    ;~(pfix (just '-') qtrm)
    %+  cook  |=(t=[@ud @ud @ud] ^-([? @ud @ud @ud] [%.y t]))
    ;~(pfix (just '+') qtrm)
    (cook |=(t=[@ud @ud @ud] ^-([? @ud @ud @ud] [%.y t])) qtrm)
  ==
++  qtal
  ;~  pose
    %+  cook  |=(t=[@ud @ud @ud] ^-([? @ud @ud @ud] [%.n t]))
    ;~(pfix (just '-') qtrm)
    %+  cook  |=(t=[@ud @ud @ud] ^-([? @ud @ud @ud] [%.y t]))
    ;~(pfix (just '+') qtrm)
  ==
::    +bldq:  assemble parsed terms into a canonical qol
++  bldq
  |=  [a=[s=? n=@ud d=@ud e=@ud] b=(list [s=? n=@ud d=@ud e=@ud])]
  ^-  qol
  =/  ts=(list [s=? n=@ud d=@ud e=@ud])  [a b]
  =|  acc=qol
  |-  ^-  qol
  ?~  ts  acc
  =/  cf=frac  (new:qq (new:si s.i.ts n.i.ts) d.i.ts)
  =/  mn=qol   (shift:qx (canon:qx ~[cf]) e.i.ts)
  $(ts t.ts, acc (add:qx acc mn))
++  qpoly  (cook bldq ;~(plug qhed (star qtal)))
--
