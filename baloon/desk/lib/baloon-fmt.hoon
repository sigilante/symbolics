  ::  /lib/baloon-fmt
::::  Human-readable rendering and parsing for Baloon
::
::  Baloon stores matrices as nested lists, which is right for computation
::  and unreadable for people: the 2x2 identity over Q is
::  ~[~[[--1 1] [--0 1]] ~[[--0 1] [--1 1]]].  This library renders those
::  as aligned tables and parses the notation back, for all three rings.
::
::  It is a CONSUMER of /lib/baloon, not part of it, exactly as
::  /lib/racoon-fmt is to Racoon.  Nothing here may be added to the
::  library cores once they freeze.
::
::  NAMING: the trailing letter is the RING, as in /lib/racoon-fmt, whose
::  +shoz, +shom, +shoq and +redz, +redq name the integer, modular, and
::  rational cases.  So +shoq renders a $qmat, +shoz a $zmat, +shom an
::  $mmat, and +redq, +redz, +redm parse them back.
::
::  Milestone A named these +shom and +redm for "matrix", when there was
::  only one ring and no ambiguity to have.  Milestone C created the
::  ambiguity -- $mmat is the ring Z/n -- and made the old names actively
::  wrong: +redm parsed a matrix over Q.  They were renamed rather than
::  worked around, which is the whole reason /sur/baloon ring-prefixes
::  every type it declares.
::
::  Columns are right-aligned to a common width so that a matrix reads as
::  a grid rather than a ragged list -- alignment is most of what makes a
::  printed matrix legible at all.
::
/-  *baloon, *racoon
/+  baloon, racoon
=/  qq  qq:racoon
|%
+|  %numbers
::    +dot:  a natural as plain decimal digits
::
::  Deliberately not +scow: dot-grouping renders 1000 as "1.000", which in
::  a computer algebra context reads as a decimal fraction.
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
+|  %layout
::
::  Ring-agnostic.  Every renderer below turns its entries into tapes and
::  hands them here, so alignment is written once rather than three times.
::
::    +pad:  right-align a tape in a field of the given width
++  pad
  |=  [t=tape w=@ud]
  ^-  tape
  =/  l=@ud  (lent t)
  ?:  (gte l w)  t
  (weld (reap (sub w l) ' ') t)
::    +widest:  the longest rendered entry in a table
::
::  Computed over the whole table rather than per column, so every entry
::  sits in the same field and the grid reads squarely.
++  widest
  |=  rs=(list (list tape))
  ^-  @ud
  =/  rows=(list (list tape))  rs
  =/  w=@ud                    1
  |-  ^-  @ud
  ?~  rows  w
  =/  rw=@ud
    =/  cs=(list tape)  i.rows
    =/  x=@ud           0
    |-  ^-  @ud
    ?~  cs  x
    $(cs t.cs, x (max x (lent i.cs)))
  $(rows t.rows, w (max w rw))
::    +grid:  render a table of rendered entries as aligned row tapes
::
::  Produces one tape per row rather than a single tape carrying newlines:
::  a tape with \0a in it renders its escapes literally in the dojo, which
::  defeats the purpose.  Callers print the lines.
++  grid
  |=  rs=(list (list tape))
  ^-  (list tape)
  =/  w=@ud  (widest rs)
  %+  turn  rs
  |=  r=(list tape)
  ^-  tape
  =/  cs=(list tape)  r
  =/  out=tape        "["
  |-  ^-  tape
  ?~  cs  (weld out " ]")
  $(cs t.cs, out :(weld out " " (pad i.cs w)))
::    +line:  render one vector of rendered entries, bracketed, on a line
++  line
  |=  r=(list tape)
  ^-  tape
  ?~  r  "[]"
  =/  cs=(list tape)  r
  =/  out=tape        "["
  |-  ^-  tape
  ?~  cs  (weld out "]")
  =/  gap=tape  ?~(t.cs "" " ")
  $(cs t.cs, out :(weld out i.cs gap))
::    +shod:  dimensions, as "r x c"
::
::  Takes the dimensions rather than a matrix, so it serves all three
::  rings from one arm: a shape is not a ring-dependent notion.  Callers
::  pass (dims:qm m), (dims:zm m), or ~(dims mm n).
++  shod
  |=  d=[r=@ud c=@ud]
  ^-  tape
  :(weld (dot r.d) " x " (dot c.d))
::
+|  %rationals
::    +shoq:  render a matrix over Q as aligned row tapes
++  shoq
  |=  m=qmat
  ^-  (list tape)
  %-  grid
  %+  turn  m
  |=(r=qvec ^-((list tape) (turn r |=(f=frac (shof f)))))
::    +shovq:  render a vector over Q on one line
++  shovq
  |=  v=qvec
  ^-  tape
  (line (turn v |=(f=frac (shof f))))
::
+|  %integers
::    +shoz:  render a matrix over Z as aligned row tapes
++  shoz
  |=  m=zmat
  ^-  (list tape)
  %-  grid
  %+  turn  m
  |=(r=zvec ^-((list tape) (turn r |=(x=@s (sig x)))))
::    +shovz:  render a vector over Z on one line
++  shovz
  |=  v=zvec
  ^-  tape
  (line (turn v |=(x=@s (sig x))))
::
+|  %modular
::    +shom:  render a matrix over Z/n as aligned row tapes
::
::  Entries print as the naturals they are.  The modulus is NOT shown --
::  it belongs to the +mm door, not to the matrix, so this library has no
::  access to it and could only guess.  Callers wanting it in the output
::  print it themselves.
++  shom
  |=  m=mmat
  ^-  (list tape)
  %-  grid
  %+  turn  m
  |=(r=mvec ^-((list tape) (turn r |=(x=@ud (dot x)))))
::    +shovm:  render a vector over Z/n on one line
++  shovm
  |=  v=mvec
  ^-  tape
  (line (turn v |=(x=@ud (dot x))))
::
+|  %parsing
::
::  Accepts [[1 2] [3 4]] and [[1, 2], [3, 4]] alike, with any whitespace.
::  Every +red* produces ~ on a parse failure OR on a ragged result:
::  raggedness is outside the canonical form, and a parser is exactly the
::  boundary where that should be caught rather than admitted.
::
::    +num:  an unsigned decimal
++  num  dem
::    +spa:  optional whitespace
++  spa  (star (mask " \0a\09"))
::    +sep:  an entry separator
++  sep  ;~(plug spa (star (just ',')) spa)
::    +rect:  is a parsed table nonempty and rectangular?
++  rect
  |=  rs=(list (list))
  ^-  ?
  ?~  rs  %.n
  =/  w=@ud  (lent i.rs)
  ?:  =(0 w)  %.n
  ::  widen before +levy: it is wet, so it would otherwise inherit the
  ::  non-empty type ?~ refined rs to and fail to nest internally
  =/  ws=(list (list))  rs
  (levy ws |=(r=(list) =(w (lent r))))
::    +qent:  one rational entry, "p", "-p", "p/q", or "-p/q"
++  qent
  ;~  pose
    %+  cook  |=([n=@ud d=@ud] ^-(frac (new:qq (dif:si --0 (sun:si n)) d)))
    ;~(pfix (just '-') ;~(plug num ;~(pfix (just '/') num)))
    %+  cook  |=(n=@ud ^-(frac (new:qq (dif:si --0 (sun:si n)) 1)))
    ;~(pfix (just '-') num)
    %+  cook  |=([n=@ud d=@ud] ^-(frac (new:qq (sun:si n) d)))
    ;~(plug num ;~(pfix (just '/') num))
    (cook |=(n=@ud ^-(frac (new:qq (sun:si n) 1))) num)
  ==
::    +zent:  one integer entry, "n" or "-n"
++  zent
  ;~  pose
    %+  cook  |=(n=@ud ^-(@s (dif:si --0 (sun:si n))))
    ;~(pfix (just '-') num)
    (cook |=(n=@ud ^-(@s (sun:si n))) num)
  ==
::    +ment:  one entry of Z/n
::
::  Naturals only.  A negative literal has no representative here without
::  the modulus, which this library does not have, so "-1" is a parse
::  failure rather than a silent guess.  Parse over Z and reduce through
::  +of-z:mm when negative input matters.
++  ment  num
::    +qrow:  a bracketed row over Q
++  qrow
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep qent)
::    +zrow:  a bracketed row over Z
++  zrow
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep zent)
::    +mrow:  a bracketed row over Z/n
++  mrow
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep ment)
::    +qmatr:  a matrix over Q, as bracketed rows inside brackets
++  qmatr
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep qrow)
::    +zmatr:  a matrix over Z
++  zmatr
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep zrow)
::    +mmatr:  a matrix over Z/n
++  mmatr
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep mrow)
::    +redq:  parse a matrix over Q
++  redq
  |=  txt=@t
  ^-  (unit qmat)
  =/  res  (rust (trip txt) qmatr)
  ?~  res  ~
  =/  m=qmat  u.res
  ?.  (rect m)  ~
  `m
::    +redz:  parse a matrix over Z
++  redz
  |=  txt=@t
  ^-  (unit zmat)
  =/  res  (rust (trip txt) zmatr)
  ?~  res  ~
  =/  m=zmat  u.res
  ?.  (rect m)  ~
  `m
::    +redm:  parse a matrix over Z/n
::
::  Entries are not reduced -- the modulus lives on the +mm door, so a
::  caller that means them as residues passes the result through
::  +canon:mm.
++  redm
  |=  txt=@t
  ^-  (unit mmat)
  =/  res  (rust (trip txt) mmatr)
  ?~  res  ~
  =/  m=mmat  u.res
  ?.  (rect m)  ~
  `m
::    +redvq:  parse a single bracketed vector over Q
++  redvq
  |=  txt=@t
  ^-  (unit qvec)
  =/  res  (rust (trip txt) qrow)
  ?~  res  ~
  ?~  u.res  ~
  res
::    +redvz:  parse a single bracketed vector over Z
++  redvz
  |=  txt=@t
  ^-  (unit zvec)
  =/  res  (rust (trip txt) zrow)
  ?~  res  ~
  ?~  u.res  ~
  res
::    +redvm:  parse a single bracketed vector over Z/n
++  redvm
  |=  txt=@t
  ^-  (unit mvec)
  =/  res  (rust (trip txt) mrow)
  ?~  res  ~
  ?~  u.res  ~
  res
--
