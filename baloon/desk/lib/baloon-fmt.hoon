  ::  /lib/baloon-fmt
::::  Human-readable rendering and parsing for Baloon
::
::  Baloon stores matrices as nested lists of ZigZag-coded rationals, which
::  is right for computation and unreadable for people: the 2x2 identity is
::  ~[~[[--1 1] [--0 1]] ~[[--0 1] [--1 1]]].  This library renders those as
::  aligned tables and parses the notation back.
::
::  It is a CONSUMER of /lib/baloon, not part of it, exactly as
::  /lib/racoon-fmt is to Racoon.  Nothing here may be added to the library
::  cores once they freeze.
::
::  Columns are right-aligned to a common width so that a matrix reads as a
::  grid rather than a ragged list -- alignment is most of what makes a
::  printed matrix legible at all.
::
/-  *baloon, *racoon
/+  baloon, racoon
=/  qq  qq:racoon
=/  qm  qm:baloon
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
+|  %matrices
::    +pad:  right-align a tape in a field of the given width
++  pad
  |=  [t=tape w=@ud]
  ^-  tape
  =/  l=@ud  (lent t)
  ?:  (gte l w)  t
  (weld (reap (sub w l) ' ') t)
::    +widest:  the longest rendered entry in a matrix
::
::  Computed over the whole matrix rather than per column, so every entry
::  sits in the same field and the grid reads squarely.
++  widest
  |=  m=qmat
  ^-  @ud
  =/  rows=qmat  m
  =/  w=@ud      1
  |-  ^-  @ud
  ?~  rows  w
  =/  rw=@ud
    =/  cs=qvec  i.rows
    =/  x=@ud    0
    |-  ^-  @ud
    ?~  cs  x
    $(cs t.cs, x (max x (lent (shof i.cs))))
  $(rows t.rows, w (max w rw))
::    +shov:  render a vector on one line, bracketed
++  shov
  |=  v=qvec
  ^-  tape
  ?~  v  "[]"
  =/  cs=qvec  v
  =/  out=tape  "["
  |-  ^-  tape
  ?~  cs  (weld out "]")
  =/  sep=tape  ?~(t.cs "" " ")
  $(cs t.cs, out :(weld out (shof i.cs) sep))
::    +shom:  render a matrix as a list of aligned row tapes
::
::  Produces one tape per row rather than a single tape carrying newlines:
::  a tape with \0a in it renders its escapes literally in the dojo, which
::  defeats the purpose.  Callers print the lines.
++  shom
  |=  m=qmat
  ^-  (list tape)
  =/  w=@ud  (widest m)
  %+  turn  m
  |=  r=qvec
  ^-  tape
  =/  cs=qvec   r
  =/  out=tape  "["
  |-  ^-  tape
  ?~  cs  (weld out " ]")
  $(cs t.cs, out :(weld out " " (pad (shof i.cs) w)))
::    +shod:  the dimensions, as "r x c"
++  shod
  |=  m=qmat
  ^-  tape
  =/  d  (dims:qm m)
  :(weld (dot r.d) " x " (dot c.d))
::
+|  %parsing
::    +num:  an unsigned decimal
++  num  dem
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
::    +qrow:  a bracketed row, entries separated by whitespace or commas
++  qrow
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep qent)
::    +spa:  optional whitespace
++  spa  (star (mask " \0a\09"))
::    +sep:  an entry separator
++  sep  ;~(plug spa (star (just ',')) spa)
::    +qmatr:  a matrix, as bracketed rows inside brackets
++  qmatr
  %+  ifix  [;~(plug (just '[') spa) ;~(plug spa (just ']'))]
  (more sep qrow)
::    +redm:  parse a matrix
::
::  Accepts [[1 2] [3 4]] and [[1, 2], [3, 4]] alike, with any whitespace.
::  Produces ~ on a parse failure OR on a ragged result: raggedness is
::  outside the canonical form, and a parser is exactly the boundary where
::  that should be caught rather than admitted.
++  redm
  |=  txt=@t
  ^-  (unit qmat)
  =/  res  (rust (trip txt) qmatr)
  ?~  res  ~
  =/  m=qmat  u.res
  ?~  m  ~
  =/  w=@ud  (lent i.m)
  ?:  =(0 w)  ~
  ::  widen before +levy: it is wet, so it would otherwise inherit the
  ::  non-empty type ?~ refined m to and fail to nest internally
  =/  ms=qmat  m
  ?.  (levy ms |=(r=qvec =(w (lent r))))  ~
  `ms
::    +redv:  parse a single bracketed vector
++  redv
  |=  txt=@t
  ^-  (unit qvec)
  =/  res  (rust (trip txt) qrow)
  ?~  res  ~
  ?~  u.res  ~
  res
--
