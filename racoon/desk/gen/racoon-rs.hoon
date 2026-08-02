  ::  /gen/racoon-rs
::::  Reed-Solomon round-trip demonstration
::
::  Usage:  +racoon-rs 'hello'
::          +racoon-rs 'hello', =errs 2
::
::  Encodes the text as field elements over F_257, corrupts .errs symbols
::  deterministically, decodes, and reports whether the original text came
::  back.  Up to 2 errors are correctable at the default nsym = 4.
::
/-  *racoon
/+  rs=racoon-rs
:-  %say
|=  [* [txt=@t ~] [errs=@ud ~]]
:-  %noun
^-  tape
=/  c  ~(. rs [257 3 4])
::  a tape is (list @tD); the symbols are (list @ud), so cast
=/  msg=(list @ud)  (turn (trip txt) |=(c=@tD `@ud`c))
?:  =(~ msg)  "empty input"
=/  code  (encode:c msg)
=/  n=@ud  (lent code)
::  corrupt .errs symbols at spread-out positions
=/  recv=(list @ud)
  =/  i=@ud           0
  =/  acc=(list @ud)  code
  |-  ^-  (list @ud)
  ?:  (gte i errs)  acc
  =/  pos=@ud  (mod (mul i 3) n)
  =/  was=@ud  (snag pos `(list @ud)`acc)
  $(i +(i), acc (sput:c acc pos (mod (add was 97) 257)))
=/  got  (decode:c recv)
=/  shown=tape
  ?~  got  "UNCORRECTABLE"
  =/  back=(list @ud)  (unencode:c u.got)
  ?.  =(back msg)  "decoded to a DIFFERENT message"
  (turn back |=(s=@ud ^-(@tD `@tD`s)))
::  printed line by line rather than returned as one tape: a tape carrying
::  \0a renders its escapes literally in the dojo, which defeats the point
::  of a demonstration
~&  (weld "message   " (trip txt))
~&  (weld "codeword  " <code>)
~&  :(weld "corrupted " <recv> "  (" <errs> " errors)")
(weld "recovered " shown)
