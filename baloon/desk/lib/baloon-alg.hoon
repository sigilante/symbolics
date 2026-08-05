  ::  /lib/baloon-alg
::::  Real algebraic numbers with van Hoeij bound in -- SPEC A8, V1
::
::  /lib/racoon-alg is a DOOR over its recombination step, defaulting to
::  +firr:zx so that it builds from Racoon alone.  This is that door with
::  +factor:vh in the sample instead, which is the whole file:
::
::      /+  al=baloon-alg
::      (add:al a b)
::
::  It lives on the Baloon side for the reason escalation R4 gives --
::  /lib/vanhoeij consumes both libraries, so anything consuming IT has
::  to sit here too.  Racoon's desk stays self-contained.
::
::  IT EXISTS SO THE FAST PATH IS ALSO A PLAIN IMPORT.  Binding by hand
::  is one line, and a caller who forgets gets the right answer slowly
::  -- 281.9 s against 90.4 s on the degree-32 sum -- with nothing to
::  notice.  A silent slow path is worth a file to avoid.
::
::  Every arm, type, and crash is /lib/racoon-alg's; see that file.  The
::  two bindings agree on every input by construction, since +factor:vh
::  falls through to +firr:zx below +lat-min and confirms every factor
::  by trial division above it (SPEC V4).
::
/+  al=racoon-alg, vh=vanhoeij
~(. al factor:vh)
