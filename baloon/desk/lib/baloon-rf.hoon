  ::  /lib/baloon-rf
::::  Rational functions with van Hoeij bound in -- SPEC F1
::
::  /lib/racoon-rf is a DOOR over its recombination step, defaulting to
::  +firr:zx so that it builds from Racoon alone.  This is that door with
::  +factor:vh in the sample instead, which is the whole file:
::
::      /+  rf=baloon-rf
::      (integrate:rf f)
::
::  Partial fractions factors the denominator, so this is the same cost
::  cliff SPEC V0 measured -- a denominator with sixteen modular factors
::  is not exotic, and there +factor:vh is 21x faster.  Below +lat-min it
::  IS +firr:zx, so this binding is never the slower choice.
::
::  IT EXISTS SO THE FAST PATH IS ALSO A PLAIN IMPORT, the same reason
::  /lib/baloon-alg does.  Binding by hand is one line, and a caller who
::  forgets gets the right answer slowly with nothing to notice.
::
::  Every arm, type, and crash is /lib/racoon-rf's; see that file.
::
/+  rf=racoon-rf, vh=vanhoeij
~(. rf factor:vh)
