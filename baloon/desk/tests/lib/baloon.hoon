  ::  /tests/lib/baloon
::::  Baloon test suite
::
::  Phase 0: shape and construction.
::
::  Naming: ++test-p0-* for Phase 0.  Every crash row in SPEC S8 gets a
::  dedicated ++test-p0-crash-* arm, and every non-crash row a matching
::  ++test-p0-nocrash-* arm -- S8 is a two-sided contract and both halves
::  are jettable.
::
::  Property-test inputs are built by local helpers rather than by the
::  library arm they would otherwise be exercising.
::
/-  *baloon, *racoon
/+  *test, baloon, racoon, vec=baloon-vectors
=/  qq  qq:racoon
=/  qm  qm:baloon
|%
+|  %seeds
::    +seed-qm:  pinned PRNG seed for the +qm property tests
++  seed-qm  0xba10.0f00.1234.5678
::
+|  %helpers
::    +rng:  a bounded stream of naturals from a pinned seed
++  rng
  |=  [seed=@ n=@ud hi=@ud]
  ^-  (list @ud)
  =/  gen  ~(. og seed)
  =|  out=(list @ud)
  |-  ^-  (list @ud)
  ?:  =(0 n)  (flop out)
  =^  r  gen  (rads:gen hi)
  $(n (dec n), out [r out])
::    +mkf:  a canonical frac from a natural
::
::  Uses +new:qq, a Racoon arm and so not under test here.
++  mkf
  |=  n=@ud
  ^-  frac
  (new:qq (dif:si (sun:si (mod n 19)) --9) +((mod n 5)))
::    +mk:  build an r x c matrix from a stream of naturals
::
::  Deliberately does NOT call +canon:qm: a property test must not depend
::  on the arm it would otherwise be exercising.  +new:qq canonicalizes
::  each entry directly.
++  mk
  |=  [r=@ud c=@ud ns=(list @ud)]
  ^-  qmat
  %+  turn  (gulf 0 (dec r))
  |=  i=@ud
  ^-  qvec
  %+  turn  (gulf 0 (dec c))
  |=  j=@ud
  ^-  frac
  (mkf (roll (scag +((add (mul i c) j)) ns) add))
::    +qmats:  a deterministic supply of canonical matrices
++  qmats
  |=  [seed=@ count=@ud]
  ^-  (list qmat)
  =/  ns  (rng seed (mul count 40) 1.000)
  %+  turn  (gulf 0 (dec count))
  |=  k=@ud
  ^-  qmat
  =/  r=@ud  +((mod k 4))
  =/  c=@ud  +((mod (add k 2) 4))
  (mk r c (slag (mul k 40) ns))
::    +squares:  a deterministic supply of square matrices
++  qsquares
  |=  [seed=@ count=@ud]
  ^-  (list qmat)
  =/  ns  (rng seed (mul count 40) 1.000)
  %+  turn  (gulf 0 (dec count))
  |=  k=@ud
  ^-  qmat
  =/  n=@ud  +((mod k 4))
  (mk n n (slag (mul k 40) ns))
::
+|  %p0-shape
++  test-p0-dims
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  wide=qmat  ~[~[[--1 1] [--2 1] [--3 1]]]
  =/  tall=qmat  ~[~[[--1 1]] ~[[--2 1]]]
  ;:  weld
    %+  expect-eq  !>([r=`@ud`2 c=`@ud`2])  !>((dims:qm m2))
    %+  expect-eq  !>([r=`@ud`1 c=`@ud`3])  !>((dims:qm wide))
    %+  expect-eq  !>([r=`@ud`2 c=`@ud`1])  !>((dims:qm tall))
    %+  expect-eq  !>(%.y)  !>((is-square:qm m2))
    %+  expect-eq  !>(%.n)  !>((is-square:qm wide))
    %+  expect-eq  !>(%.n)  !>((is-square:qm tall))
  ==
++  test-p0-get
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    ::  zero-based, row then column
    %+  expect-eq  !>(`frac`[--1 1])  !>((get:qm m2 0 0))
    %+  expect-eq  !>(`frac`[--2 1])  !>((get:qm m2 0 1))
    %+  expect-eq  !>(`frac`[--3 1])  !>((get:qm m2 1 0))
    %+  expect-eq  !>(`frac`[--4 1])  !>((get:qm m2 1 1))
  ==
++  test-p0-row-col
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qvec`~[[--1 1] [--2 1]])
    !>((row:qm m2 0))
    %+  expect-eq
      !>(`qvec`~[[--3 1] [--4 1]])
    !>((row:qm m2 1))
    %+  expect-eq
      !>(`qvec`~[[--1 1] [--3 1]])
    !>((col:qm m2 0))
    %+  expect-eq
      !>(`qvec`~[[--2 1] [--4 1]])
    !>((col:qm m2 1))
  ==
++  test-p0-put
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qmat`~[~[[--9 1] [--2 1]] ~[[--3 1] [--4 1]]])
    !>((put:qm m2 0 0 [--9 1]))
    %+  expect-eq
      !>(`qmat`~[~[[--1 1] [--2 1]] ~[[--3 1] [--9 1]]])
    !>((put:qm m2 1 1 [--9 1]))
    ::  a fractional entry is stored as given, already canonical
    %+  expect-eq
      !>(`qmat`~[~[[--1 1] [--1 2]] ~[[--3 1] [--4 1]]])
    !>((put:qm m2 0 1 [--1 2]))
  ==
++  test-p0-transpose
  =/  wide=qmat  ~[~[[--1 1] [--2 1] [--3 1]] ~[[--4 1] [--5 1] [--6 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qmat`~[~[[--1 1] [--4 1]] ~[[--2 1] [--5 1]] ~[[--3 1] [--6 1]]])
    !>((transpose:qm wide))
    ::  involutive
    %+  expect-eq  !>(wide)  !>((transpose:qm (transpose:qm wide)))
    ::  a 1x1 is its own transpose
    %+  expect-eq
      !>(`qmat`~[~[[--7 1]]])
    !>((transpose:qm ~[~[[--7 1]]]))
  ==
++  test-p0-constructors
  ;:  weld
    %+  expect-eq  !>(`qmat`~[~[[--1 1]]])  !>((idn:qm 1))
    %+  expect-eq
      !>(`qmat`~[~[[--1 1] [--0 1]] ~[[--0 1] [--1 1]]])
    !>((idn:qm 2))
    %+  expect-eq
      !>(`qmat`~[~[[--0 1] [--0 1] [--0 1]]])
    !>((zeros:qm 1 3))
    %+  expect-eq
      !>(`qmat`~[~[[--0 1]] ~[[--0 1]]])
    !>((zeros:qm 2 1))
  ==
::  S7: +canon re-canonicalizes entries and is the only arm accepting
::  non-canonical input.
++  test-p0-canon
  ;:  weld
    ::  2/4 reduces to 1/2
    %+  expect-eq
      !>(`qmat`~[~[[--1 2]]])
    !>((canon:qm ~[~[[--2 4]]]))
    ::  already canonical input is unchanged
    %+  expect-eq
      !>(`qmat`~[~[[--1 2] [-3 4]]])
    !>((canon:qm ~[~[[--1 2] [-3 4]]]))
  ==
::
+|  %p0-properties
::  Property: dimensions agree with the structure, and every row has the
::  column count -- the rectangularity the canonical form asserts.
++  test-p0-prop-dims
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 40)
  |=  m=qmat
  =/  d  (dims:qm m)
  ?&  =(r.d (lent m))
      (levy m |=(r=qvec =(c.d (lent r))))
      (gth r.d 0)
      (gth c.d 0)
  ==
::  Property: transpose is involutive and swaps the dimensions.
++  test-p0-prop-transpose
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 40)
  |=  m=qmat
  =/  d   (dims:qm m)
  =/  t   (transpose:qm m)
  =/  dt  (dims:qm t)
  ?&  =(m (transpose:qm t))
      =(r.d c.dt)
      =(c.d r.dt)
  ==
::  Property: transpose moves entry (i, j) to (j, i).
++  test-p0-prop-transpose-entries
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 24)
  |=  m=qmat
  =/  d  (dims:qm m)
  =/  t  (transpose:qm m)
  %+  levy  (gulf 0 (dec r.d))
  |=  i=@ud
  %+  levy  (gulf 0 (dec c.d))
  |=(j=@ud =((get:qm m i j) (get:qm t j i)))
::  Property: +put then +get round-trips, and disturbs nothing else.
++  test-p0-prop-put-get
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 24)
  |=  m=qmat
  =/  d  (dims:qm m)
  =/  x=frac  [--7 3]
  %+  levy  (gulf 0 (dec r.d))
  |=  i=@ud
  %+  levy  (gulf 0 (dec c.d))
  |=  j=@ud
  =/  n  (put:qm m i j x)
  ?&  =(x (get:qm n i j))
      =((dims:qm n) d)
      ::  every other entry is untouched
      %+  levy  (gulf 0 (dec r.d))
      |=  a=@ud
      %+  levy  (gulf 0 (dec c.d))
      |=  b=@ud
      ?|(?&(=(a i) =(b j)) =((get:qm m a b) (get:qm n a b)))
  ==
::  Property: +row and +col agree with +get.
++  test-p0-prop-row-col
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 24)
  |=  m=qmat
  =/  d  (dims:qm m)
  ?&  %+  levy  (gulf 0 (dec r.d))
      |=  i=@ud
      =/  rw  (row:qm m i)
      ?&  =(c.d (lent rw))
          %+  levy  (gulf 0 (dec c.d))
          |=(j=@ud =((get:qm m i j) (snag j rw)))
      ==
      %+  levy  (gulf 0 (dec c.d))
      |=  j=@ud
      =/  cl  (col:qm m j)
      ?&  =(r.d (lent cl))
          %+  levy  (gulf 0 (dec r.d))
          |=(i=@ud =((get:qm m i j) (snag i cl)))
      ==
  ==
::  Property: +idn is square with ones on the diagonal and zeros elsewhere.
++  test-p0-prop-idn
  %+  expect-eq  !>(~)
  !>  ^-  (list @ud)
  %+  skip  (gulf 1 10)
  |=  n=@ud
  =/  m  (idn:qm n)
  =/  d  (dims:qm m)
  ?&  =(r.d n)
      =(c.d n)
      %+  levy  (gulf 0 (dec n))
      |=  i=@ud
      %+  levy  (gulf 0 (dec n))
      |=  j=@ud
      =((get:qm m i j) ?:(=(i j) one:qq zero:qq))
  ==
::  Property: +zeros has the requested shape and is entirely zero.
++  test-p0-prop-zeros
  =/  shapes=(list [r=@ud c=@ud])
    %+  turn  (gulf 1 24)
    |=  k=@ud
    ^-  [r=@ud c=@ud]
    [+((mod k 5)) +((mod k 4))]
  %+  expect-eq  !>(~)
  !>  ^-  (list [r=@ud c=@ud])
  %+  skip  shapes
  |=  [r=@ud c=@ud]
  =/  m  (zeros:qm r c)
  =/  d  (dims:qm m)
  ?&  =(r.d r)
      =(c.d c)
      (levy m |=(v=qvec (levy v |=(f=frac =(f zero:qq)))))
  ==
::  Property: +canon is idempotent and preserves shape.
++  test-p0-prop-canon
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 40)
  |=  m=qmat
  ?&  =(m (canon:qm m))
      =((canon:qm m) (canon:qm (canon:qm m)))
      =((dims:qm m) (dims:qm (canon:qm m)))
  ==
::
+|  %p0-crashes
::  S8: index out of range crashes, in both directions, for every accessor.
++  test-p0-crash-get-oob
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    (expect-fail |.((get:qm m2 2 0)))
    (expect-fail |.((get:qm m2 0 2)))
    (expect-fail |.((get:qm m2 99 99)))
  ==
++  test-p0-crash-put-oob
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    (expect-fail |.((put:qm m2 2 0 [--1 1])))
    (expect-fail |.((put:qm m2 0 2 [--1 1])))
  ==
++  test-p0-crash-row-col-oob
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    (expect-fail |.((row:qm m2 2)))
    (expect-fail |.((col:qm m2 2)))
  ==
::  S8: the empty matrix is not representable.
++  test-p0-crash-constructors-zero
  ;:  weld
    (expect-fail |.((idn:qm 0)))
    (expect-fail |.((zeros:qm 0 3)))
    (expect-fail |.((zeros:qm 3 0)))
    (expect-fail |.((zeros:qm 0 0)))
  ==
::  S8: +canon crashes on a zero denominator, through +new:qq.
++  test-p0-crash-canon-zero-denominator
  (expect-fail |.((canon:qm ~[~[[--1 0]]])))
::  The arms that must NOT crash at the boundaries.
++  test-p0-nocrash
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    ::  the last valid index in each direction
    (expect-success |.((get:qm m2 1 1)))
    (expect-success |.((row:qm m2 1)))
    (expect-success |.((col:qm m2 1)))
    (expect-success |.((put:qm m2 1 1 [--0 1])))
    ::  the smallest representable matrix
    (expect-success |.((idn:qm 1)))
    (expect-success |.((zeros:qm 1 1)))
    (expect-success |.((dims:qm ~[~[[--1 1]]])))
    (expect-success |.((transpose:qm ~[~[[--1 1]]])))
  ==
::
+|  %p0-vectors
::  Oracle is sympy.Matrix; see tools/genvec.py, whose +selfcheck asserts
::  every convention relied on against its definition on every generation.
::
++  test-p0-vec-dims
  %+  expect-eq  !>(~)
  !>  %+  skip  dims-vectors:vec
      |=  [a=qmat r=@ud c=@ud]
      =([r c] (dims:qm a))
::
++  test-p0-vec-transpose
  %+  expect-eq  !>(~)
  !>  %+  skip  transpose-vectors:vec
      |=  [a=qmat t=qmat]
      =(t (transpose:qm a))
::
++  test-p0-vec-idn
  %+  expect-eq  !>(~)
  !>  %+  skip  idn-vectors:vec
      |=  [n=@ud m=qmat]
      =(m (idn:qm n))
::
++  test-p0-vec-zeros
  %+  expect-eq  !>(~)
  !>  %+  skip  zeros-vectors:vec
      |=  [r=@ud c=@ud m=qmat]
      =(m (zeros:qm r c))
--
