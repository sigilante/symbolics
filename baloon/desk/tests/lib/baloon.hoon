  ::  /tests/lib/baloon
::::  Baloon test suite
::
::  Phases 0 through 3: shape, arithmetic, elimination, spectra.
::
::  Naming: ++test-p0-*, ++test-p1-*, and so on.  Every crash row in SPEC
::  S8 gets a dedicated ++test-*-crash-* arm, and every non-crash row a
::  matching ++test-*-nocrash-* arm -- S8 is a two-sided contract and both
::  halves are jettable.
::
::  Property-test inputs are built by local helpers rather than by the
::  library arm they would otherwise be exercising.
::
/-  *baloon, *racoon
/+  *test, baloon, racoon, vec=baloon-vectors
=/  qq  qq:racoon
=/  qx  qx:racoon
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
::    +zip-mats:  consecutive pairs from a matrix supply
++  zip-mats
  |=  a=(list qmat)
  ^-  (list [qmat qmat])
  ?~  a  ~
  ?~  t.a  ~
  [[i.a i.t.a] $(a t.a)]
::    +triple-mats:  consecutive triples from a matrix supply
++  triple-mats
  |=  a=(list qmat)
  ^-  (list [qmat qmat qmat])
  ?~  a  ~
  ?~  t.a  ~
  ?~  t.t.a  ~
  [[i.a i.t.a i.t.t.a] $(a t.a)]
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
::
+|  %p1-arithmetic
++  test-p1-add-sub
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  mb=qmat  ~[~[[--5 1] [--6 1]] ~[[--7 1] [--8 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qmat`~[~[[--6 1] [--8 1]] ~[[--10 1] [--12 1]]])
    !>((add:qm ma mb))
    %+  expect-eq
      !>(`qmat`~[~[[-4 1] [-4 1]] ~[[-4 1] [-4 1]]])
    !>((sub:qm ma mb))
    %+  expect-eq
      !>(`qmat`~[~[[-1 1] [-2 1]] ~[[-3 1] [-4 1]]])
    !>((neg:qm ma))
    ::  subtracting a matrix from itself gives the zero matrix, which is
    ::  canonical -- unlike a polynomial, a matrix never collapses
    %+  expect-eq  !>((zeros:qm 2 2))  !>((sub:qm ma ma))
  ==
++  test-p1-mul
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  mb=qmat  ~[~[[--5 1] [--6 1]] ~[[--7 1] [--8 1]]]
  =/  w=qmat   ~[~[[--1 1] [--2 1] [--3 1]] ~[[--4 1] [--5 1] [--6 1]]]
  =/  v=qmat   ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]] ~[[--5 1] [--6 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qmat`~[~[[--19 1] [--22 1]] ~[[--43 1] [--50 1]]])
    !>((mul:qm ma mb))
    ::  non-square, in both orders: 2x3 * 3x2 is 2x2, and 3x2 * 2x3 is 3x3
    %+  expect-eq
      !>(`qmat`~[~[[--22 1] [--28 1]] ~[[--49 1] [--64 1]]])
    !>((mul:qm w v))
    %+  expect-eq
      !>  ^-  qmat
      :~  ~[[--9 1] [--12 1] [--15 1]]
          ~[[--19 1] [--26 1] [--33 1]]
          ~[[--29 1] [--40 1] [--51 1]]
      ==
    !>((mul:qm v w))
  ==
++  test-p1-scale-pow
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qmat`~[~[[--1 2] [--1 1]] ~[[--3 2] [--2 1]]])
    !>((scale:qm ma [--1 2]))
    ::  scaling by zero gives the zero matrix, not a smaller one
    %+  expect-eq  !>((zeros:qm 2 2))  !>((scale:qm ma zero:qq))
    ::  m^0 is the identity, even for the zero matrix
    %+  expect-eq  !>((idn:qm 2))  !>((pow:qm ma 0))
    %+  expect-eq  !>((idn:qm 2))  !>((pow:qm (zeros:qm 2 2) 0))
    %+  expect-eq  !>(ma)          !>((pow:qm ma 1))
    %+  expect-eq
      !>(`qmat`~[~[[--37 1] [--54 1]] ~[[--81 1] [--118 1]]])
    !>((pow:qm ma 3))
    ::  a nilpotent matrix: N^2 is zero
    %+  expect-eq
      !>((zeros:qm 2 2))
    !>((pow:qm ~[~[[--0 1] [--1 1]] ~[[--0 1] [--0 1]]] 2))
  ==
::
+|  %p1-properties
::  Property: the ring axioms of square matrices under + and *, sampled.
::  Addition commutes; multiplication does NOT, and is not asserted to.
++  test-p1-prop-axioms
  =/  ms  (qsquares seed-qm 24)
  %+  expect-eq  !>(~)
  !>  ^-  (list [qmat qmat])
  %+  skip  (zip-mats ms)
  |=  [a=qmat b=qmat]
  ?.  =((dims:qm a) (dims:qm b))  %.y
  =/  n  r:(dims:qm a)
  ?&  =((add:qm a b) (add:qm b a))
      =(a (add:qm a (zeros:qm n n)))
      =((zeros:qm n n) (add:qm a (neg:qm a)))
      =(a (mul:qm a (idn:qm n)))
      =(a (mul:qm (idn:qm n) a))
      =((sub:qm a b) (add:qm a (neg:qm b)))
  ==
::  Property: multiplication distributes over addition, and associates.
++  test-p1-prop-distributive
  =/  ms  (qsquares seed-qm 18)
  %+  expect-eq  !>(~)
  !>  ^-  (list [qmat qmat qmat])
  %+  skip  (triple-mats ms)
  |=  [a=qmat b=qmat c=qmat]
  ?.  ?&(=((dims:qm a) (dims:qm b)) =((dims:qm b) (dims:qm c)))  %.y
  ?&  =((mul:qm a (add:qm b c)) (add:qm (mul:qm a b) (mul:qm a c)))
      =((mul:qm (add:qm a b) c) (add:qm (mul:qm a c) (mul:qm b c)))
      =((mul:qm a (mul:qm b c)) (mul:qm (mul:qm a b) c))
  ==
::  Property: transpose is an anti-homomorphism for the product, and a
::  homomorphism for the sum.  (a*b)^T = b^T * a^T, note the reversal.
++  test-p1-prop-transpose-mul
  =/  ms  (qsquares seed-qm 24)
  %+  expect-eq  !>(~)
  !>  ^-  (list [qmat qmat])
  %+  skip  (zip-mats ms)
  |=  [a=qmat b=qmat]
  ?.  =((dims:qm a) (dims:qm b))  %.y
  ?&  =((transpose:qm (mul:qm a b)) (mul:qm (transpose:qm b) (transpose:qm a)))
      =((transpose:qm (add:qm a b)) (add:qm (transpose:qm a) (transpose:qm b)))
  ==
::  Property: +pow agrees with repeated multiplication.
++  test-p1-prop-pow
  =/  es=(list @ud)  ~[0 1 2 3 5]
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 18)
  |=  m=qmat
  =/  n  r:(dims:qm m)
  %+  levy  es
  |=  e=@ud
  =/  want=qmat
    =/  i=@ud     e
    =/  acc=qmat  (idn:qm n)
    |-  ^-  qmat
    ?:  =(0 i)  acc
    $(i (dec i), acc (mul:qm acc m))
  =((pow:qm m e) want)
::  Property: +scale agrees with multiplying by a scaled identity, and
::  scaling by zero always gives the zero matrix.
++  test-p1-prop-scale
  =/  xs=(list frac)  ~[[--0 1] [--1 1] [-1 1] [--1 2] [-3 4]]
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 18)
  |=  m=qmat
  =/  d  (dims:qm m)
  ?&  =((scale:qm m zero:qq) (zeros:qm r.d c.d))
      =(m (scale:qm m one:qq))
      %+  levy  xs
      |=  x=frac
      =((scale:qm m x) (mul:qm m (scale:qm (idn:qm r.d) x)))
  ==
::  Property: every arithmetic product keeps the shape it should, and its
::  entries stay canonical.
++  test-p1-prop-shape
  =/  ms  (qmats seed-qm 24)
  %+  expect-eq  !>(~)
  !>  ^-  (list [qmat qmat])
  %+  skip  (zip-mats ms)
  |=  [a=qmat b=qmat]
  =/  da  (dims:qm a)
  =/  db  (dims:qm b)
  ?&  ::  the product is rows(a) x cols(b)
      ?|  ?!(=(c.da r.db))
          =((dims:qm (mul:qm a b)) [r.da c.db])
      ==
      ::  sums keep the shape
      ?|(?!(=(da db)) =((dims:qm (add:qm a b)) da))
      ::  and every entry is canonical
      =((neg:qm a) (canon:qm (neg:qm a)))
      =((scale:qm a [--2 3]) (canon:qm (scale:qm a [--2 3])))
  ==
::
+|  %p1-crashes
::  S8: +add and +sub crash on a dimension mismatch.
++  test-p1-crash-add-mismatch
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  m1=qmat  ~[~[[--1 1]]]
  =/  w=qmat   ~[~[[--1 1] [--2 1] [--3 1]]]
  ;:  weld
    (expect-fail |.((add:qm m2 m1)))
    (expect-fail |.((add:qm m1 m2)))
    (expect-fail |.((sub:qm m2 w)))
    ::  same entry count, different shape
    (expect-fail |.((add:qm ~[~[[--1 1] [--2 1]]] ~[~[[--1 1]] ~[[--2 1]]])))
  ==
::  S8: +mul crashes unless cols(a) = rows(b).
++  test-p1-crash-mul-mismatch
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  m1=qmat  ~[~[[--1 1]]]
  ;:  weld
    (expect-fail |.((mul:qm m2 m1)))
    (expect-fail |.((mul:qm m1 m2)))
  ==
::  S8: +pow crashes on a non-square input, including at exponent zero,
::  where there is no identity of matching shape to produce.
++  test-p1-crash-pow-nonsquare
  =/  w=qmat  ~[~[[--1 1] [--2 1] [--3 1]]]
  ;:  weld
    (expect-fail |.((pow:qm w 2)))
    (expect-fail |.((pow:qm w 0)))
  ==
++  test-p1-nocrash
  =/  m2=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  w=qmat   ~[~[[--1 1] [--2 1] [--3 1]] ~[[--4 1] [--5 1] [--6 1]]]
  =/  v=qmat   ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]] ~[[--5 1] [--6 1]]]
  ;:  weld
    ::  non-square multiplication is fine when the inner dimensions agree
    (expect-success |.((mul:qm w v)))
    (expect-success |.((mul:qm v w)))
    ::  neg and scale never constrain shape
    (expect-success |.((neg:qm w)))
    (expect-success |.((scale:qm w zero:qq)))
    (expect-success |.((pow:qm m2 0)))
    (expect-success |.((add:qm w w)))
  ==
::
+|  %p1-vectors
++  test-p1-vec-add
  %+  expect-eq  !>(~)
  !>  %+  skip  add-vectors:vec
      |=  [a=qmat b=qmat c=qmat]
      =(c (add:qm a b))
::
++  test-p1-vec-sub
  %+  expect-eq  !>(~)
  !>  %+  skip  sub-vectors:vec
      |=  [a=qmat b=qmat c=qmat]
      =(c (sub:qm a b))
::
++  test-p1-vec-mul
  %+  expect-eq  !>(~)
  !>  %+  skip  mul-vectors:vec
      |=  [a=qmat b=qmat c=qmat]
      =(c (mul:qm a b))
::
++  test-p1-vec-neg
  %+  expect-eq  !>(~)
  !>  %+  skip  neg-vectors:vec
      |=  [a=qmat c=qmat]
      =(c (neg:qm a))
::
++  test-p1-vec-scale
  %+  expect-eq  !>(~)
  !>  %+  skip  scale-vectors:vec
      |=  [a=qmat x=frac c=qmat]
      =(c (scale:qm a x))
::
++  test-p1-vec-pow
  %+  expect-eq  !>(~)
  !>  %+  skip  pow-vectors:vec
      |=  [a=qmat e=@ud c=qmat]
      =(c (pow:qm a e))
::
+|  %p2-elimination
++  test-p2-det
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  ms=qmat  ~[~[[--1 1] [--2 1]] ~[[--2 1] [--4 1]]]
  =/  mt=qmat
    :~  ~[[--1 1] [--2 1] [--3 1]]
        ~[[--4 1] [--5 1] [--6 1]]
        ~[[--7 1] [--8 1] [--10 1]]
    ==
  =/  mq=qmat  ~[~[[--1 2] [--1 3]] ~[[--1 4] [--1 5]]]
  ;:  weld
    %+  expect-eq  !>(`frac`[-2 1])   !>((det:qm ma))
    ::  a singular matrix has determinant zero
    %+  expect-eq  !>(`frac`[--0 1])  !>((det:qm ms))
    %+  expect-eq  !>(`frac`[-3 1])   !>((det:qm mt))
    ::  fractional entries: 1/2*1/5 - 1/3*1/4 = 1/10 - 1/12 = 1/60
    %+  expect-eq
      !>(`frac`[--1 60])
    !>((det:qm mq))
    ::  a 1x1 determinant is its entry
    %+  expect-eq  !>(`frac`[-3 4])   !>((det:qm ~[~[[-3 4]]]))
    %+  expect-eq  !>(one:qq)         !>((det:qm (idn:qm 4)))
    ::  a zero first pivot forces the Bareiss row swap, which flips sign
    %+  expect-eq
      !>(`frac`[-1 1])
    !>((det:qm ~[~[[--0 1] [--1 1]] ~[[--1 1] [--1 1]]]))
  ==
++  test-p2-rank-rref
  =/  ms=qmat  ~[~[[--1 1] [--2 1]] ~[[--2 1] [--4 1]]]
  ;:  weld
    %+  expect-eq  !>(`@ud`2)  !>((rank:qm (idn:qm 2)))
    %+  expect-eq  !>(`@ud`1)  !>((rank:qm ms))
    %+  expect-eq  !>(`@ud`0)  !>((rank:qm (zeros:qm 3 3)))
    ::  the RREF of a singular 2x2 keeps one pivot
    %+  expect-eq
      !>  ^-  qrref
      [~[~[[--1 1] [--2 1]] ~[[--0 1] [--0 1]]] ~[0]]
    !>((rref:qm ms))
    ::  the RREF of an invertible matrix is the identity
    %+  expect-eq
      !>(`qmat`(idn:qm 2))
    !>(m:(rref:qm ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]))
  ==
++  test-p2-inv-solve
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  mq=qmat  ~[~[[--1 2] [--1 3]] ~[[--1 4] [--1 5]]]
  =/  ms=qmat  ~[~[[--1 1] [--2 1]] ~[[--2 1] [--4 1]]]
  =/  bb=qmat  ~[~[[--5 1]] ~[[--11 1]]]
  ;:  weld
    %+  expect-eq
      !>(`qmat`~[~[[-2 1] [--1 1]] ~[[--3 2] [-1 2]]])
    !>((inv:qm ma))
    ::  a fractional inverse comes out in integers here
    %+  expect-eq
      !>(`qmat`~[~[[--12 1] [-20 1]] ~[[-15 1] [--30 1]]])
    !>((inv:qm mq))
    %+  expect-eq  !>((idn:qm 3))  !>((inv:qm (idn:qm 3)))
    ::  x = [1 2] solves [[1 2] [3 4]] x = [5 11]
    %+  expect-eq
      !>(`(unit qmat)`[~ ~[~[[--1 1]] ~[[--2 1]]]])
    !>((solve:qm ma bb))
    ::  S8: a singular system produces ~ rather than crashing
    %+  expect-eq  !>(`(unit qmat)`~)  !>((solve:qm ms bb))
  ==
++  test-p2-nullspace
  =/  ms=qmat  ~[~[[--1 1] [--2 1]] ~[[--2 1] [--4 1]]]
  =/  wide=qmat
    ~[~[[--1 1] [--2 1] [--3 1] [--4 1]] ~[[--2 1] [--4 1] [--6 1] [--8 1]]]
  ;:  weld
    ::  the S7 convention: 1 at the free column, negated RREF entry at the
    ::  pivot -- so [-2 1], not [2 -1] or a scaled variant
    %+  expect-eq
      !>(`(list qvec)`~[~[[-2 1] [--1 1]]])
    !>((nullspace:qm ms))
    ::  three free columns, ordered by ascending index
    %+  expect-eq
      !>  ^-  (list qvec)
      :~  ~[[-2 1] [--1 1] [--0 1] [--0 1]]
          ~[[-3 1] [--0 1] [--1 1] [--0 1]]
          ~[[-4 1] [--0 1] [--0 1] [--1 1]]
      ==
    !>((nullspace:qm wide))
    ::  full column rank leaves an empty basis, not a crash
    %+  expect-eq  !>(`(list qvec)`~)  !>((nullspace:qm (idn:qm 3)))
  ==
::
+|  %p2-properties
::  Property: inv(m) * m and m * inv(m) are both exactly the identity.
++  test-p2-prop-inv
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n  r:(dims:qm m)
  ?:  =(zero:qq (det:qm m))  %.y
  =/  vi  (inv:qm m)
  ?&  =((mul:qm vi m) (idn:qm n))
      =((mul:qm m vi) (idn:qm n))
  ==
::  Property: rank-nullity.  rank(m) + dim(nullspace(m)) = cols(m).
++  test-p2-prop-rank-nullity
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 30)
  |=  m=qmat
  =/  d  (dims:qm m)
  =((add (rank:qm m) (lent (nullspace:qm m))) c.d)
::  Property: every nullspace basis vector really is in the kernel.
++  test-p2-prop-nullspace-kernel
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 30)
  |=  m=qmat
  =/  d  (dims:qm m)
  %+  levy  (nullspace:qm m)
  |=  v=qvec
  =/  col=qmat  (turn v |=(f=frac ^-(qvec ~[f])))
  =((mul:qm m col) (zeros:qm r.d 1))
::  Property: det is multiplicative, and invariant under transpose.
++  test-p2-prop-det
  =/  ms  (qsquares seed-qm 24)
  %+  expect-eq  !>(~)
  !>  ^-  (list [qmat qmat])
  %+  skip  (zip-mats ms)
  |=  [a=qmat b=qmat]
  ?.  =((dims:qm a) (dims:qm b))  %.y
  ?&  =((det:qm (mul:qm a b)) (mul:qq (det:qm a) (det:qm b)))
      =((det:qm (transpose:qm a)) (det:qm a))
      =((det:qm (idn:qm r:(dims:qm a))) one:qq)
  ==
::  Property: a matrix is singular exactly when its determinant vanishes.
++  test-p2-prop-singular
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n  r:(dims:qm m)
  =(=(zero:qq (det:qm m)) ?!(=(n (rank:qm m))))
::  Property: RREF is idempotent, and preserves shape.
++  test-p2-prop-rref-idempotent
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qmats seed-qm 30)
  |=  m=qmat
  =/  rr  (rref:qm m)
  ?&  =(m.rr m:(rref:qm m.rr))
      =((dims:qm m.rr) (dims:qm m))
      ::  pivots are strictly ascending
      =/  ps=(list @ud)  piv.rr
      |-  ^-  ?
      ?~  ps  %.y
      ?~  t.ps  %.y
      ?&((lth i.ps i.t.ps) $(ps t.ps))
  ==
::  Property: +solve produces an x satisfying a*x = b, and produces ~
::  exactly when a is singular.
++  test-p2-prop-solve
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n  r:(dims:qm m)
  =/  b=qmat  (scale:qm (transpose:qm ~[(row:qm (idn:qm n) 0)]) [--3 1])
  =/  x  (solve:qm m b)
  ?~  x  =(zero:qq (det:qm m))
  ?&  ?!(=(zero:qq (det:qm m)))
      =((mul:qm m u.x) b)
  ==
::
+|  %p2-crashes
::  S8: +det, +inv, and +charpoly require square input.
++  test-p2-crash-nonsquare
  =/  w=qmat  ~[~[[--1 1] [--2 1] [--3 1]]]
  ;:  weld
    (expect-fail |.((det:qm w)))
    (expect-fail |.((inv:qm w)))
  ==
::  S8: +inv crashes on a singular matrix.
++  test-p2-crash-inv-singular
  ;:  weld
    (expect-fail |.((inv:qm ~[~[[--1 1] [--2 1]] ~[[--2 1] [--4 1]]])))
    (expect-fail |.((inv:qm (zeros:qm 2 2))))
    (expect-fail |.((inv:qm ~[~[[--0 1]]])))
  ==
::  S8: +solve requires a square and matching row counts.
++  test-p2-crash-solve-shape
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  w=qmat   ~[~[[--1 1] [--2 1] [--3 1]]]
  ;:  weld
    (expect-fail |.((solve:qm w ~[~[[--1 1]]])))
    ::  b has the wrong number of rows
    (expect-fail |.((solve:qm ma ~[~[[--1 1]]])))
  ==
::  The Phase 2 arms that must NOT crash.
++  test-p2-nocrash
  =/  ms=qmat  ~[~[[--1 1] [--2 1]] ~[[--2 1] [--4 1]]]
  =/  w=qmat   ~[~[[--1 1] [--2 1] [--3 1]]]
  ;:  weld
    ::  a singular system produces ~, and singular input is fine elsewhere
    (expect-success |.((solve:qm ms ~[~[[--1 1]] ~[[--2 1]]])))
    (expect-success |.((det:qm ms)))
    (expect-success |.((rank:qm ms)))
    ::  rref, rank, and nullspace are total, including on non-square input
    (expect-success |.((rref:qm w)))
    (expect-success |.((rank:qm w)))
    (expect-success |.((nullspace:qm w)))
    (expect-success |.((nullspace:qm (idn:qm 2))))
    (expect-success |.((rref:qm (zeros:qm 2 3))))
  ==
::
+|  %p2-vectors
++  test-p2-vec-det
  %+  expect-eq  !>(~)
  !>  %+  skip  det-vectors:vec
      |=  [a=qmat d=frac]
      =(d (det:qm a))
::
++  test-p2-vec-rref
  %+  expect-eq  !>(~)
  !>  %+  skip  rref-vectors:vec
      |=  [a=qmat m=qmat piv=(list @ud)]
      =([m piv] (rref:qm a))
::
++  test-p2-vec-rank
  %+  expect-eq  !>(~)
  !>  %+  skip  rank-vectors:vec
      |=  [a=qmat r=@ud]
      =(r (rank:qm a))
::
++  test-p2-vec-inv
  %+  expect-eq  !>(~)
  !>  %+  skip  inv-vectors:vec
      |=  [a=qmat c=qmat]
      =(c (inv:qm a))
::
++  test-p2-vec-solve
  %+  expect-eq  !>(~)
  !>  %+  skip  solve-vectors:vec
      |=  [a=qmat b=qmat out=(unit qmat)]
      =(out (solve:qm a b))
::
++  test-p2-vec-nullspace
  %+  expect-eq  !>(~)
  !>  %+  skip  nullspace-vectors:vec
      |=  [a=qmat ns=(list qvec)]
      =(ns (nullspace:qm a))
::
+|  %p3-spectral
++  test-p3-charpoly
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  =/  md=qmat  ~[~[[--2 1] [--0 1]] ~[[--0 1] [--3 1]]]
  =/  mr=qmat  ~[~[[--0 1] [-1 1]] ~[[--1 1] [--0 1]]]
  =/  mj=qmat  ~[~[[--5 1] [--1 1]] ~[[--0 1] [--5 1]]]
  =/  mt=qmat
    :~  ~[[--1 1] [--2 1] [--3 1]]
        ~[[--4 1] [--5 1] [--6 1]]
        ~[[--7 1] [--8 1] [--10 1]]
    ==
  ;:  weld
    ::  x^2 - 5x - 2
    %+  expect-eq
      !>(`qol`~[[-2 1] [-5 1] [--1 1]])
    !>((charpoly:qm ma))
    ::  a diagonal matrix: (x-2)(x-3) = x^2 - 5x + 6
    %+  expect-eq
      !>(`qol`~[[--6 1] [-5 1] [--1 1]])
    !>((charpoly:qm md))
    ::  a rotation: x^2 + 1, irreducible over Q
    %+  expect-eq
      !>(`qol`~[[--1 1] [--0 1] [--1 1]])
    !>((charpoly:qm mr))
    ::  a Jordan block: (x-5)^2 = x^2 - 10x + 25
    %+  expect-eq
      !>(`qol`~[[--25 1] [-10 1] [--1 1]])
    !>((charpoly:qm mj))
    ::  odd dimension, where det(xI - A) and det(A - xI) finally differ
    %+  expect-eq
      !>(`qol`~[[--3 1] [-12 1] [-16 1] [--1 1]])
    !>((charpoly:qm mt))
    ::  a 1x1 matrix [c] has characteristic polynomial x - c
    %+  expect-eq
      !>(`qol`~[[-7 1] [--1 1]])
    !>((charpoly:qm ~[~[[--7 1]]]))
  ==
++  test-p3-eigen
  =/  md=qmat  ~[~[[--2 1] [--0 1]] ~[[--0 1] [--3 1]]]
  =/  mr=qmat  ~[~[[--0 1] [-1 1]] ~[[--1 1] [--0 1]]]
  =/  mj=qmat  ~[~[[--5 1] [--1 1]] ~[[--0 1] [--5 1]]]
  =/  ma=qmat  ~[~[[--1 1] [--2 1]] ~[[--3 1] [--4 1]]]
  ;:  weld
    ::  a diagonal matrix: its diagonal, ascending
    %+  expect-eq
      !>(`(list [val=frac mult=@ud])`~[[[--2 1] 1] [[--3 1] 1]])
    !>((eigen:qm md))
    ::  a repeated eigenvalue keeps its multiplicity
    %+  expect-eq
      !>(`(list [val=frac mult=@ud])`~[[[--5 1] 2]])
    !>((eigen:qm mj))
    ::  a rotation has NO rational eigenvalues -- the honest answer is ~,
    ::  not an approximation
    %+  expect-eq  !>(`(list [val=frac mult=@ud])`~)  !>((eigen:qm mr))
    ::  irrational eigenvalues are likewise absent
    %+  expect-eq  !>(`(list [val=frac mult=@ud])`~)  !>((eigen:qm ma))
    ::  a 1x1 matrix has its entry as its eigenvalue
    %+  expect-eq
      !>(`(list [val=frac mult=@ud])`~[[[-3 4] 1]])
    !>((eigen:qm ~[~[[-3 4]]]))
    ::  fractional eigenvalues come out exact
    %+  expect-eq
      !>(`(list [val=frac mult=@ud])`~[[[-1 3] 1] [[--1 2] 1]])
    !>((eigen:qm ~[~[[--1 2] [--0 1]] ~[[--0 1] [-1 3]]]))
  ==
::
+|  %p3-properties
::  Property: the characteristic polynomial is monic of degree n.
++  test-p3-prop-charpoly-monic
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n   r:(dims:qm m)
  =/  cp  (charpoly:qm m)
  ?&  =(+(n) (lent cp))
      =(one:qq (rear cp))
  ==
::  Property: the constant term of det(xI - A) is (-1)^n det(A), and the
::  x^(n-1) coefficient is -trace(A).  Both are standard identities and
::  both would break under the det(A - xI) convention.
++  test-p3-prop-charpoly-coeffs
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n   r:(dims:qm m)
  =/  cp  (charpoly:qm m)
  =/  tr=frac
    =/  i=@ud     0
    =/  acc=frac  zero:qq
    |-  ^-  frac
    ?:  (gte i n)  acc
    $(i +(i), acc (add:qq acc (get:qm m i i)))
  =/  d=frac  (det:qm m)
  ?&  ::  constant term
      =/  k=frac  (snag 0 `qol`cp)
      =(k ?:(=(0 (mod n 2)) d (neg:qq d)))
      ::  the next-to-leading coefficient
      =(=(0 n) %.n)
      =/  s=frac  (snag (dec n) `qol`cp)
      =(s (neg:qq tr))
  ==
::  Property: every rational eigenvalue really is a root of the
::  characteristic polynomial, and total multiplicity never exceeds n.
++  test-p3-prop-eigen-roots
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n    r:(dims:qm m)
  =/  cp   (charpoly:qm m)
  =/  evs  (eigen:qm m)
  ?&  %+  levy  evs
      |=([val=frac mult=@ud] =(zero:qq (eval:qx cp val)))
      ::  multiplicities are positive and sum to at most n
      (levy evs |=([val=frac mult=@ud] (gth mult 0)))
      =/  tot=@ud
        =/  es=(list [val=frac mult=@ud])  evs
        =/  acc=@ud  0
        |-  ^-  @ud
        ?~  es  acc
        $(es t.es, acc (add acc mult.i.es))
      (lte tot n)
  ==
::  Property: an eigenvalue makes A - lambda*I singular, which is the
::  defining property and is checked independently of how it was found.
++  test-p3-prop-eigen-singular
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  n  r:(dims:qm m)
  %+  levy  (eigen:qm m)
  |=  [val=frac mult=@ud]
  =/  shifted  (sub:qm m (scale:qm (idn:qm n) val))
  ?&  =(zero:qq (det:qm shifted))
      ::  and so has a nonempty kernel
      (gth (lent (nullspace:qm shifted)) 0)
  ==
::  Property: eigenvalues are strictly ascending, hence sorted and distinct.
++  test-p3-prop-eigen-sorted
  %+  expect-eq  !>(~)
  !>  ^-  (list qmat)
  %+  skip  (qsquares seed-qm 24)
  |=  m=qmat
  =/  es=(list [val=frac mult=@ud])  (eigen:qm m)
  |-  ^-  ?
  ?~  es  %.y
  ?~  t.es  %.y
  ?&(=(%lt (cmp:qq val.i.es val.i.t.es)) $(es t.es))
::
+|  %p3-crashes
::  S8: +charpoly requires square input.
++  test-p3-crash-charpoly-nonsquare
  =/  w=qmat  ~[~[[--1 1] [--2 1] [--3 1]]]
  ;:  weld
    (expect-fail |.((charpoly:qm w)))
    (expect-fail |.((eigen:qm w)))
  ==
++  test-p3-nocrash
  =/  mr=qmat  ~[~[[--0 1] [-1 1]] ~[[--1 1] [--0 1]]]
  ;:  weld
    ::  no rational eigenvalues produces ~, not a crash
    (expect-success |.((eigen:qm mr)))
    (expect-success |.((eigen:qm (zeros:qm 3 3))))
    (expect-success |.((charpoly:qm (zeros:qm 3 3))))
    (expect-success |.((charpoly:qm ~[~[[--7 1]]])))
  ==
::
+|  %p3-vectors
++  test-p3-vec-charpoly
  %+  expect-eq  !>(~)
  !>  %+  skip  charpoly-vectors:vec
      |=  [a=qmat cp=qol]
      =(cp (charpoly:qm a))
::
++  test-p3-vec-eigen
  %+  expect-eq  !>(~)
  !>  %+  skip  eigen-vectors:vec
      |=  [a=qmat evs=(list [val=frac mult=@ud])]
      =(evs (eigen:qm a))
--
