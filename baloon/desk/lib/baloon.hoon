  ::  /lib/baloon
::::  Baloon, Basic linear ALgebra in hOON
::
::  Exact linear algebra over Q, built entirely on Racoon.  No floating
::  point anywhere: Lagoon owns the approximate case, Baloon the exact one,
::  and the two are siblings rather than layers.
::
::  This library is the specification; native jets must be Kleene-equal to
::  it on every input.  Every product here is a canonical mathematical
::  object -- the determinant, the reduced row echelon form, the rank, the
::  inverse, the characteristic polynomial are each unique for a given
::  input -- so every arm is `free` and a jet may use any algorithm.  Where
::  uniqueness needs help, as with the nullspace basis, SPEC S7 pins a
::  CONVENTION rather than an algorithm.
::
::  Phases 0 and 1: shape, construction, and arithmetic.
::
::  Jet registration follows /lib/racoon, which follows urbit/numerics
::  /lib/math.hoon: one root ~% under %non, then ~/ per nested core.
::
/-  *baloon, *racoon
/+  racoon
::  Racoon's scalar cores.  Further cores are bound as the phases that need
::  them land: +zx for the fraction-free determinant, +qx for +charpoly.
=/  qq  qq:racoon
=<  baloon
~%  %non  ..part  ~
|%
+|  %private
::    +pv:  private helpers, not part of the public API
::
::  Outside the %baloon jet core, so that helper churn cannot disturb the
::  battery layout of a hinted core.
::
::  The indexing helpers are written out rather than delegated to ++snag,
::  which carries a ~_ hint and so puts "snag-fail" into the crash trace.
::  Trace payloads are observable under virtualization and would become
::  part of the jet contract; SPEC B3 keeps them out.  These crash bare.
++  pv
  |%
  ::    +vat:  index into a vector
  ::
  ::  [v=qvec i=@ud] -> frac.  Crashes bare when i is out of range.
  ++  vat
    |=  [v=qvec i=@ud]
    ^-  frac
    ?~  v  !!
    ?:  =(0 i)  i.v
    $(v t.v, i (dec i))
  ::    +vput:  replace one entry of a vector
  ::
  ::  [v=qvec i=@ud x=frac] -> qvec.  Crashes bare when i is out of range.
  ++  vput
    |=  [v=qvec i=@ud x=frac]
    ^-  qvec
    ?~  v  !!
    ?:  =(0 i)  [x t.v]
    [i.v $(v t.v, i (dec i))]
  ::    +mrow:  extract one row of a matrix
  ::
  ::  [m=qmat i=@ud] -> qvec.  Crashes bare when i is out of range.
  ++  mrow
    |=  [m=qmat i=@ud]
    ^-  qvec
    ?~  m  !!
    ?:  =(0 i)  i.m
    $(m t.m, i (dec i))
  ::    +mput:  replace one row of a matrix
  ::
  ::  [m=qmat i=@ud r=qvec] -> qmat.  Crashes bare when i is out of range.
  ++  mput
    |=  [m=qmat i=@ud r=qvec]
    ^-  qmat
    ?~  m  !!
    ?:  =(0 i)  [r t.m]
    [i.m $(m t.m, i (dec i))]
  ::    +vadd:  elementwise sum of two vectors
  ::
  ::  The callers check dimensions first, so the two lists always run out
  ::  together; a short list simply terminates the walk.
  ++  vadd
    |=  [x=qvec y=qvec]
    ^-  qvec
    ?~  x  ~
    ?~  y  ~
    [(add:qq i.x i.y) $(x t.x, y t.y)]
  ::    +vsub:  elementwise difference of two vectors
  ++  vsub
    |=  [x=qvec y=qvec]
    ^-  qvec
    ?~  x  ~
    ?~  y  ~
    [(sub:qq i.x i.y) $(x t.x, y t.y)]
  ::    +dot:  the inner product of two vectors
  ::
  ::  Produces the zero rational on an empty vector, which cannot arise for
  ::  canonical input since every row has at least one entry.
  ++  dot
    |=  [x=qvec y=qvec]
    ^-  frac
    ?~  x  zero:qq
    ?~  y  zero:qq
    (add:qq (mul:qq i.x i.y) $(x t.x, y t.y))
  --
+|  %public
++  baloon
  ~/  %baloon
  |%
  +|  %rationals
  ::    +qm:  matrices over Q
  ::
  ::  Every arm requires canonical input (SPEC S7) and produces canonical
  ::  output; +canon is the sole exception.  Ragged and empty matrices are
  ::  outside the supported domain: the Hoon computes deterministically and
  ::  a Milestone B jet detects the violation and falls back.
  ::
  ::  Phases 0 and 1 below.  Phase 2 adds rref, rank, det, inv, solve, and
  ::  nullspace; Phase 3 adds charpoly and eigen.
  ++  qm
    ~/  %qm
    |%
    ::    +canon:  impose the canonical form on the entries
    ::
    ::  [m=qmat] -> qmat.  Re-canonicalizes every entry through +new:qq.
    ::  The only arm that accepts non-canonical input.
    ::
    ::  Does NOT repair raggedness: a ragged matrix is outside the
    ::  supported domain, not a form this arm is expected to normalize.
    ::  Crashes on a zero denominator, through +new:qq.
    ++  canon
      |=  m=qmat
      ^-  qmat
      %+  turn  m
      |=  r=qvec
      ^-  qvec
      (turn r |=(f=frac (new:qq p.f q.f)))
    ::    +dims:  the dimensions of a matrix
    ::
    ::  [m=qmat] -> [r=@ud c=@ud].  Derived rather than stored.  Crashes
    ::  on the empty matrix, which the canonical form excludes.
    ++  dims
      |=  m=qmat
      ^-  [r=@ud c=@ud]
      ?~  m  !!
      [(lent m) (lent i.m)]
    ::    +is-square:  does the matrix have as many rows as columns?
    ++  is-square
      |=  m=qmat
      ^-  ?
      =/  d  (dims m)
      =(r.d c.d)
    ::    +get:  the entry at row i, column j
    ::
    ::  Zero-based.  Crashes when either index is out of range (SPEC S8).
    ::  The bounds are checked here so that the crash is bare rather than
    ::  whatever the accessor would have produced.
    ++  get
      |=  [m=qmat i=@ud j=@ud]
      ^-  frac
      =/  d  (dims m)
      ?>  ?&((lth i r.d) (lth j c.d))
      (vat:pv (mrow:pv m i) j)
    ::    +put:  replace the entry at row i, column j
    ::
    ::  Crashes when either index is out of range (SPEC S8).
    ++  put
      |=  [m=qmat i=@ud j=@ud x=frac]
      ^-  qmat
      =/  d  (dims m)
      ?>  ?&((lth i r.d) (lth j c.d))
      (mput:pv m i (vput:pv (mrow:pv m i) j x))
    ::    +row:  extract row i
    ::
    ::  Crashes when i is out of range (SPEC S8).
    ++  row
      |=  [m=qmat i=@ud]
      ^-  qvec
      =/  d  (dims m)
      ?>  (lth i r.d)
      (mrow:pv m i)
    ::    +col:  extract column j
    ::
    ::  Crashes when j is out of range (SPEC S8).
    ++  col
      |=  [m=qmat j=@ud]
      ^-  qvec
      =/  d  (dims m)
      ?>  (lth j c.d)
      (turn m |=(r=qvec (vat:pv r j)))
    ::    +transpose:  exchange rows and columns
    ::
    ::  The product of an r x c matrix is c x r, and is canonical whenever
    ::  the input is.  Involutive: transpose(transpose(m)) = m.
    ++  transpose
      |=  m=qmat
      ^-  qmat
      =/  d  (dims m)
      %+  turn  (gulf 0 (dec c.d))
      |=(j=@ud ^-(qvec (turn m |=(r=qvec (vat:pv r j)))))
    ::    +idn:  the n x n identity matrix
    ::
    ::  Crashes on n = 0: the empty matrix is not representable (SPEC S8).
    ++  idn
      |=  n=@ud
      ^-  qmat
      ?>  (gth n 0)
      %+  turn  (gulf 0 (dec n))
      |=  i=@ud
      ^-  qvec
      %+  turn  (gulf 0 (dec n))
      |=(j=@ud ?:(=(i j) one:qq zero:qq))
    ::    +zeros:  the r x c zero matrix
    ::
    ::  Crashes on r = 0 or c = 0 (SPEC S8).
    ++  zeros
      |=  [r=@ud c=@ud]
      ^-  qmat
      ?>  ?&((gth r 0) (gth c 0))
      %+  turn  (gulf 0 (dec r))
      |=  *
      ^-  qvec
      (reap c zero:qq)
    ::    +add:  matrix addition
    ::
    ::  [a=qmat b=qmat] -> qmat.  Elementwise.  Crashes on a dimension
    ::  mismatch (SPEC S8).
    ::
    ::  No canonicalization is needed: entry sums come from +add:qq, which
    ::  is canonical, and a matrix has no trailing-zero form to strip.  This
    ::  is where matrices are simpler than Racoon's polynomials, whose +add
    ::  must canonicalize because leading terms can cancel.
    ++  add
      |=  [a=qmat b=qmat]
      ^-  qmat
      ?>  =((dims a) (dims b))
      |-  ^-  qmat
      ?~  a  ~
      ?~  b  ~
      [(vadd:pv i.a i.b) $(a t.a, b t.b)]
    ::    +neg:  matrix negation
    ++  neg
      |=  m=qmat
      ^-  qmat
      %+  turn  m
      |=(r=qvec ^-(qvec (turn r neg:qq)))
    ::    +sub:  matrix subtraction
    ::
    ::  Crashes on a dimension mismatch (SPEC S8).
    ++  sub
      |=  [a=qmat b=qmat]
      ^-  qmat
      ?>  =((dims a) (dims b))
      |-  ^-  qmat
      ?~  a  ~
      ?~  b  ~
      [(vsub:pv i.a i.b) $(a t.a, b t.b)]
    ::    +scale:  multiply every entry by a scalar
    ::
    ::  Scaling by zero produces the zero matrix, which is canonical: a
    ::  matrix has no notion of collapsing to a smaller shape.
    ++  scale
      |=  [m=qmat x=frac]
      ^-  qmat
      %+  turn  m
      |=(r=qvec ^-(qvec (turn r |=(f=frac (mul:qq x f)))))
    ::    +mul:  matrix multiplication
    ::
    ::  [a=qmat b=qmat] -> qmat, of shape rows(a) x cols(b).  Crashes
    ::  unless cols(a) = rows(b) (SPEC S8).
    ::
    ::  Transposing b once up front turns every entry of the product into
    ::  an inner product of two ROWS, which is the cheap direction on
    ::  nested lists -- walking a column otherwise costs a traversal per
    ::  entry.
    ++  mul
      ~/  %mul
      |=  [a=qmat b=qmat]
      ^-  qmat
      ?>  =(c:(dims a) r:(dims b))
      =/  bt=qmat  (transpose b)
      %+  turn  a
      |=  r=qvec
      ^-  qvec
      (turn bt |=(s=qvec (dot:pv r s)))
    ::    +pow:  matrix power
    ::
    ::  [m=qmat e=@ud] -> qmat.  Binary square-and-multiply.  m^0 is the
    ::  identity of matching size, including for the zero matrix.  Crashes
    ::  on a non-square input (SPEC S8).
    ++  pow
      |=  [m=qmat e=@ud]
      ^-  qmat
      =/  d  (dims m)
      ?>  =(r.d c.d)
      ?:  =(0 e)  (idn r.d)
      =/  k=@ud     (dec (met 0 e))
      =/  acc=qmat  m
      |-  ^-  qmat
      ?:  =(0 k)  acc
      =/  nk=@ud    (dec k)
      =/  sq=qmat   (mul acc acc)
      %=  $
        k    nk
        acc  ?:(=(1 (cut 0 [nk 1] e)) (mul sq m) sq)
      ==
    --
  +|  %reserved
  ::    +zm:  matrices over Z.  Milestone C.
  ::
  ::  Declared empty deliberately.  Adding an arm to a Hoon core moves the
  ::  battery axes of the arms already in it, so introducing a sub-core
  ::  when its milestone arrives would shift the %baloon battery -- and
  ::  that is the parent axis every sub-core jet resolves against.  This is
  ::  Racoon's Q5, applied up front rather than retrofitted.
  ++  zm
    ~/  %zm
    |%
    --
  ::    +mm:  matrices over Z/n, a door on the modulus.  Milestone C.
  ::
  ::  Three sub-cores, not four: F_p is Z/n with n prime, so it shares
  ::  $mmat and this door, exactly as Racoon serves both from +mx.
  ++  mm
    ~/  %mm
    |_  n=@ud
    --
  --
--
