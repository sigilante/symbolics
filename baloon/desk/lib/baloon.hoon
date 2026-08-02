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
::  Phases 0 through 2: shape, arithmetic, and elimination.
::
::  Jet registration follows /lib/racoon, which follows urbit/numerics
::  /lib/math.hoon: one root ~% under %non, then ~/ per nested core.
::
/-  *baloon, *racoon
/+  racoon
::  Racoon's cores.  +qx is bound when Phase 3's +charpoly lands.
=/  qq  qq:racoon
=/  nz  nz:racoon
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
  ::    +vscale:  multiply every entry of a vector by a scalar
  ++  vscale
    |=  [v=qvec x=frac]
    ^-  qvec
    (turn v |=(f=frac (mul:qq x f)))
  ::    +vaxpy:  y - x * v, the elimination step
  ::
  ::  Subtracting a multiple of one row from another is the whole of
  ::  Gauss-Jordan, so it is worth having as one arm rather than a compose.
  ++  vaxpy
    |=  [y=qvec v=qvec x=frac]
    ^-  qvec
    ?~  y  ~
    ?~  v  ~
    [(sub:qq i.y (mul:qq x i.v)) $(y t.y, v t.v)]
  ::    +is-zed:  is this rational zero?
  ++  is-zed
    |=  f=frac
    ^-  ?
    =(--0 p.f)
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
  ::    +zat:  index into a row of integers
  ++  zat
    |=  [v=(list @s) i=@ud]
    ^-  @s
    ?~  v  !!
    ?:  =(0 i)  i.v
    $(v t.v, i (dec i))
  ::    +zrow:  extract one row of an integer matrix
  ++  zrow
    |=  [m=(list (list @s)) i=@ud]
    ^-  (list @s)
    ?~  m  !!
    ?:  =(0 i)  i.m
    $(m t.m, i (dec i))
  ::    +zput:  replace one row of an integer matrix
  ++  zput
    |=  [m=(list (list @s)) i=@ud r=(list @s)]
    ^-  (list (list @s))
    ?~  m  !!
    ?:  =(0 i)  [r t.m]
    [i.m $(m t.m, i (dec i))]
  ::    +bareiss:  the determinant of an integer matrix, fraction-free
  ::
  ::  [m=(list (list @s)) n=@ud] -> @s, for an n x n integer matrix.
  ::
  ::  Bareiss (1968).  Each elimination step computes
  ::
  ::      a[i][j] <- (a[i][j] * a[k][k] - a[i][k] * a[k][j]) / prev
  ::
  ::  where .prev is the previous pivot, starting at 1.  Sylvester's
  ::  identity guarantees that division is EXACT, so every intermediate
  ::  stays an integer and no denominators ever appear.  That is the whole
  ::  point: eliminating over Q instead would swell denominators badly.
  ::
  ::  On a zero pivot the algorithm swaps in a nonzero row below and flips
  ::  the sign; if the whole column below is zero the matrix is singular
  ::  and the determinant is --0.
  ++  bareiss
    |=  [m=(list (list @s)) n=@ud]
    ^-  @s
    =/  cur=(list (list @s))  m
    =/  prev=@s               --1
    =/  sgn=@s                --1
    =/  k=@ud                 0
    |-  ^-  @s
    ?:  =(k (dec n))  (pro:si sgn (zat (zrow cur k) k))
    ::  ensure a nonzero pivot at [k][k], swapping and flipping sign
    =/  pk=@s  (zat (zrow cur k) k)
    ?:  =(--0 pk)
      =/  hit=(unit @ud)
        =/  i=@ud  +(k)
        |-  ^-  (unit @ud)
        ?:  (gte i n)  ~
        ?.  =(--0 (zat (zrow cur i) k))  `i
        $(i +(i))
      ?~  hit  --0
      ::  retry the same k with the rows swapped; the enclosing |- is the
      ::  loop, so this is $ and not ^$, which would reach past it to the
      ::  gate where cur and sgn are not sample faces
      %=  $
        cur  (zput (zput cur k (zrow cur u.hit)) u.hit (zrow cur k))
        sgn  (dif:si --0 sgn)
      ==
    =/  nxt=(list (list @s))
      =/  i=@ud                 +(k)
      =/  acc=(list (list @s))  cur
      |-  ^-  (list (list @s))
      ?:  (gte i n)  acc
      =/  aik=@s  (zat (zrow acc i) k)
      =/  nr=(list @s)
        %+  turn  (gulf 0 (dec n))
        |=  j=@ud
        ^-  @s
        ?:  (lte j k)  (zat (zrow acc i) j)
        %+  fra:si
          %+  dif:si
            (pro:si (zat (zrow acc i) j) pk)
          (pro:si aik (zat (zrow acc k) j))
        prev
      $(i +(i), acc (zput acc i nr))
    $(cur nxt, prev pk, k +(k))
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
  ::  Phases 0 through 2 below.  Phase 3 adds charpoly and eigen.
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
    ::    +rref:  reduced row echelon form, with pivot columns
    ::
    ::  [m=qmat] -> qrref.  Gauss-Jordan.  The form is unique for a given
    ::  matrix, which is what makes this arm `free`.
    ::
    ::  Pivot selection is the FIRST nonzero at or below the current row --
    ::  deterministic and exact.  There is no magnitude-based partial
    ::  pivoting here because there is no rounding error to control; that
    ::  technique belongs to Lagoon's world, not this one.
    ::
    ::  Never crashes: every matrix has an RREF.
    ++  rref
      ~/  %rref
      |=  m=qmat
      ^-  qrref
      =/  d  (dims m)
      =/  cur=qmat          m
      =/  piv=(list @ud)    ~
      =/  r=@ud             0
      =/  j=@ud             0
      |-  ^-  qrref
      ?:  ?|((gte r r.d) (gte j c.d))  [cur (flop piv)]
      ::  find the first nonzero at or below row r in column j
      =/  hit=(unit @ud)
        =/  i=@ud  r
        |-  ^-  (unit @ud)
        ?:  (gte i r.d)  ~
        ?.  (is-zed:pv (vat:pv (mrow:pv cur i) j))  `i
        $(i +(i))
      ?~  hit  $(j +(j))
      ::  bring it to row r, then scale that row to a leading 1
      =/  swapped=qmat
        ?:  =(u.hit r)  cur
        %^  mput:pv  (mput:pv cur r (mrow:pv cur u.hit))  u.hit
        (mrow:pv cur r)
      =/  pr=qvec   (mrow:pv swapped r)
      =/  lead=frac  (vat:pv pr j)
      =/  unit=qvec  (vscale:pv pr (inv:qq lead))
      =/  based=qmat  (mput:pv swapped r unit)
      ::  clear column j in every OTHER row -- reduced, not merely echelon
      =/  cleared=qmat
        =/  i=@ud     0
        =/  acc=qmat  based
        |-  ^-  qmat
        ?:  (gte i r.d)  acc
        ?:  =(i r)  $(i +(i))
        =/  fac=frac  (vat:pv (mrow:pv acc i) j)
        ?:  (is-zed:pv fac)  $(i +(i))
        $(i +(i), acc (mput:pv acc i (vaxpy:pv (mrow:pv acc i) unit fac)))
      %=  $
        cur  cleared
        piv  [j piv]
        r    +(r)
        j    +(j)
      ==
    ::    +rank:  the rank of a matrix
    ::
    ::  The number of pivot columns of the RREF.  Never crashes.
    ++  rank
      |=  m=qmat
      ^-  @ud
      (lent piv:(rref m))
    ::    +det:  the determinant
    ::
    ::  [m=qmat] -> frac.  Crashes on a non-square input (SPEC S8).
    ::
    ::  Bareiss fraction-free elimination over Z (SPEC B4).  Plain
    ::  Gauss-Jordan over Q would be shorter, but rational elimination
    ::  swells denominators badly; Bareiss keeps every intermediate an
    ::  exact integer, each division being exact by Sylvester's identity.
    ::  So: clear denominators, eliminate over Z, then divide the scaling
    ::  back out.  The same discipline +gcd:qx uses in delegating to +zx.
    ++  det
      ~/  %det
      |=  m=qmat
      ^-  frac
      =/  d  (dims m)
      ?>  =(r.d c.d)
      ::  clear denominators row by row: scaling row i by L_i multiplies
      ::  the determinant by L_i, so divide by their product at the end
      =/  ls=(list @ud)
        %+  turn  m
        |=  v=qvec
        ^-  @ud
        =/  acc=@ud  1
        |-  ^-  @ud
        ?~  v  acc
        $(v t.v, acc (^div (^mul acc q.i.v) (gcd:nz acc q.i.v)))
      =/  zm=(list (list @s))
        =/  rows=qmat        m
        =/  fs=(list @ud)    ls
        |-  ^-  (list (list @s))
        ?~  rows  ~
        ?~  fs  ~
        :-  ^-  (list @s)
            %+  turn  i.rows
            |=(f=frac (pro:si p.f (sun:si (^div i.fs q.f))))
        $(rows t.rows, fs t.fs)
      =/  dz=@s  (bareiss:pv zm r.d)
      =/  scale=@ud
        =/  fs=(list @ud)  ls
        =/  acc=@ud        1
        |-  ^-  @ud
        ?~  fs  acc
        $(fs t.fs, acc (^mul acc i.fs))
      (new:qq dz scale)
    ::    +inv:  the matrix inverse
    ::
    ::  Crashes on a non-square input and on a singular one (SPEC S8).
    ::  Gauss-Jordan on [m | I]: when m is invertible the left half reduces
    ::  to the identity and the right half is the inverse.
    ++  inv
      ~/  %inv
      |=  m=qmat
      ^-  qmat
      =/  d  (dims m)
      ?>  =(r.d c.d)
      =/  aug=qmat
        =/  rows=qmat  m
        =/  eye=qmat   (idn r.d)
        |-  ^-  qmat
        ?~  rows  ~
        ?~  eye  ~
        [(weld i.rows i.eye) $(rows t.rows, eye t.eye)]
      =/  rr  (rref aug)
      ::  the left half reduces to the identity exactly when m is invertible
      ?>  =(piv.rr (gulf 0 (dec r.d)))
      %+  turn  m.rr
      |=(v=qvec ^-(qvec (slag r.d v)))
    ::    +solve:  solve a*x = b
    ::
    ::  [a=qmat b=qmat] -> (unit qmat).  Requires a square and with as many
    ::  rows as b; crashes otherwise (SPEC S8).  Produces ~ exactly when a
    ::  is singular, and the unique solution otherwise.
    ::
    ::  This is deliberately not a least-squares or parametric solver: a
    ::  non-unique answer would not be canonical, and B1 admits no such arm.
    ++  solve
      ~/  %solve
      |=  [a=qmat b=qmat]
      ^-  (unit qmat)
      =/  da  (dims a)
      =/  db  (dims b)
      ?>  =(r.da c.da)
      ?>  =(r.da r.db)
      =/  aug=qmat
        =/  rows=qmat  a
        =/  rhs=qmat   b
        |-  ^-  qmat
        ?~  rows  ~
        ?~  rhs  ~
        [(weld i.rows i.rhs) $(rows t.rows, rhs t.rhs)]
      =/  rr  (rref aug)
      ?.  =(piv.rr (gulf 0 (dec r.da)))  ~
      :-  ~
      %+  turn  m.rr
      |=(v=qvec ^-(qvec (slag r.da v)))
    ::    +nullspace:  a basis for the kernel
    ::
    ::  [m=qmat] -> (list qvec).  Empty exactly when m has full column
    ::  rank.  Never crashes.
    ::
    ::  The basis is PINNED by SPEC S7, because a kernel basis is not
    ::  otherwise unique: for each non-pivot (free) column j, one vector
    ::  with 1 at j, 0 at every other free column, and -(rref entry) at
    ::  each pivot position, ordered by ascending j.  Pinning the
    ::  convention rather than an algorithm is what keeps the product
    ::  canonical while leaving a jet free.
    ++  nullspace
      |=  m=qmat
      ^-  (list qvec)
      =/  d   (dims m)
      =/  rr  (rref m)
      =/  free=(list @ud)
        %+  skip  (gulf 0 (dec c.d))
        |=(j=@ud (lien piv.rr |=(k=@ud =(k j))))
      %+  turn  free
      |=  j=@ud
      ^-  qvec
      %+  turn  (gulf 0 (dec c.d))
      |=  k=@ud
      ^-  frac
      ?:  =(k j)  one:qq
      ::  a pivot column contributes the negated RREF entry in row (index
      ::  of that pivot); a different free column contributes zero
      =/  at=(unit @ud)
        =/  ps=(list @ud)  piv.rr
        =/  i=@ud          0
        |-  ^-  (unit @ud)
        ?~  ps  ~
        ?:  =(i.ps k)  `i
        $(ps t.ps, i +(i))
      ?~  at  zero:qq
      (neg:qq (vat:pv (mrow:pv m.rr u.at) j))
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
