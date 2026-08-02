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
::  Phases 0 through 3: shape, arithmetic, elimination, and spectra.
::
::  Jet registration follows /lib/racoon, which follows urbit/numerics
::  /lib/math.hoon: one root ~% under %non, then ~/ per nested core.
::
/-  *baloon, *racoon
/+  racoon
::  Racoon's cores.  +qx carries the characteristic polynomial; +zx
::  factors it, which is how the rational eigenvalues come out exact.
=/  qq  qq:racoon
=/  nz  nz:racoon
=/  zx  zx:racoon
=/  mx  mx:racoon
=/  qx  qx:racoon
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
  ::    +lagrange:  the unique polynomial through a set of points
  ::
  ::  [(list [x=frac y=frac])] -> qol, of degree below the point count.
  ::  The x values must be pairwise distinct, which the caller guarantees
  ::  by sampling at 0, 1, ..., n.
  ::
  ::  Sum over i of y_i times the basis polynomial that is 1 at x_i and 0
  ::  at every other node.  Built with +qx arithmetic, so every
  ::  coefficient stays an exact rational.
  ++  lagrange
    |=  pts=(list [x=frac y=frac])
    ^-  qol
    =/  all=(list [x=frac y=frac])  pts
    =/  rest=(list [x=frac y=frac])  pts
    =|  acc=qol
    |-  ^-  qol
    ?~  rest  acc
    ::  basis_i(t) = prod over j /= i of (t - x_j) / (x_i - x_j)
    =/  basis=qol
      =/  js=(list [x=frac y=frac])  all
      =/  b=qol  ~[one:qq]
      |-  ^-  qol
      ?~  js  b
      ?:  =(x.i.js x.i.rest)  $(js t.js)
      =/  den=frac  (sub:qq x.i.rest x.i.js)
      =/  lin=qol   ~[(neg:qq (div:qq x.i.js den)) (inv:qq den)]
      $(js t.js, b (mul:qx b lin))
    $(rest t.rest, acc (add:qx acc (scale:qx basis y.i.rest)))
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
  ::    +zvput:  replace one entry of an integer vector
  ++  zvput
    |=  [v=(list @s) i=@ud x=@s]
    ^-  (list @s)
    ?~  v  !!
    ?:  =(0 i)  [x t.v]
    [i.v $(v t.v, i (dec i))]
  ::    +zvadd:  elementwise sum of two integer vectors
  ++  zvadd
    |=  [a=(list @s) b=(list @s)]
    ^-  (list @s)
    ?~  a  ~
    ?~  b  ~
    [(sum:si i.a i.b) $(a t.a, b t.b)]
  ::    +zvsub:  elementwise difference of two integer vectors
  ++  zvsub
    |=  [a=(list @s) b=(list @s)]
    ^-  (list @s)
    ?~  a  ~
    ?~  b  ~
    [(dif:si i.a i.b) $(a t.a, b t.b)]
  ::    +zdot:  inner product of two integer vectors
  ::
  ::  Runs to the shorter of the two, which the callers never exercise --
  ::  every use here has already checked the shapes agree.
  ++  zdot
    |=  [a=(list @s) b=(list @s)]
    ^-  @s
    =/  acc=@s  --0
    |-  ^-  @s
    ?~  a  acc
    ?~  b  acc
    $(a t.a, b t.b, acc (sum:si acc (pro:si i.a i.b)))
  ::    +lcmn:  least common multiple over the naturals
  ::
  ::  Divides before multiplying, so the intermediate never exceeds the
  ::  result.  lcm(0, b) = 0, which is the convention +gcd:nz implies.
  ++  lcmn
    |=  [a=@ud b=@ud]
    ^-  @ud
    ?:  ?|(=(0 a) =(0 b))  0
    (mul (div a (gcd:nz a b)) b)
  ::    +nat:  index into a modular vector
  ++  nat
    |=  [v=(list @ud) i=@ud]
    ^-  @ud
    ?~  v  !!
    ?:  =(0 i)  i.v
    $(v t.v, i (dec i))
  ::    +nvput:  replace one entry of a modular vector
  ++  nvput
    |=  [v=(list @ud) i=@ud x=@ud]
    ^-  (list @ud)
    ?~  v  !!
    ?:  =(0 i)  [x t.v]
    [i.v $(v t.v, i (dec i))]
  ::    +nrow:  extract one row of a modular matrix
  ++  nrow
    |=  [m=(list (list @ud)) i=@ud]
    ^-  (list @ud)
    ?~  m  !!
    ?:  =(0 i)  i.m
    $(m t.m, i (dec i))
  ::    +nput:  replace one row of a modular matrix
  ++  nput
    |=  [m=(list (list @ud)) i=@ud r=(list @ud)]
    ^-  (list (list @ud))
    ?~  m  !!
    ?:  =(0 i)  [r t.m]
    [i.m $(m t.m, i (dec i))]
  ::    +nvadd:  elementwise sum of two vectors mod n
  ::
  ::  These three replicate +cadd:mx, +csub:mx, and +cmul:mx exactly
  ::  rather than threading the door through +pv.  Entries are assumed
  ::  already in [0, n) -- the canonical form guarantees it.
  ++  nvadd
    |=  [n=@ud a=(list @ud) b=(list @ud)]
    ^-  (list @ud)
    ?~  a  ~
    ?~  b  ~
    [(mod (add i.a i.b) n) $(a t.a, b t.b)]
  ::    +nvsub:  elementwise difference of two vectors mod n
  ++  nvsub
    |=  [n=@ud a=(list @ud) b=(list @ud)]
    ^-  (list @ud)
    ?~  a  ~
    ?~  b  ~
    [(mod (sub (add n i.a) i.b) n) $(a t.a, b t.b)]
  ::    +ndot:  inner product of two vectors mod n
  ++  ndot
    |=  [n=@ud a=(list @ud) b=(list @ud)]
    ^-  @ud
    =/  acc=@ud  0
    |-  ^-  @ud
    ?~  a  acc
    ?~  b  acc
    $(a t.a, b t.b, acc (mod (add acc (mul i.a i.b)) n))
  ::    +zmodn:  reduce a signed integer into [0, n)
  ++  zmodn
    |=  [x=@s n=@ud]
    ^-  @ud
    =/  a=@ud  (mod (abs:si x) n)
    ?:  (syn:si x)  a
    ?:(=(0 a) 0 (sub n a))
  ::    +zminor:  delete row i and column j from an integer matrix
  ++  zminor
    |=  [m=(list (list @s)) i=@ud j=@ud]
    ^-  (list (list @s))
    =/  rs=(list (list @s))  m
    =/  k=@ud                0
    =|  out=(list (list @s))
    |-  ^-  (list (list @s))
    ?~  rs  (flop out)
    ?:  =(k i)  $(rs t.rs, k +(k))
    =/  nr=(list @s)
      =/  cs=(list @s)  i.rs
      =/  l=@ud         0
      =|  acc=(list @s)
      |-  ^-  (list @s)
      ?~  cs  (flop acc)
      ?:  =(l j)  $(cs t.cs, l +(l))
      $(cs t.cs, l +(l), acc [i.cs acc])
    $(rs t.rs, k +(k), out [nr out])
  ::    +zadj:  the adjugate of an n x n integer matrix
  ::
  ::  adj(A)[i][j] = (-1)^(i+j) * det(A with row j and column i deleted).
  ::  Note the transposed index order: the adjugate is the TRANSPOSE of
  ::  the cofactor matrix, and satisfies A * adj(A) = det(A) * I over Z.
  ::
  ::  That identity is why +inv:mm can invert without pivoting at all --
  ::  it holds in any commutative ring, so reducing it mod n is legal for
  ::  every n, prime or not.  The 1 x 1 adjugate is [[1]], which the
  ::  general formula cannot express since it needs a 0 x 0 determinant.
  ++  zadj
    |=  [m=(list (list @s)) n=@ud]
    ^-  (list (list @s))
    ?:  =(1 n)  ~[~[--1]]
    %+  turn  (gulf 0 (dec n))
    |=  i=@ud
    ^-  (list @s)
    %+  turn  (gulf 0 (dec n))
    |=  j=@ud
    ^-  @s
    =/  c=@s  (bareiss (zminor m j i) (dec n))
    ?:(=(0 (mod (add i j) 2)) c (dif:si --0 c))
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
  ::  All four phases below.
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
    ::    +charpoly:  the characteristic polynomial
    ::
    ::  [m=qmat] -> qol, monic of degree n.  Crashes on a non-square input
    ::  (SPEC S8).
    ::
    ::  det(xI - A), NOT det(A - xI).  The two differ by (-1)^n and agree
    ::  only in even dimension, so a 2x2 test cannot tell them apart; the
    ::  convention is pinned in S7 and was verified against the definition
    ::  at odd dimension before being written down.
    ::
    ::  Computed by interpolation: the polynomial has degree n, so its
    ::  values at n+1 distinct points determine it.  Each value is a
    ::  determinant, which +det already computes fraction-free.  Lagrange
    ::  interpolation then recovers the coefficients.  The product is
    ::  canonical either way, so this arm is `free` like every other.
    ++  charpoly
      ~/  %charpoly
      |=  m=qmat
      ^-  qol
      =/  d  (dims m)
      ?>  =(r.d c.d)
      =/  n=@ud  r.d
      ::  sample det(tI - A) at t = 0, 1, ..., n
      =/  pts=(list [x=frac y=frac])
        %+  turn  (gulf 0 n)
        |=  k=@ud
        ^-  [x=frac y=frac]
        =/  t=frac  (new:qq (sun:si k) 1)
        :-  t
        (det (sub (scale (idn n) t) m))
      (lagrange:pv pts)
    ::    +eigen:  the RATIONAL eigenvalues, with multiplicities
    ::
    ::  [m=qmat] -> (list [val=frac mult=@ud]), ascending by +cmp:qq.
    ::  Crashes on a non-square input, through +charpoly.
    ::
    ::  IRRATIONAL AND COMPLEX EIGENVALUES ARE ABSENT, not approximated.
    ::  A rotation matrix produces ~, and that is the honest answer: this
    ::  library has no way to name sqrt(2) or i, and inventing a float
    ::  would betray the whole premise.  Callers wanting to know whether
    ::  anything was omitted should compare the total multiplicity here
    ::  against the dimension.
    ::
    ::  The characteristic polynomial is cleared of denominators and
    ::  factored over Z through +factor:zx; each LINEAR factor ax + b
    ::  contributes the root -b/a with its multiplicity.  Factors of higher
    ::  degree are irreducible over Q and so have no rational root.
    ++  eigen
      |=  m=qmat
      ^-  (list [val=frac mult=@ud])
      =/  cp=qol  (charpoly m)
      ?~  cp  ~
      =/  zp=zol  (clear:qx cp)
      ?~  zp  ~
      =/  fc  (factor:zx zp)
      =/  out=(list [val=frac mult=@ud])
        %+  murn  fs.fc
        |=  [p=zol mult=@ud]
        ^-  (unit [val=frac mult=@ud])
        ::  only a linear factor has a rational root
        ?.  =(2 (lent p))  ~
        =/  b=@s  (snag 0 `zol`p)
        =/  a=@s  (snag 1 `zol`p)
        `[(neg:qq (new:qq b (abs:si a))) mult]
      %+  sort  out
      |=  [x=[val=frac mult=@ud] y=[val=frac mult=@ud]]
      ?!(=(%gt (cmp:qq val.x val.y)))
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
    ::    +dims:  the dimensions of a matrix
    ::
    ::  [m=zmat] -> [r=@ud c=@ud].  Derived rather than stored.  Crashes
    ::  on the empty matrix, which the canonical form excludes.
    ::
    ::  There is deliberately no +canon here.  Over Q the entries carry a
    ::  normal form that +new:qq imposes; over Z every @s is already its
    ::  own canonical form, so the arm would be the identity.  An arm that
    ::  does nothing is worse than an absent one -- see also +rref and its
    ::  companions below.
    ++  dims
      |=  m=zmat
      ^-  [r=@ud c=@ud]
      ?~  m  !!
      [(lent m) (lent i.m)]
    ::    +is-square:  does the matrix have as many rows as columns?
    ++  is-square
      |=  m=zmat
      ^-  ?
      =/  d  (dims m)
      =(r.d c.d)
    ::    +get:  the entry at row i, column j
    ::
    ::  Zero-based.  Crashes when either index is out of range (SPEC S8).
    ++  get
      |=  [m=zmat i=@ud j=@ud]
      ^-  @s
      =/  d  (dims m)
      ?>  ?&((lth i r.d) (lth j c.d))
      (zat:pv (zrow:pv m i) j)
    ::    +put:  replace the entry at row i, column j
    ::
    ::  Crashes when either index is out of range (SPEC S8).
    ++  put
      |=  [m=zmat i=@ud j=@ud x=@s]
      ^-  zmat
      =/  d  (dims m)
      ?>  ?&((lth i r.d) (lth j c.d))
      (zput:pv m i (zvput:pv (zrow:pv m i) j x))
    ::    +row:  extract row i
    ::
    ::  Crashes when i is out of range (SPEC S8).
    ++  row
      |=  [m=zmat i=@ud]
      ^-  zvec
      =/  d  (dims m)
      ?>  (lth i r.d)
      (zrow:pv m i)
    ::    +col:  extract column j
    ::
    ::  Crashes when j is out of range (SPEC S8).
    ++  col
      |=  [m=zmat j=@ud]
      ^-  zvec
      =/  d  (dims m)
      ?>  (lth j c.d)
      (turn m |=(r=zvec (zat:pv r j)))
    ::    +transpose:  exchange rows and columns
    ::
    ::  Involutive: transpose(transpose(m)) = m.
    ++  transpose
      |=  m=zmat
      ^-  zmat
      =/  d  (dims m)
      %+  turn  (gulf 0 (dec c.d))
      |=(j=@ud ^-(zvec (turn m |=(r=zvec (zat:pv r j)))))
    ::    +idn:  the n x n identity matrix
    ::
    ::  Crashes on n = 0: the empty matrix is not representable (SPEC S8).
    ++  idn
      |=  n=@ud
      ^-  zmat
      ?>  (gth n 0)
      %+  turn  (gulf 0 (dec n))
      |=  i=@ud
      ^-  zvec
      %+  turn  (gulf 0 (dec n))
      |=(j=@ud ?:(=(i j) --1 --0))
    ::    +zeros:  the r x c zero matrix
    ::
    ::  Crashes on r = 0 or c = 0 (SPEC S8).
    ++  zeros
      |=  [r=@ud c=@ud]
      ^-  zmat
      ?>  ?&((gth r 0) (gth c 0))
      %+  turn  (gulf 0 (dec r))
      |=  *
      ^-  zvec
      (reap c --0)
    ::    +add:  matrix addition
    ::
    ::  Elementwise.  Crashes on a dimension mismatch (SPEC S8).
    ++  add
      |=  [a=zmat b=zmat]
      ^-  zmat
      ?>  =((dims a) (dims b))
      |-  ^-  zmat
      ?~  a  ~
      ?~  b  ~
      [(zvadd:pv i.a i.b) $(a t.a, b t.b)]
    ::    +neg:  matrix negation
    ++  neg
      |=  m=zmat
      ^-  zmat
      %+  turn  m
      |=(r=zvec ^-(zvec (turn r |=(x=@s (dif:si --0 x)))))
    ::    +sub:  matrix subtraction
    ::
    ::  Crashes on a dimension mismatch (SPEC S8).
    ++  sub
      |=  [a=zmat b=zmat]
      ^-  zmat
      ?>  =((dims a) (dims b))
      |-  ^-  zmat
      ?~  a  ~
      ?~  b  ~
      [(zvsub:pv i.a i.b) $(a t.a, b t.b)]
    ::    +scale:  multiply every entry by a scalar
    ++  scale
      |=  [m=zmat x=@s]
      ^-  zmat
      %+  turn  m
      |=(r=zvec ^-(zvec (turn r |=(y=@s (pro:si x y)))))
    ::    +mul:  matrix multiplication
    ::
    ::  [a=zmat b=zmat] -> zmat, of shape rows(a) x cols(b).  Crashes
    ::  unless cols(a) = rows(b) (SPEC S8).
    ::
    ::  Transposing b once up front turns every entry into an inner
    ::  product of two ROWS, the cheap direction on nested lists.  Same
    ::  reasoning as +mul:qm; no coefficient growth to worry about, since
    ::  Z has no denominators to swell.
    ++  mul
      ~/  %mul
      |=  [a=zmat b=zmat]
      ^-  zmat
      ?>  =(c:(dims a) r:(dims b))
      =/  bt=zmat  (transpose b)
      %+  turn  a
      |=  r=zvec
      ^-  zvec
      (turn bt |=(s=zvec (zdot:pv r s)))
    ::    +pow:  matrix power
    ::
    ::  Binary square-and-multiply.  m^0 is the identity of matching size.
    ::  Crashes on a non-square input (SPEC S8).
    ++  pow
      |=  [m=zmat e=@ud]
      ^-  zmat
      =/  d  (dims m)
      ?>  =(r.d c.d)
      ?:  =(0 e)  (idn r.d)
      =/  k=@ud     (dec (met 0 e))
      =/  acc=zmat  m
      |-  ^-  zmat
      ?:  =(0 k)  acc
      =/  nk=@ud    (dec k)
      =/  sq=zmat   (mul acc acc)
      %=  $
        k    nk
        acc  ?:(=(1 (cut 0 [nk 1] e)) (mul sq m) sq)
      ==
    ::    +to-q:  embed an integer matrix in Q
    ::
    ::  [m=zmat] -> qmat.  Exact and total: every integer x is the
    ::  canonical fraction x/1.
    ++  to-q
      |=  m=zmat
      ^-  qmat
      %+  turn  m
      |=(r=zvec ^-(qvec (turn r |=(x=@s ^-(frac [x 1])))))
    ::    +of-q:  clear denominators
    ::
    ::  [m=qmat] -> [z=zmat d=@ud] with z = d * m entrywise, where d is
    ::  the LCM of every denominator.  The denominator comes back with the
    ::  matrix because the map Q -> Z loses it otherwise, and a caller who
    ::  drops it silently computes in the wrong ring.
    ::
    ::  d is the SMALLEST such multiplier, so the pair is canonical: any
    ::  common denominator would do arithmetically, but only the least one
    ::  is a function of the input alone.
    ++  of-q
      |=  m=qmat
      ^-  [z=zmat d=@ud]
      =/  dd=@ud
        =/  rs=qmat  m
        =/  acc=@ud  1
        |-  ^-  @ud
        ?~  rs  acc
        =/  rw=@ud
          =/  cs=qvec  i.rs
          =/  x=@ud    1
          |-  ^-  @ud
          ?~  cs  x
          $(cs t.cs, x (lcmn:pv x q.i.cs))
        $(rs t.rs, acc (lcmn:pv acc rw))
      :_  dd
      %+  turn  m
      |=  r=qvec
      ^-  zvec
      %+  turn  r
      |=  f=frac
      ^-  @s
      (pro:si p.f (sun:si (div dd q.f)))
    ::    +det:  the determinant, fraction-free
    ::
    ::  [m=zmat] -> @s.  Bareiss elimination, promoted from +pv rather
    ::  than written fresh: +det:qm already reaches it by clearing
    ::  denominators, and over Z the clearing step is what disappears.
    ::  Crashes on a non-square input (SPEC S8).
    ::
    ::  Every intermediate is an integer by Sylvester's identity, so this
    ::  is exact at every step -- no denominators appear and none have to
    ::  be cancelled at the end.
    ++  det
      ~/  %det
      |=  m=zmat
      ^-  @s
      =/  d  (dims m)
      ?>  =(r.d c.d)
      (bareiss:pv m r.d)
    ::    +rank:  the rank
    ::
    ::  [m=zmat] -> @ud.  The rank of an integer matrix is its rank over
    ::  Q -- equivalently the size of its largest nonvanishing minor, and
    ::  the two agree -- so this is the definition, computed where the
    ::  definition lives.  Never crashes.
    ::
    ::  That agreement is exactly what composite Z/n lacks, which is why
    ::  +rank:mm asserts primality and this arm does not.
    ++  rank
      |=  m=zmat
      ^-  @ud
      (rank:qm (to-q m))
    ::    +charpoly:  the characteristic polynomial
    ::
    ::  [m=zmat] -> zol, monic of degree n.  det(xI - A), NOT det(A - xI):
    ::  the two differ by (-1)^n and agree only in even dimension.
    ::  Crashes on a non-square input (SPEC S8).
    ::
    ::  Computed over Q and brought back.  An integer matrix has a MONIC
    ::  INTEGER characteristic polynomial -- the coefficients are the
    ::  signed sums of principal minors -- so every denominator here must
    ::  be 1, and the ?> asserting it is a real check on the arm rather
    ::  than a restatement of an assumption.
    ++  charpoly
      ~/  %charpoly
      |=  m=zmat
      ^-  zol
      %+  turn  (charpoly:qm (to-q m))
      |=  f=frac
      ^-  @s
      ?>  =(1 q.f)
      p.f
    --
  ::    +mm:  matrices over Z/n, a door on the modulus.  Milestone C.
  ::
  ::  Three sub-cores, not four: F_p is Z/n with n prime, so it shares
  ::  $mmat and this door, exactly as Racoon serves both from +mx.
  ++  mm
    ~/  %mm
    |_  n=@ud
    ::    +md:  Racoon's Z/n core at this modulus
    ::
    ::  Scalar arithmetic goes through +mx throughout, so an entry is
    ::  canonical for the same reason a $mol coefficient is.
    ++  md  ~(. mx n)
    ::    +canon:  impose the canonical form on the entries
    ::
    ::  [m=mmat] -> mmat.  Reduces every entry into [0, n).  The only arm
    ::  that accepts non-canonical input.  Unlike +zm, this core has real
    ::  work for +canon: [0, n) is a genuine normal form, where @s is not.
    ::
    ::  Does NOT repair raggedness, exactly as +canon:qm does not.
    ++  canon
      |=  m=mmat
      ^-  mmat
      %+  turn  m
      |=(r=mvec ^-(mvec (turn r |=(x=@ud (mod x n)))))
    ::    +dims:  the dimensions of a matrix
    ::
    ::  Derived rather than stored.  Crashes on the empty matrix.
    ++  dims
      |=  m=mmat
      ^-  [r=@ud c=@ud]
      ?~  m  !!
      [(lent m) (lent i.m)]
    ::    +is-square:  does the matrix have as many rows as columns?
    ++  is-square
      |=  m=mmat
      ^-  ?
      =/  d  (dims m)
      =(r.d c.d)
    ::    +get:  the entry at row i, column j
    ::
    ::  Zero-based.  Crashes when either index is out of range (SPEC S8).
    ++  get
      |=  [m=mmat i=@ud j=@ud]
      ^-  @ud
      =/  d  (dims m)
      ?>  ?&((lth i r.d) (lth j c.d))
      (nat:pv (nrow:pv m i) j)
    ::    +put:  replace the entry at row i, column j
    ++  put
      |=  [m=mmat i=@ud j=@ud x=@ud]
      ^-  mmat
      =/  d  (dims m)
      ?>  ?&((lth i r.d) (lth j c.d))
      (nput:pv m i (nvput:pv (nrow:pv m i) j x))
    ::    +row:  extract row i
    ++  row
      |=  [m=mmat i=@ud]
      ^-  mvec
      =/  d  (dims m)
      ?>  (lth i r.d)
      (nrow:pv m i)
    ::    +col:  extract column j
    ++  col
      |=  [m=mmat j=@ud]
      ^-  mvec
      =/  d  (dims m)
      ?>  (lth j c.d)
      (turn m |=(r=mvec (nat:pv r j)))
    ::    +transpose:  exchange rows and columns
    ++  transpose
      |=  m=mmat
      ^-  mmat
      =/  d  (dims m)
      %+  turn  (gulf 0 (dec c.d))
      |=(j=@ud ^-(mvec (turn m |=(r=mvec (nat:pv r j)))))
    ::    +idn:  the n x n identity matrix
    ::
    ::  Crashes on a dimension of 0 (SPEC S8).  The face is +k to keep the
    ::  door's modulus +n visible; every other core calls this argument n.
    ++  idn
      |=  k=@ud
      ^-  mmat
      ?>  (gth k 0)
      %+  turn  (gulf 0 (dec k))
      |=  i=@ud
      ^-  mvec
      %+  turn  (gulf 0 (dec k))
      |=(j=@ud ?:(=(i j) 1 0))
    ::    +zeros:  the r x c zero matrix
    ++  zeros
      |=  [r=@ud c=@ud]
      ^-  mmat
      ?>  ?&((gth r 0) (gth c 0))
      %+  turn  (gulf 0 (dec r))
      |=  *
      ^-  mvec
      (reap c 0)
    ::    +add:  matrix addition
    ::
    ::  Elementwise.  Crashes on a dimension mismatch (SPEC S8).
    ++  add
      |=  [a=mmat b=mmat]
      ^-  mmat
      ?>  =((dims a) (dims b))
      |-  ^-  mmat
      ?~  a  ~
      ?~  b  ~
      [(nvadd:pv n i.a i.b) $(a t.a, b t.b)]
    ::    +neg:  matrix negation
    ++  neg
      |=  m=mmat
      ^-  mmat
      %+  turn  m
      |=(r=mvec ^-(mvec (turn r |=(x=@ud (cneg:md x)))))
    ::    +sub:  matrix subtraction
    ++  sub
      |=  [a=mmat b=mmat]
      ^-  mmat
      ?>  =((dims a) (dims b))
      |-  ^-  mmat
      ?~  a  ~
      ?~  b  ~
      [(nvsub:pv n i.a i.b) $(a t.a, b t.b)]
    ::    +scale:  multiply every entry by a scalar
    ++  scale
      |=  [m=mmat x=@ud]
      ^-  mmat
      %+  turn  m
      |=(r=mvec ^-(mvec (turn r |=(y=@ud (cmul:md x y)))))
    ::    +mul:  matrix multiplication
    ::
    ::  Crashes unless cols(a) = rows(b) (SPEC S8).  Transposing b up
    ::  front makes every entry an inner product of two rows, as in +qm.
    ++  mul
      ~/  %mul
      |=  [a=mmat b=mmat]
      ^-  mmat
      ?>  =(c:(dims a) r:(dims b))
      =/  bt=mmat  (transpose b)
      %+  turn  a
      |=  r=mvec
      ^-  mvec
      (turn bt |=(s=mvec (ndot:pv n r s)))
    ::    +pow:  matrix power
    ::
    ::  Binary square-and-multiply.  m^0 is the identity of matching size.
    ::  Crashes on a non-square input (SPEC S8).
    ++  pow
      |=  [m=mmat e=@ud]
      ^-  mmat
      =/  d  (dims m)
      ?>  =(r.d c.d)
      ?:  =(0 e)  (idn r.d)
      =/  k=@ud     (dec (met 0 e))
      =/  acc=mmat  m
      |-  ^-  mmat
      ?:  =(0 k)  acc
      =/  nk=@ud    (dec k)
      =/  sq=mmat   (mul acc acc)
      %=  $
        k    nk
        acc  ?:(=(1 (cut 0 [nk 1] e)) (mul sq m) sq)
      ==
    ::    +of-z:  reduce an integer matrix mod n
    ++  of-z
      |=  m=zmat
      ^-  mmat
      %+  turn  m
      |=(r=zvec ^-(mvec (turn r |=(x=@s (zmodn:pv x n)))))
    ::    +to-z:  lift to the symmetric representatives
    ::
    ::  [m=mmat] -> zmat with entries in (-n/2, n/2].  Not a right
    ::  inverse of +of-z at the level of matrices -- to-z(of-z(m)) is m
    ::  only when m already lay in that window -- which is what
    ::  "representative" means and is why the arm says so here rather
    ::  than leaving a caller to discover it.
    ::
    ::  Symmetric rather than [0, n) because the lift feeds integer
    ::  determinants: halving the magnitude of every entry keeps the
    ::  Bareiss intermediates smaller, and any representatives at all
    ::  would be correct.
    ++  to-z
      |=  m=mmat
      ^-  zmat
      %+  turn  m
      |=  r=mvec
      ^-  zvec
      %+  turn  r
      |=  x=@ud
      ^-  @s
      ::  ^mul: the bare name is this door's own matrix multiplication
      ?:  (gth (^mul 2 x) n)  (dif:si (sun:si x) (sun:si n))
      (sun:si x)
    ::    +rref:  reduced row echelon form, with pivot columns
    ::
    ::  [m=mmat] -> mrref.  Gauss-Jordan.
    ::
    ::  Pivot selection is the first entry at or below the current row
    ::  that is a UNIT mod n -- not merely the first nonzero, because a
    ::  nonzero non-unit cannot be scaled to 1.  If a column has nonzero
    ::  entries at or below the current row but no unit among them, this
    ::  crashes (SPEC C3).  Over F_p every nonzero element is a unit, so
    ::  the search always succeeds at the first nonzero and the crash is
    ::  unreachable.
    ::
    ::  THAT CRASH IS REACHABLE ON AN INVERTIBLE MATRIX.  Over Z/6 the
    ::  matrix [[2 1] [3 1]] has determinant -1 = 5, a unit, yet neither
    ::  entry of its first column is a unit mod 6.  Gauss-Jordan with
    ::  unit pivots is therefore strictly weaker than invertibility over
    ::  a composite modulus, which is exactly why +inv below does not go
    ::  through this arm.
    ++  rref
      ~/  %rref
      |=  m=mmat
      ^-  mrref
      =/  d  (dims m)
      =/  cur=mmat  m
      =/  r=@ud     0
      =/  j=@ud     0
      =|  piv=(list @ud)
      |-  ^-  mrref
      ?:  ?|(=(r r.d) =(j c.d))  [cur (flop piv)]
      ::  the first unit at or below row r in column j
      =/  hit=(unit @ud)
        =/  i=@ud  r
        |-  ^-  (unit @ud)
        ?:  (gte i r.d)  ~
        ?:  =(1 (gcd:nz (nat:pv (nrow:pv cur i) j) n))  `i
        $(i +(i))
      ?~  hit
        ::  no unit here: a nonzero non-unit below is unusable, and
        ::  proceeding would silently drop a row from the echelon form
        =/  live=?
          =/  i=@ud  r
          |-  ^-  ?
          ?:  (gte i r.d)  %.n
          ?.  =(0 (nat:pv (nrow:pv cur i) j))  %.y
          $(i +(i))
        ?>  !live
        $(j +(j))
      =/  sw=mmat
        ?:  =(u.hit r)  cur
        (nput:pv (nput:pv cur r (nrow:pv cur u.hit)) u.hit (nrow:pv cur r))
      =/  pin=@ud   (cinv:md (nat:pv (nrow:pv sw r) j))
      =/  nr=mvec   (turn (nrow:pv sw r) |=(x=@ud (cmul:md pin x)))
      =/  base=mmat  (nput:pv sw r nr)
      =/  elim=mmat
        =/  i=@ud     0
        =/  acc=mmat  base
        |-  ^-  mmat
        ?:  (gte i r.d)  acc
        ?:  =(i r)  $(i +(i))
        =/  f=@ud  (nat:pv (nrow:pv acc i) j)
        ?:  =(0 f)  $(i +(i))
        =/  rw=mvec
          %+  turn  (gulf 0 (dec c.d))
          |=  k=@ud
          ^-  @ud
          %+  csub:md  (nat:pv (nrow:pv acc i) k)
          (cmul:md f (nat:pv nr k))
        $(i +(i), acc (nput:pv acc i rw))
      $(cur elim, r +(r), j +(j), piv [j piv])
    ::    +rank:  the rank
    ::
    ::  [m=mmat] -> @ud.  REQUIRES n PRIME, asserted.
    ::
    ::  Over a field the rank is the number of pivots and every
    ::  definition of rank agrees.  Over composite Z/n they diverge --
    ::  the module is not free and the largest nonvanishing minor need
    ::  not match the pivot count -- so there is no single number to
    ::  return and returning one anyway would be silently wrong.
    ++  rank
      |=  m=mmat
      ^-  @ud
      ?>  (is-prime:nz n)
      (lent piv:(rref m))
    ::    +det:  the determinant
    ::
    ::  [m=mmat] -> @ud in [0, n).  Crashes on a non-square input.
    ::
    ::  LIFTED TO Z, computed there, and reduced back.  The determinant
    ::  is a polynomial with integer coefficients in the entries, so the
    ::  answer is independent of which representatives are lifted and the
    ::  reduction is exact -- for every n, prime or not.
    ::
    ::  This sidesteps Bareiss's exact divisions, which are unavailable
    ::  in Z/n because a divisor need not be a unit, rather than trying
    ::  to work around them in the ring.
    ++  det
      ~/  %det
      |=  m=mmat
      ^-  @ud
      =/  d  (dims m)
      ?>  =(r.d c.d)
      (zmodn:pv (bareiss:pv (to-z m) r.d) n)
    ::    +inv:  the matrix inverse
    ::
    ::  [m=mmat] -> mmat.  Crashes on a non-square input, and on a matrix
    ::  whose determinant is not a unit mod n -- which is the right
    ::  singularity test here: over Z/n a nonzero determinant is not
    ::  enough, it must be invertible.
    ::
    ::  By the ADJUGATE, not by elimination: A * adj(A) = det(A) * I holds
    ::  in every commutative ring, so A^-1 = det(A)^-1 * adj(A) whenever
    ::  det(A) is a unit.  This needs no pivoting and therefore inverts
    ::  matrices +rref cannot reduce -- see the Z/6 example there.
    ::
    ::  The cost is O(n^5): n^2 cofactors, each an (n-1)-square Bareiss
    ::  determinant.  Correctness over a composite modulus is worth more
    ::  than the exponent at the sizes this library targets, and a
    ::  Milestone B jet is free to do better since the product is
    ::  canonical.
    ++  inv
      ~/  %inv
      |=  m=mmat
      ^-  mmat
      =/  d  (dims m)
      ?>  =(r.d c.d)
      ::  +cinv:md crashes unless the determinant is a unit
      =/  di=@ud   (cinv:md (det m))
      =/  aj=zmat  (zadj:pv (to-z m) r.d)
      %+  turn  aj
      |=  r=zvec
      ^-  mvec
      (turn r |=(x=@s (cmul:md di (zmodn:pv x n))))
    ::    +solve:  solve a x = b
    ::
    ::  [a=mmat b=mmat] -> (unit mmat).  Crashes unless a is square and
    ::  rows(b) = rows(a).  Produces ~ exactly when det(a) is not a unit
    ::  mod n, and the unique solution otherwise (SPEC C3).
    ++  solve
      |=  [a=mmat b=mmat]
      ^-  (unit mmat)
      =/  da  (dims a)
      =/  db  (dims b)
      ?>  ?&(=(r.da c.da) =(r.db r.da))
      ?.  =(1 (gcd:nz (det a) n))  ~
      `(mul (inv a) b)
    ::    +nullspace:  a basis for the kernel
    ::
    ::  [m=mmat] -> (list mvec).  REQUIRES n PRIME, asserted, for the
    ::  same reason +rank does: over composite Z/n the kernel is not a
    ::  free module and a unit-pivot echelon form does not generate it.
    ::
    ::  Basis convention as SPEC S7, unchanged from +qm: one vector per
    ::  free column j, with 1 at j, 0 at every other free column, and the
    ::  negated RREF entry at each pivot position.  Empty exactly when
    ::  the matrix has full column rank.
    ++  nullspace
      |=  m=mmat
      ^-  (list mvec)
      ?>  (is-prime:nz n)
      =/  d   (dims m)
      =/  rr  (rref m)
      =/  free=(list @ud)
        %+  skip  (gulf 0 (dec c.d))
        |=(j=@ud (lien piv.rr |=(k=@ud =(k j))))
      %+  turn  free
      |=  j=@ud
      ^-  mvec
      %+  turn  (gulf 0 (dec c.d))
      |=  k=@ud
      ^-  @ud
      ?:  =(k j)  1
      =/  at=(unit @ud)
        =/  ps=(list @ud)  piv.rr
        =/  i=@ud          0
        |-  ^-  (unit @ud)
        ?~  ps  ~
        ?:  =(i.ps k)  `i
        $(ps t.ps, i +(i))
      ?~  at  0
      (cneg:md (nat:pv (nrow:pv m.rr u.at) j))
    ::    +charpoly:  the characteristic polynomial
    ::
    ::  [m=mmat] -> mol, monic of degree n.  det(xI - A), NOT det(A - xI).
    ::  Crashes on a non-square input (SPEC S8).
    ::
    ::  Lifted to Z and reduced back, by the same argument as +det: the
    ::  coefficients are integer polynomials in the entries.  No trailing
    ::  zero can appear, since the leading coefficient is 1 and the
    ::  modulus is at least 2, so the $mol form needs no stripping.
    ++  charpoly
      ~/  %charpoly
      |=  m=mmat
      ^-  mol
      =/  d  (dims m)
      ?>  =(r.d c.d)
      (turn (charpoly:zm (to-z m)) |=(x=@s (zmodn:pv x n)))
    --
  --
--
