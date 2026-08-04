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
/+  *test, baloon, racoon, vec=baloon-vectors, fmt=baloon-fmt
/+  vh=vanhoeij
=/  qq  qq:racoon
=/  qx  qx:racoon
=/  qm  qm:baloon
=/  nz  nz:racoon
=/  mx  mx:racoon
=/  zm  zm:baloon
=/  mm  mm:baloon
|%
++  unimodular
  |=  m=zmat
  ^-  ?
  =/  x=@s  (det:zm m)
  ?|(=(--1 x) =(-1 x))
::    +lead:  the index of the first nonzero entry of a row, if any
++  lead
  |=  v=zvec
  ^-  (unit @ud)
  =/  j=@ud  0
  |-  ^-  (unit @ud)
  ?~  v  ~
  ?.  =(--0 i.v)  `j
  $(v t.v, j +(j))
::    +hnf-ok:  does h satisfy the SPEC C2 Hermite conditions?
::
::  Nonzero rows first, leading columns strictly increasing, every pivot
::  strictly positive, and every entry above a pivot in [0, pivot).
++  hnf-ok
  |=  h=zmat
  ^-  ?
  =/  d   (dims:zm h)
  =/  i=@ud     0
  =/  prev=(unit @ud)  ~
  =/  dead=?    %.n
  |-  ^-  ?
  ?:  =(i r.d)  %.y
  =/  lj  (lead (row:zm h i))
  ?~  lj
    ::  once a zero row appears, every later row must be zero too
    $(i +(i), dead %.y)
  ?:  dead  %.n
  =/  p=@s  (get:zm h i u.lj)
  ?.  (syn:si p)  %.n
  ?:  =(--0 p)  %.n
  ::  strictly advancing pivots
  ?.  ?~(prev %.y (gth u.lj u.prev))  %.n
  ::  every entry above this pivot reduced into [0, pivot)
  =/  above=?
    =/  k=@ud  0
    |-  ^-  ?
    ?:  (gte k i)  %.y
    =/  x=@s  (get:zm h k u.lj)
    ?.  ?&((syn:si x) (gth p x))  %.n
    $(k +(k))
  ?.  above  %.n
  ::  $ and not ^$: the inner |- closed inside its own =/, so the nearest
  ::  loop in scope here is already the outer one
  $(i +(i), prev `u.lj)
::    +snf-ok:  is d diagonal, non-negative, with d_i dividing d_(i+1)?
++  snf-ok
  |=  m=zmat
  ^-  ?
  =/  dd  (dims:zm m)
  =/  lim=@ud  (min r.dd c.dd)
  =/  i=@ud  0
  |-  ^-  ?
  ?:  =(i r.dd)  %.y
  =/  ok=?
    =/  j=@ud  0
    |-  ^-  ?
    ?:  =(j c.dd)  %.y
    =/  x=@s  (get:zm m i j)
    ?:  =(i j)
      ::  on the diagonal: non-negative, and divides its successor
      ?.  (syn:si x)  %.n
      ?:  (gte +(i) lim)  $(j +(j))
      =/  y=@s  (get:zm m +(i) +(i))
      ?.  ?:(=(--0 x) =(--0 y) =(0 (mod (abs:si y) (abs:si x))))  %.n
      $(j +(j))
    ::  off the diagonal: zero
    ?.  =(--0 x)  %.n
    $(j +(j))
  ?.  ok  %.n
  $(i +(i))
::
++  nsq
  |=  v=zvec
  ^-  @ud
  =/  acc=@ud  0
  |-  ^-  @ud
  ?~  v  acc
  $(v t.v, acc (add acc (abs:si (pro:si i.v i.v))))
::  Integer lattice bases for the LLL tests.  Full row rank, which
::  +lll asserts; the shapes are mixed square and rectangular since
::  a lattice need not fill its ambient space.
++  lllvecs
  ^-  (list zmat)
  :~
    ~[~[--1 --0 --0 -20] ~[--0 --1 --0 -2] ~[--0 --0 --1 -36]]
    ~[~[--1 --1 --1] ~[-1 --0 --2] ~[--3 --5 --6]]
    ~[~[--15 --23 --11] ~[--46 --15 --3] ~[--32 --1 --1]]
    ~[~[--201 --37] ~[--1.648 --297]]
    ~[~[--1 --0] ~[--0 --1]]
    ~[~[--1 --0 --0] ~[--0 --1 --0] ~[--0 --0 --1]]
    ~[~[--2 --0] ~[--0 --3]]
    :~  ~[--105 --821 --4.551 --42.104]
        ~[--0 --1 --0 --0]
        ~[--0 --0 --1 --0]
        ~[--0 --0 --0 --1]
    ==
    ~[~[--8 -3] ~[--6 -1]]
    ~[~[-9 -6] ~[--4 -8]]
    ~[~[--9 -6 -3] ~[-2 -8 -2] ~[--1 --7 -2]]
    ~[~[-9 --1] ~[-4 --3]]
    ~[~[-9 -6 -3] ~[--2 --1 -5] ~[-4 --9 -3]]
    ~[~[-9 --2] ~[-7 --8]]
  ==
::
::  Lattice reduction (/lib/vanhoeij), SPEC Milestone C phase V0.
::
::  A CONSUMER OF BOTH LIBRARIES -- it uses Racoon's rationals for the
::  Gram-Schmidt and Baloon's integer matrices for the lattice, which is
::  why it sits here rather than in Racoon (escalation R4).
::
::  VERIFIED STRUCTURALLY, NOT AGAINST ANOTHER PROGRAM.  SymPy has
::  DomainMatrix.lll, but an LLL-reduced basis is NOT unique -- two
::  correct implementations at the same delta can return different bases
::  -- so matching its output is neither necessary nor sufficient.  §11.3
::  says confirm a convention before pinning it against a tool; here the
::  conclusion is that the tool is the wrong oracle.  The definition is
::  checked instead, and it is complete: size-reduced, Lovasz, and the
::  same lattice.  Any basis satisfying all three IS an LLL-reduced basis
::  of that lattice.
::
++  test-v0-lll-values
  ::  annotated: an un-typed ~[...] infers as a fixed tuple, which the
  ::  wet +snag below cannot nest
  =/  b=zmat  ~[~[--1 --0 --0 -20] ~[--0 --1 --0 -2] ~[--0 --0 --1 -36]]
  ;:  weld
    ::  the classic worked example.  SymPy's DomainMatrix.lll happens to
    ::  agree here, which is a coincidence worth noting and not a
    ::  guarantee -- see the chapter header
    %+  expect-eq
      !>(`zmat`~[~[--0 --1 --0 -2] ~[-2 --2 --1 --0] ~[-3 -5 --2 -2]])
    !>((lll:vh b))
    ::  the input was not reduced; the output is
    %-  expect  !>(!(reduced:vh b))
    %-  expect  !>((reduced:vh (lll:vh b)))
    ::  an identity basis is already reduced, so nothing moves
    %+  expect-eq  !>((idn:zm 3))  !>((lll:vh (idn:zm 3)))
    %-  expect  !>((reduced:vh (idn:zm 3)))
    ::  a single row is reduced vacuously
    %+  expect-eq  !>(`zmat`~[~[--3 --4]])  !>((lll:vh ~[~[--3 --4]]))
    %-  expect  !>((reduced:vh ~[~[--3 --4]]))
  ==
++  test-v0-lll-properties
  =/  vs  lllvecs
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  b=zmat  i.vs
  =/  r=zmat  (lll:vh b)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      ;:  weld
        ::  the whole specification of +lll, in three checks
        %-  expect  !>((reduced:vh r))
        ::  SAME LATTICE, which needs no oracle at all: two bases generate
        ::  the same lattice exactly when their Hermite forms agree.  This
        ::  is the check Baloon's Milestone C made possible.
        %+  expect-eq  !>(h:(hnf:zm b))  !>(h:(hnf:zm r))
        ::  and the shape is unchanged
        %+  expect-eq  !>((dims:zm b))  !>((dims:zm r))
      ==
  ==
++  test-v0-lll-unimodular
  ::  for a square basis the transform is unimodular, so |det| survives
  =/  vs=(list zmat)  (skim lllvecs |=(b=zmat =(r:(dims:zm b) c:(dims:zm b))))
  =|  out=tang
  |-  ^-  tang
  ?~  vs  out
  =/  b=zmat  i.vs
  =/  r=zmat  (lll:vh b)
  %=  $
    vs  t.vs
    out
      %+  weld  out
      %+  expect-eq
        !>((abs:si (det:zm b)))
      !>((abs:si (det:zm r)))
  ==
++  test-v0-lll-shortens
  ::  reduction does what it is for: the first basis vector comes out no
  ::  longer than it went in, and usually much shorter
  ::  annotated: an un-typed ~[...] infers as a fixed tuple, which the
  ::  wet +snag below cannot nest
  =/  b=zmat  ~[~[--1 --0 --0 -20] ~[--0 --1 --0 -2] ~[--0 --0 --1 -36]]
  =/  r=zmat  (lll:vh b)
  ;:  weld
    ::  ||b_0||^2 was 401; the reduced leader is 5
    %+  expect-eq  !>(`@ud`401)  !>((nsq (snag 0 b)))
    %+  expect-eq  !>(`@ud`5)    !>((nsq (snag 0 r)))
    %-  expect  !>((lte (nsq (snag 0 r)) (nsq (snag 0 b))))
  ==
++  test-v0-lll-crash
  ;:  weld
    ::  the empty basis has no lattice
    (expect-fail |.((lll:vh ~)))
    ::  linearly dependent rows: the Gram-Schmidt would divide by zero, so
    ::  +lll asserts full rank first and says which precondition failed
    (expect-fail |.((lll:vh ~[~[--1 --2] ~[--2 --4]])))
    (expect-fail |.((lll:vh ~[~[--1 --2 --3] ~[--2 --4 --6]])))
    ::  three rows in a plane
    (expect-fail |.((lll:vh ~[~[--1 --0] ~[--0 --1] ~[--1 --1]])))
    (expect-success |.((lll:vh ~[~[--1 --2] ~[--3 --4]])))
    ::  +reduced is total: it answers for any basis, reduced or not
    (expect-success |.((reduced:vh ~[~[--1 --2] ~[--2 --4]])))
    %-  expect  !>((reduced:vh ~))
  ==
--
