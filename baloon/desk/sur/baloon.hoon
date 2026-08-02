  ::  /sur/baloon
::::  Types for Baloon, Basic linear ALgebra in hOON
::
::  Matrices are dense, row-major, nested lists.  Canonical form in every
::  ring: nonempty, rectangular (every row the same nonempty length), and
::  every entry canonical for its ring.  Dimensions are DERIVED, not stored:
::  rows = (lent m), cols = (lent -.m).
::
::  Carrying [r c data] would add two further invariants that can desync
::  from the data; deriving adds one, rectangularity.  Fewer redundant
::  invariants is the same reasoning behind Racoon's no-trailing-zero
::  polynomial form.
::
::  Names are ring-prefixed throughout, as Racoon's $zol / $mol / $qol are.
::  Nothing here is unprefixed: an unprefixed name in a multi-ring library
::  is a trap that only springs once the second ring arrives.
::
::  Milestone A implements Q only.  $zmat and $mmat are declared so that
::  naming and representation are settled once, while the reasoning is
::  fresh, rather than chosen inconsistently later.  No arm consumes them
::  until Milestone C.  Types carry no battery-axis consequence -- they are
::  not jetted -- so declaring them early costs nothing.
::
/-  *racoon
|%
::    $qmat:  a matrix over Q
::
::  Entries are canonical $frac.
::
+$  qmat  (list (list frac))
::    $qvec:  a vector over Q
::
::  A bare list, used where a product is not itself a matrix: a nullspace
::  basis element, a single extracted row or column.
::
+$  qvec  (list frac)
::    $zmat:  a matrix over Z.  Milestone C.
+$  zmat  (list (list @s))
::    $zvec:  a vector over Z.  Milestone C.
+$  zvec  (list @s)
::    $mmat:  a matrix over Z/n.  Milestone C.
::
::  Entries lie in [0, n).  The modulus is carried by the +mm door, not by
::  the matrix, exactly as Racoon's $mol leaves n to +mx.
::
+$  mmat  (list (list @ud))
::    $mvec:  a vector over Z/n.  Milestone C.
+$  mvec  (list @ud)
::    $qrref:  reduced row echelon form over Q, with its pivot columns
::
::  .piv is ascending, and (lent piv) is the rank.
::
::  Ring-prefixed because RREF is NOT a ring-generic notion.  Over Z there
::  is no RREF at all -- a pivot cannot be scaled to 1 without leaving Z --
::  and the row-canonical form is instead the Hermite normal form.  Over
::  Z/n an RREF exists exactly when the pivots actually needed are units.
::
+$  qrref  [m=qmat piv=(list @ud)]
::
::  RESERVED, deliberately not declared: the Hermite and Smith normal form
::  products for +zm.  Whether they carry their unimodular transform
::  ([h=zmat u=zmat] against a bare h) depends on design work not yet done,
::  and guessing would pin a convention SPEC S14 would rather see raised.
--
