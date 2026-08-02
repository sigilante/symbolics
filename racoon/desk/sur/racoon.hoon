  ::  /sur/racoon
::::  Types for Racoon, Real AlgebraiCs in hOON
::
::  Every type declared here is a canonical form.  Public arms in /lib/racoon
::  require canonical inputs and produce canonical outputs; arms do not
::  defensively re-canonicalize their arguments.  The sole exception per ring
::  is +canon, which exists precisely to impose the canonical form.
::
::  Signed integers are Hoon's ZigZag-coded @s; all signed scalar arithmetic
::  goes through ++si.  Unsigned integers are @ud.
::
|%
::
::    $ord:  result of a total-order comparison
::
::  Product of every comparison in the library: +cmp:qq on $frac, and +pcmp
::  on each polynomial ring.  Distinct from ++cmp:si, which produces an @s in
::  {-1, --0, --1}.
+$  ord  ?(%lt %gt %eq)
::
::    $frac:  rational number, an element of Q
::
::  Invariants: q > 0, and gcd(|p|, q) = 1.  Hence every rational has exactly
::  one representation.  Zero is [--0 1]; one is [--1 1].
+$  frac  [p=@s q=@ud]
::
::  Univariate polynomials are dense and little-endian: index i holds the
::  coefficient of x**i.  Canonical form carries no trailing zero coefficient,
::  so the zero polynomial is ~ and the degree of a nonzero p is
::  (dec (lent p)).  Degree is undefined (crash) on ~.
::
::  This makes the canonical-form check O(1) -- nonempty, and last coefficient
::  nonzero -- which is the check native jets use to decide native-vs-fallback.
::
::    $zol:  polynomial in Z[x]
::
::  Trailing coefficient, if any, is not --0.
+$  zol  (list @s)
::
::    $mol:  polynomial in (Z/n)[x]
::
::  Coefficients lie in [0, n); the modulus n is carried by the +mx door, not
::  by the polynomial itself.  Trailing coefficient, if any, is not 0.
+$  mol  (list @ud)
::    $qol:  polynomial in Q[x]
::
::  Trailing coefficient, if any, is not the zero $frac.
::
+$  qol  (list frac)
::
::    $zfac:  factorization over Z
::
::  Represents input = c * prod(p_i ^ m_i).  Each p_i is primitive with
::  positive leading coefficient and irreducible in Z[x]; |c| is the content
::  of the input and sign(c) is the sign of the input's leading coefficient.
::  .fs is sorted ascending by +pcmp:zx, each m_i is >= 1, and the p_i are
::  pairwise distinct.
::
::  Factoring the zero polynomial is undefined (crash).  A degree-0 input
::  factors as [c ~].
+$  zfac  [c=@s fs=(list [p=zol m=@ud])]
::
::    $mfac:  factorization over F_p, n prime
::
::  Represents input = c * prod(p_i ^ m_i).  c is the leading coefficient of
::  the input and each p_i is monic irreducible.  .fs is sorted ascending by
::  +pcmp:mx, each m_i is >= 1, and the p_i are pairwise distinct.
::
::  Factoring the zero polynomial is undefined (crash).  A degree-0 input
::  factors as [c ~].
+$  mfac  [c=@ud fs=(list [p=mol m=@ud])]
--
