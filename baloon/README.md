# Baloon — Basic Linear ALgebra in hOON

Exact linear algebra over ℚ for Urbit, built entirely on [Racoon](../racoon).
No floating point anywhere: Lagoon owns the approximate case, Baloon the
exact one, and the two are siblings rather than layers.

`../baloon-spec.md` is normative. `/lib/baloon` depends on `/lib/racoon` and
nothing else, the same relationship `/lib/lagoon` has to `/lib/math`.

Note on spelling: **Baloon**, one `l`, in every path and in prose — matching
Racoon's single `c`.

## Status

| Phase | Contents | State |
|---|---|---|
| **P0** | shape and construction | **complete** |
| **P1** | arithmetic | **complete** |
| **P2** | elimination — rref, rank, det, inv, solve, nullspace | **complete** |
| **P3** | spectral — charpoly, eigen | **complete** |

Milestone A is **ℚ only**. `+zm` (ℤ) and `+mm` (ℤ/n, which also serves 𝔽p)
were declared empty and reserved for Milestone C — declaring them up front
keeps the `%baloon` battery from moving later, which is Racoon's Q5 applied
in advance rather than retrofitted. **Milestone C is now built**; see below.

## Every arm is `free`

Racoon needed five pinned algorithms because their outputs were
underdetermined — `egcd`'s cofactors, the Miller–Rabin witness schedule, the
Mignotte bound. Every Baloon product is instead a unique mathematical object:
the determinant, the RREF, the rank, the inverse, the characteristic
polynomial. So Milestone B jets have complete algorithmic freedom.

The one place uniqueness needs help is the nullspace, whose *basis* is not
unique. §7 pins a basis convention rather than an algorithm, which keeps the
output canonical without constraining how a jet computes it.

## Edit–test loop

`/lib/baloon` imports `/lib/racoon`, so sync Racoon first if `%base` is fresh.

```
../racoon/scripts/sync.sh             # host, once
scripts/sync.sh                       # host
|commit %base                         # dojo
-test /=base=/tests/lib/baloon ~      # dojo
```

Override the pier with `BALOON_PIER=/path/to/zod`.

## Reference vectors

```
python3 tools/genvec.py > desk/lib/baloon-vectors.hoon
```

Deterministic from a pinned seed. The generator's `+selfcheck` asserts every
SymPy convention it relies on against that convention's definition, and runs
on every generation — so a SymPy upgrade that changes a convention breaks
generation loudly rather than corrupting the corpus quietly. That check
exists because Racoon lost time to `sympy.resultant` silently normalizing
its argument order.

## Testing

```
-test /=base=/tests/lib/baloon ~
```

100 arms, all green. Behavioral, property, crash-row, and vector-driven.
§8 is treated as a two-sided contract: every crash row has a dedicated test
and every non-crash boundary has a matching expected-success test.

Property-test inputs are built by local helpers rather than by the library
arm they would otherwise be exercising — the same discipline Racoon's suite
uses.

## Human surface

`/lib/baloon-fmt` renders matrices as aligned grids and parses them back, so
nothing has to be read as a nested list of ZigZag rationals. A consumer of
the library, exactly as `racoon-fmt` is to Racoon.

```
+baloon-det '[[1 2] [3 4]]'
[ 1 2 ]
[ 3 4 ]
dims  2 x 2
rank  2
det   -2
no rational eigenvalues
```

Entries are right-aligned to a common width — alignment is most of what
makes a printed matrix legible. The parser accepts `[[1 2] [3 4]]` and
`[[1, 2], [3, 4]]` alike, with any whitespace, and **rejects ragged input**:
raggedness is outside the canonical form, and a parser is the right boundary
to catch it rather than admit it.

`parse . print` is asserted as an identity over the whole generated corpus.

## Benchmarks

```
+baloon-bench
```

No performance gates in Milestone A; these are the denominator for
Milestone B speedup claims. Vere 4.6, `%zuse` 409, fake `~zod`, `--loom 33`,
Darwin arm64. One measurement each.

| Arm | n = 4 | n = 8 | n = 16 |
|---|---:|---:|---:|
| `mul:qm` | 1.348 ms | 9.748 ms | 79.071 ms |
| `det:qm` | 373 µs | 3.289 ms | 34.040 ms |
| `rref:qm` | 1.479 ms | 13.633 ms | 150.946 ms |
| `inv:qm` | 2.817 ms | 29.903 ms | 364.358 ms |
| `charpoly:qm` | — | 63.032 ms | — |

`mul` runs almost exactly 8× per doubling — cubic, which is what the triply
nested product should cost, and a sign the baseline measures what it claims
to. `det` tracks it closely; Bareiss is cubic in arithmetic operations, and
the slight excess over 8× is the integer entries growing as elimination
proceeds. `rref` and `inv` grow faster than cubic because their entries are
rationals whose numerators and denominators both grow — which is exactly the
swell B4 warns about, and exactly why `det` avoids it by working over ℤ.

That contrast is the most useful number here: **`det` at n = 16 costs 34 ms
against `inv`'s 364 ms**, an order of magnitude, for work of the same
asymptotic shape. Fraction-free elimination earns its keep.

## Milestone C — ℤ and ℤ/n

`+zm` and `+mm` are no longer empty. **Milestone B (jets) is still
deferred**; C proceeded ahead of it because it needs nothing from it.

| Core | Contents | State |
|---|---|---|
| **`+zm`** | shape, arithmetic, `to-q`/`of-q`, `det`, `rank`, `charpoly` | **complete** |
| **`+mm`** | the whole `+qm` arm set over ℤ/n, plus `of-z`/`to-z` | **complete** |
| **`+zm` normal forms** | `hnf`, `snf`, each with its transform | **complete** |

**The reserved-core discipline paid off exactly as intended.** Adding arms
*inside* `+zm` and `+mm` leaves `%baloon`'s own battery at three arms, so
nothing frozen at Milestone A moved. Milestone C added no arm to `+qm` and
no matrix type.

**`+qm` stayed shut.** `minpoly` and rational eigenvectors are Milestone C
candidates, but adding either to `+qm` would move axes frozen at P3. They
are computable from `qm`'s public arms alone, so they belong in a consumer
library — the pattern `/lib/racoon-rs` and `/lib/racoon-fp3` established
twice. A frozen interface reopened for every good idea was never frozen.

### What ℤ does not have

`+canon`, `+rref`, `+inv`, `+solve`, and `+nullspace` **do not exist on
`+zm`**. Over ℤ a pivot cannot be scaled to 1 without leaving the ring, so
there is no RREF; the row-canonical form is the Hermite normal form, and
those arms belong to it. `+canon` has nothing to normalize — every `@s` is
already its own canonical form, so the arm would be the identity, which is
worse than an absent one. `+det` and `+rank` *do* exist: both are well
defined over ℤ, `rank` being the rank over ℚ.

### ℤ/n is not a field, and the arms say which ones care

Most of `+mm` needs no primality at all. Two arms do, and they assert it:

- **`+rank` and `+nullspace` require `n` prime.** Over a field the kernel
  is a vector space and every definition of rank agrees. Over composite
  ℤ/n the module is not free and they diverge, so there is no single
  number to return — and returning a plausible one anyway would be
  silently wrong.
- **`+det`, `+charpoly`, `+inv`, `+solve` require nothing.** `det` and
  `charpoly` lift to ℤ, compute there, and reduce: both are polynomials
  with integer coefficients in the entries, so the answer is independent
  of which representatives are lifted. That sidesteps Bareiss's exact
  divisions — unavailable in ℤ/n, since a divisor need not be a unit —
  rather than working around them.

### The ℤ/6 finding

**`+rref` can crash on a matrix that is invertible.** Over ℤ/6:

```
w = [[2 1] [3 1]]     det(w) = -1 = 5, a unit mod 6, so w is invertible
```

Yet neither entry of the first column is a unit mod 6, so Gauss–Jordan
with unit pivots cannot even start. Unit-pivot elimination is therefore
strictly weaker than invertibility over a composite modulus.

This is why **`+inv` does not go through `+rref`.** It uses the adjugate:
`A · adj(A) = det(A) · I` holds in *every* commutative ring, so
`A⁻¹ = det(A)⁻¹ · adj(A)` whenever `det(A)` is a unit — no pivoting
anywhere. The cost is O(n⁵), which is worth paying for an answer that is
correct over every modulus; the product is canonical, so a jet may do
better. All three behaviors are pinned by tests: `det:mm w = 5`,
`w · inv(w) = I`, and `rref:mm w` crashes.

### Normal forms carry their transforms

Escalation B1 is resolved: **carry the transform.** `hnf` returns
`[h u]` with `u · m = h`; `snf` returns `[d u v]` with `u · m · v = d`,
all three unimodular where they should be.

The deciding argument was testability. A bare `h` can only be checked
against another implementation; with the transform, `u · m = h` and
`det u = ±1` are exact properties the suite asserts directly — and the ℤ
kernel and ℤ-solve read the transform, not the form. It costs the same
row operations applied to an identity alongside.

Conventions, both row-style since Baloon is row-major and §7 is
row-indexed throughout:

- **`hnf`** — upper triangular; pivots strictly positive and strictly
  advancing; every entry *above* a pivot reduced into `[0, pivot)`; zero
  rows last.
- **`snf`** — diagonal, non-negative, `d_i | d_(i+1)`; the elementary
  divisors in the usual order, zeros last.

Both are unique for a given matrix, so both arms are `free`.

`snf` runs in two stages: alternate row/column clearing isolates each
diagonal entry, then a divisibility pass repairs any adjacent pair where
`d_i ∤ d_(i+1)` by folding one column into the other and re-isolating the
2×2 block. The scan restarts after each repair — fixing one pair can
disturb an earlier one — and terminates because the product of the
diagonal is invariant while `|d_i|` strictly decreases. Column operations
reuse the row-clearing routine through the transpose rather than being
written out a second time.

```
m = [[2 4 4] [-6 6 12] [10 -4 -16]]

hnf → h = [[2 4 4] [0 6 0] [0 0 12]]     det u = -1
snf → d = diag(2, 6, 12)                 det u = -1, det v = 1
```

### Verification

Cross-ring agreement is the cheapest real check Milestone C affords, and
it needs no external oracle: Milestone A's ℚ arms are already trusted
against SymPy, so they *are* the oracle for the new rings. `det:zm` must
agree with `det:qm` on the embedding, `charpoly:qm` with `charpoly:zm`
coefficient by coefficient, and `det:mm` with `det:zm` reduced.
Transcribed SymPy vectors pin fixed inputs on top of that, and **𝔽₂ and
𝔽₃ are covered exhaustively** — all 16 and all 81 2×2 matrices, with the
determinant cross-checked against `ad − bc`, an independent formula.

The normal forms are checked differently, and deliberately. SymPy's
`hermite_normal_form` is **column**-style, so it is not an oracle for a
row-style form without transposing — the Hermite *shape* is therefore
verified structurally, straight from the conditions above, which are
decidable directly. The Smith diagonal *is* checked against SymPy's
`invariant_factors`, which are canonical up to sign and so
convention-independent. That turned out to be the better test either way:
it verifies the definition rather than agreement with another program.

100 test arms, all green.

## Decision log

| # | Decision | Rationale |
|---|---|---|
| — | Indexing helpers written out in `+pv` rather than using `++snag` | `snag` carries a `~_` hint, so an out-of-range crash puts `"snag-fail"` into the trace. Trace payloads are observable under virtualization and would become part of the jet contract; B3 keeps them out. The local helpers crash bare, and public arms guard bounds with `?>` so the guard fires before any accessor could. |
| — | `$qrref`, not `$rref` | RREF is not ring-generic: over ℤ there is none at all, and the row-canonical form is Hermite. An unprefixed name in a multi-ring library is a trap that only springs once the second ring arrives. |
| — | `det` by Bareiss over ℤ, not Gauss–Jordan over ℚ | B4. Rational elimination swells denominators badly. Bareiss keeps every intermediate an exact integer — each division is exact by Sylvester's identity — so the arm clears denominators, eliminates over ℤ, then divides the scaling back out. Same discipline `gcd:qx` uses in delegating to `gcd:zx`. |
| — | `rref` pivots on the first nonzero, not the largest | There is no rounding error to control, so magnitude-based partial pivoting buys nothing. That technique belongs to Lagoon's world. First-nonzero is deterministic and exact. |
| — | Dimensions derived, not stored | Carrying `[r c data]` adds two invariants that can desync; deriving adds one, rectangularity. |
| — | `idn` vectors number 12, not 40 | The arm is parameterized only by a dimension, so there is no input variety to sample; sizes 1–12 cover the structure exhaustively. Padding to 40 would be ceremony, and 40×40 identity literals would add ~200 KB to the corpus. §11.2 was amended to permit this — see below. |

### Resolved spec question

§11.2 originally required ≥ 40 vector cases per public arm without
qualification. That fits arms with a rich input space and does not fit arms
parameterized only by a dimension, where `idn` and `zeros` exhaust their
structure in a dozen cases. The section now reads:

> ≥ 40 cases per public arm **where the arm's input space warrants it**; an
> arm parameterized only by a dimension may instead use exhaustive
> small-case coverage, documented in the decision log.

`idn` is the one arm relying on this. Every other family meets the 40
minimum.

A second concern raised at the same time turned out to be unfounded and
needed no amendment: §11.5's benchmark sizes of 4/8/16 were expected to be
impractical for interpreted exact arithmetic, but all three run comfortably
— the largest, `inv` at n = 16, takes 364 ms.
