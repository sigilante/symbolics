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

**Milestone B is deferred** until there are more clients, in step with
Racoon. Nothing here is jetted, so the freeze discipline is about keeping
the *option* of jets rather than serving existing ones.

## Layout

```
baloon/
  desk/
    sur/baloon.hoon           shared types
    lib/baloon.hoon           the library -- qm zm mm
    lib/baloon-vectors.hoon   generated vectors -- never hand-edited
    lib/baloon-fmt.hoon       rendering and parsing, all three rings
    lib/vanhoeij.hoon         LLL and van Hoeij -- imports BOTH libraries
    lib/baloon-alg.hoon       racoon-alg with van Hoeij bound in
    tests/lib/baloon.hoon     test suite -- Q, Z, and Z/n
    tests/lib/vanhoeij.hoon   LLL and van Hoeij
    gen/baloon-bench.hoon     benchmark generator
    gen/baloon-det.hoon       parse, print, and analyze a matrix
    gen/baloon-lll.hoon       reduce an integer lattice basis
    gen/baloon-lll-bench.hoon time +lll on a van Hoeij-shaped lattice
    gen/baloon-vh-bench.hoon  van Hoeij against Zassenhaus, same input
    gen/baloon-alg-bench.hoon algebraic arithmetic, van Hoeij column
  tools/genvec.py             SymPy vector generator
  tools/requirements.txt      pinned SymPy version
  scripts/sync.sh             copy desk/ into the pier
  README.md                   this file
  SPEC-QUESTIONS.md           escalation log
```

`baloon-fmt` is a **consumer**: it imports the frozen library like any other
caller and is not part of it. So is anything else built on top —
`minpoly` and rational eigenvectors will go in a consumer library rather
than into `+qm`, which is the substance of resolved question B2.

Baloon's desk files sit alongside Racoon's in the same `%base`, so sync
Racoon first if the pier is fresh.

## Lattice reduction and van Hoeij recombination

`/lib/vanhoeij` is Milestone C phase V, and **both phases are built**: V0
is LLL over ℤ, V1 is van Hoeij recombination on top of it
(`raccoon-spec.md` §V).

**It lives here because it is a consumer of *both* libraries.** LLL
operates on integer lattice bases — that is exactly `$zmat` — and
Milestone C already supplies `det`, `mul`, `rank`, and the Hermite form
over ℤ. Racoon cannot import Baloon, since the dependency runs the other
way, so putting LLL in Racoon would have meant duplicating all of it.
Escalation R4 in `racoon/SPEC-QUESTIONS.md` records the decision.

**`+lll` is `pinned`, not `free`** — the first pinned arm outside Racoon's
five. A lattice has *many* LLL-reduced bases, so the output is
underdetermined by the specification and a jet cannot be allowed to pick a
different one. The procedure is the contract, exactly as for `egcd:nz`.
What is pinned is δ = 3/4, the classic algorithm, descending-order size
reduction, ties-away-from-zero rounding, and the swap rule — **not** how
the Gram–Schmidt data is computed, since exact rational GSO and an
incrementally updated one are mathematically equal and yield the same
output.

Pinning stops there: van Hoeij's `factor` is `free`, because every
candidate is verified by trial division regardless of which reduced basis
LLL returned.

**Exact rationals throughout.** The classic LLL failure mode is a
Gram–Schmidt computed in floating point drifting until the Lovász test
flips the wrong way. Here it cannot happen.

**Verified structurally, not against another program.** SymPy has
`DomainMatrix.lll`, but an LLL-reduced basis is **not unique** — two
correct implementations at the same δ can return different bases — so
matching its output is neither necessary nor sufficient. §11.3 says
confirm a convention before pinning it against a tool; here the conclusion
is that the tool is the wrong oracle. The definition is checked instead,
and it is complete:

- **size-reduced**: `|μ_ij| ≤ 1/2`
- **Lovász**: `‖b*_k‖² ≥ (3/4 − μ²_{k,k−1})·‖b*_{k−1}‖²`
- **same lattice**: `hnf:zm` of the input equals `hnf:zm` of the output —
  which needs no oracle at all, and is exactly the check phase C2 made
  possible

Any basis satisfying all three *is* an LLL-reduced basis of that lattice.
`+reduced` is exposed so callers can assert it too. On the worked example
the output happens to agree with SymPy's, which is worth noting and is not
a guarantee.

### Recombination

`+factor` is the phase V1 arm: `zol -> (list zol)`, the irreducible
factors over ℤ of a squarefree primitive polynomial. The chain is
Hensel-lifted modular factors from `hdata:zx`, power sums by Newton's
identities, the knapsack lattice, `+lll`, 0-1 patterns read off the short
vectors, trial division into `f`, and Zassenhaus over whatever is left.

**The lattice is an accelerator, never an oracle.** Every candidate
subset — however it was proposed — is confirmed by dividing into `f`, and
anything the lattice misses falls through to the same enumeration
`+firr:zx` uses. A bug in the bound, the scaling, the choice of power
sums, or `+lll` itself can make this slower; it cannot make it wrong.
That is what lets a heuristic-shaped algorithm be `free`, and it is why
`+factor` and `+firr:zx` agree on every input by construction rather than
by luck.

**`+fact` exposes the gate, and it has to.** Since a lattice that
proposes nothing at all is invisible to a test that only checks the
answer, `+fact f 0` forces the pass at every `r`; `+factor` supplies
`+lat-min`. The suite uses the forced form to check that the lattice
proposes the *right* subsets rather than none.

**`+lat-min` is 16, and it is measured, not chosen.** Below sixteen
modular factors the subset enumeration is cheaper than reducing the
lattice, so `+factor` runs plain Zassenhaus there — which is the shape of
the table below. `r = 12` is untested; lowering the gate to reach it
should be measured rather than assumed.

**Power sums are computed in monic form and never divide.** Newton's
identities carry a division by `k`, and over ℤ/p^a a `k` divisible by `p`
is not a unit. The recurrence is arranged so the division never happens.

### Benchmarks — where the speed difference is the deliverable

```
+baloon-vh-bench 5 0    Zassenhaus on SD_5
+baloon-vh-bench 5 1    van Hoeij on SD_5
```

This is the one place in the project where a speed difference is the
product rather than a footnote (§V7.5). Same machine, same inputs, both
answers correct and identical. The van Hoeij column forces the lattice
with `+fact f 0`, because at `r = 4` and `r = 8` the gate would otherwise
hand the work to Zassenhaus and the table would be comparing it with
itself. Vere 4.6, `%zuse` 409, fake `~zod`, `--loom 33`, Darwin arm64,
best of two.

| | modular factors `r` | Zassenhaus | van Hoeij |
|---|---:|---:|---:|
| `SD_3` | 4 | 22.4 ms | 42.5 ms |
| `SD_4` | 8 | 298.7 ms | 459.7 ms |
| `SD_5` | 16 | 202.5 s | **9.42 s** — 21.5× |

**`SD_5` is the number that mattered.** `raccoon-spec.md` §V0 measured
Zassenhaus there at 204 s and named it the benchmark phase V1 has to
beat; the cost is exponential in `r`, not in the degree, so `SD_4`'s 39
subsets become `SD_5`'s 39,202. Van Hoeij replaces that enumeration with
one lattice reduction and comes back in under ten seconds.

**Below the crossover it loses, and the table says so.** Building the
lattice costs more than trying ten subsets, so at `SD_3` and `SD_4` van
Hoeij is roughly 1.5× slower. That is what `+lat-min` is for: engaging
the lattice is never the slower choice at the default entry point.

**What made it work was not the algorithm.** An earlier `+lll` on
rational Gram–Schmidt made four trace columns at `r = 16` cost 221.7 s,
against an enumeration of 197.9 s — so the column budget was two, and two
columns cannot separate this family. Rewriting `+lll` onto integer Gram
determinants brought the same reduction to 2.3 s, the budget became
eight, and eight separates. `baloon/SPEC-QUESTIONS.md` V1 records the
whole line, including the two dead ends, which are still true in
isolation.

### The first consumer: `/lib/baloon-alg`

Racoon's `/lib/racoon-alg` — real algebraic numbers — reduces every
operation to a minimal polynomial, which means factoring, and that is
where `factor` earns its keep. But `racoon/desk` builds from Racoon
alone and must keep doing so, and `/lib/vanhoeij` is on this side.

So `racoon-alg` is a **door over its recombination step**, defaulting to
`firr:zx`, and this file is that door with `factor:vh` bound in:

```hoon
/+  al=racoon-alg, vh=vanhoeij
~(. al factor:vh)
```

That is the entire library. It exists so the fast path is a plain import
rather than a line someone has to remember — forgetting it returns the
right answer at 281.9 s instead of 90.4 s, with nothing to notice. The
two bindings are asserted to agree in `tests/lib/vanhoeij`, and
`/gen/baloon-alg-bench` is the van Hoeij column of the table in
`racoon/README.md`.

## Every arm in `+qm`, `+zm`, and `+mm` is `free`

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

112 arms, all green. Behavioral, property, crash-row, and vector-driven.
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

**All three rings are covered**, and the trailing letter names the ring —
the convention `racoon-fmt` already uses for `shoz`/`shom`/`shoq` and
`redz`/`redq`:

| | ℚ | ℤ | ℤ/n |
|---|---|---|---|
| render matrix | `shoq` | `shoz` | `shom` |
| render vector | `shovq` | `shovz` | `shovm` |
| parse matrix | `redq` | `redz` | `redm` |
| parse vector | `redvq` | `redvz` | `redvm` |

Milestone A called these `shom` and `redm` — for *matrix*, when there was
one ring and no ambiguity to have. Milestone C created the ambiguity:
`$mmat` **is** the ring ℤ/n, so `redm` parsing a matrix over ℚ had become
actively wrong. They were renamed rather than worked around, which is the
whole reason `/sur/baloon` ring-prefixes every type it declares.

`shod` is shared by all three and takes *dimensions* rather than a matrix,
since a shape is not a ring-dependent notion: `(shod (dims:zm m))`.

Two things the ℤ/n side cannot do, and says so instead of guessing: the
modulus lives on the `mm` door rather than on the matrix, so `shom` does
not print it, and `redm` rejects a negative literal outright — `-1` has no
representative without knowing `n`. Parse over ℤ and reduce through
`of-z:mm` when negative input matters. Parsed entries are never reduced;
that is `canon:mm`'s job.

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

### The integer kernel and the integer solve

`hnf` was argued for on two grounds; this is the second one, cashed in.

**`nullspace:zm` reads the transform, not the form.** `u · mᵀ = h`, and
row *i* of `h` is zero exactly when row *i* of `u` annihilates `mᵀ` from
the left — that is, lies in the right kernel of `m`. Unimodularity is
what makes those rows a basis **over ℤ** and not merely over ℚ: they
extend to a basis of the whole lattice, so the sublattice they generate
is saturated and no integer kernel vector is missed.

That distinction is testable, and tested. The kernel of `[[2 4] [4 8]]`
is spanned by `(2, −1)` — *not* `(4, −2)`. A basis read off a rational
nullspace need not be saturated; one read off a unimodular transform
always is.

**It needs a second Hermite pass to be canonical.** `h` is unique for a
given matrix but `u` is *not* when the kernel is nontrivial: any multiple
of a kernel row may be added to another. Running the kernel rows through
`hnf` again fixes it, because the Hermite form of a full-row-rank matrix
depends only on the lattice its rows generate. So the output is a
function of `m` alone, and the arm stays `free`.

**`solve:zm` turns out not to need HNF at all.** For square `a` the
rational solution is already unique, and the only question is whether it
lands in ℤ. `of-q` returns the *least* common denominator of its input,
so `d = 1` is exactly the integrality test — no per-entry check, no
divisibility argument. Two situations collapse into its `~`, and the arm
says so plainly: `a` may be singular, or the unique rational solution may
simply not be integral, as for `2x = 1`.

`canon`, `rref`, and `inv` remain absent from `zm`. There is no RREF over
ℤ, and `inv` would be defined only for the `det = ±1` case that `solve`
already covers.

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

112 test arms, all green.

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
