# BALOON — Basic Linear ALgebra in hOON

**Engineering Specification v0.1 — Milestone A: the Hoon-normative kernel**

Status: **draft, for review**. Sections 6–10 become pinned on approval. This document mirrors `raccoon-spec.md` in structure deliberately: the discipline it imposed is the reason Racoon's four phases landed without rework.

Audience: as for Racoon. Assume competence; assume Racoon Milestone A is complete, frozen, and available.

---

## 1. Mission

Exact linear algebra over ℚ for Urbit, built entirely on Racoon. Determinants, reduced row echelon form, rank, inverse, linear solving, nullspace, characteristic polynomial, and rational eigenvalues — all exact, no floating point anywhere.

Baloon is to exact arithmetic what Lagoon is to approximate arithmetic. The two are siblings, not layers: Lagoon owns IEEE 754, fixed-point, posits, and complex; Baloon owns ℚ (and later ℤ and ℤ/n). Neither depends on the other.

`/lib/baloon` depends on `/lib/racoon` and nothing else, the same relationship `/lib/lagoon` has to `/lib/math`.

**Milestone A is ℚ only.** ℤ, ℤ/n, and 𝔽p are Milestone C (§13). They shape the type layer and the core layout now — §6 declares their matrix types and reserves their sub-cores, because both choices are cheaper to make once, up front, than to retrofit — but no arm in Milestone A consumes them.

## 2. Platform contract

Inherits Racoon's §2 in full: nouns, jets Kleene-equal on every input, crashes observable through the virtualization tower and therefore part of the interface, canonical-output principle, canonical inputs as the supported domain with no defensive re-canonicalization.

One consequence deserves emphasis because it differs from Racoon in a favorable way. **Every Baloon product is a canonical mathematical object.** The determinant, the reduced row echelon form, the rank, the inverse, the characteristic polynomial — each is unique for a given input. Racoon had five arms whose algorithm had to be pinned because their output was not fully determined (`egcd` cofactors, the Miller–Rabin witness schedule, the Mignotte bound). Baloon has none. §9 classifies every arm as `free`, and that is not an accident of drafting: it is a property of the subject.

The one place uniqueness needs help is the nullspace, where the *basis* is not unique. §7 pins a basis convention rather than an algorithm, which keeps the output canonical without constraining how a jet computes it.

## 3. Deliverables

| # | Path | Contents |
|---|------|----------|
| 1 | `desk/sur/baloon.hoon` | Shared types (§6) |
| 2 | `desk/lib/baloon.hoon` | The library. Single file, nested cores (§6) |
| 3 | `desk/lib/baloon-vectors.hoon` | Generated reference vectors. Never hand-edited |
| 4 | `desk/tests/lib/baloon.hoon` | Test suite (§11) |
| 5 | `desk/gen/baloon-bench.hoon` | Benchmark generator: timing table, no perf gates |
| 6 | `tools/genvec.py` | SymPy-based vector generator emitting deliverable 3 |
| 7 | `README.md` | Setup, test loop, pinned versions, recorded baselines, decision log |

Repository layout mirrors `racoon/`, with `scripts/sync.sh` copying an explicit file list into the pier.

A human-readable surface (`desk/lib/baloon-fmt.hoon` plus generators) follows the same consumer pattern Racoon's does: outside the frozen cores, importing the library like any other caller. It is not a Milestone A deliverable but should land early, for the same reason it did in Racoon — matrices printed as raw nested `frac` lists are unreadable, and `print ∘ parse` is a free property test.

## 4. Development environment

Identical to Racoon's §4, against the same pier and the same pinned Vere. Baloon's desk files sit alongside Racoon's; the test loop is `scripts/sync.sh`, `|commit %base`, `-test /=base=/tests/lib/baloon ~`.

## 5. Design invariants

- **B1.** Every public arm returns a canonical value. There are no pinned algorithms (§2). Where uniqueness needs a convention, §7 supplies one.
- **B2.** All crash conditions enumerated (§8) and tested, both the crashes and the non-crashes.
- **B3.** No `~|` anywhere in `lib/baloon.hoon`. As in Racoon: trace payloads are observable under virtualization, and keeping them out keeps the jet contract to crash-vs-value.
- **B4.** Coefficient swell is the failure mode of exact linear algebra. Prefer fraction-free methods over ℤ with a final rescale, the same discipline `gcd:qx` uses in delegating to `gcd:zx`.
- **B5.** Canonical inputs are the supported domain (§7); no defensive normalization inside arms.
- **B6.** After a phase gate closes, the battery layout of hinted cores is frozen. All sub-cores are declared up front (§6) so that the parent battery never moves — Racoon learned this the hard way; see its decision log Q5.
- **B7.** Dry gates only. Every arm carries an explicit `^-` product cast.
- **B8.** No dependencies beyond `hoon.hoon` standard arms, `/lib/racoon`, and `/lib/test` in the test file only.

## 6. Types and library structure

`desk/sur/baloon.hoon`:

```hoon
/-  *racoon
|%
::  Matrices are dense, row-major, nested lists.  Canonical form in every
::  ring: nonempty, rectangular (every row the same nonempty length), every
::  entry canonical for its ring.  Dimensions are derived, not stored:
::  rows = (lent m), cols = (lent (snag 0 m)).
::
::  Names are ring-prefixed throughout, as Racoon's $zol / $mol / $qol are.
::  Nothing here is unprefixed: an unprefixed name in a multi-ring library
::  is a trap that only springs once the second ring arrives.
::
::    $qmat: a matrix over Q.  Entries are canonical $frac.
::
+$  qmat  (list (list frac))
+$  qvec  (list frac)
::    $zmat: a matrix over Z.  Milestone C; declared now because the
::    representation question is already settled by $qmat's.
::
+$  zmat  (list (list @s))
+$  zvec  (list @s)
::    $mmat: a matrix over Z/n.  Entries lie in [0, n); the modulus is
::    carried by the +mm door, not by the matrix, exactly as Racoon's $mol
::    leaves n to +mx.  Milestone C.
::
+$  mmat  (list (list @ud))
+$  mvec  (list @ud)
::    $qrref: reduced row echelon form over Q, with its pivot columns.
::    .piv is ascending, and (lent piv) is the rank.
::
::  Ring-prefixed because RREF is NOT a ring-generic notion.  Over Z there
::  is no RREF at all -- a pivot cannot be scaled to 1 without leaving Z --
::  and the row-canonical form is instead the Hermite normal form.  Over
::  Z/n an RREF exists exactly when the needed pivots are units.
::
+$  qrref  [m=qmat piv=(list @ud)]
::
::  RESERVED, deliberately not declared: the Hermite and Smith normal form
::  products for +zm.  Whether they carry their unimodular transform
::  ([h=zmat u=zmat] against a bare h) depends on design work not yet done,
::  and guessing would pin a convention S14 would rather see escalated.
--
```

Dimensions are derived rather than carried. Carrying `[r c data]` would introduce two further invariants that can desync from the data; deriving introduces one (rectangularity). Fewer redundant invariants is the same reasoning that gave Racoon its no-trailing-zero polynomial form.

**Milestone A builds ℚ only.** `$zmat` and `$mmat` are declared so that naming and representation are settled once, while the reasoning is fresh, rather than chosen inconsistently later under pressure. No arm consumes them until Milestone C. Types carry no battery-axis consequence — they are not jetted — so declaring them early costs nothing, which is precisely why the genuinely unpredictable shapes above are left undeclared instead.

`desk/lib/baloon.hoon` skeleton:

```hoon
/-  *baloon, *racoon
/+  racoon
=<  baloon
~%  %non  ..part  ~
|%
+|  %private
++  pv   :: private helpers, outside the jet core
  |%  --
+|  %public
++  baloon
  ~/  %baloon
  |%
  ++  qm            ::  matrices over Q
    ~/  %qm
    |%  --
  ++  zm            ::  matrices over Z -- reserved, Milestone C
    ~/  %zm
    |%  --
  ++  mm            ::  matrices over Z/n -- reserved, Milestone C
    ~/  %mm
    |_  n=@ud  --
  --
--
```

`+zm` and `+mm` are declared empty from the outset. Adding an arm to a Hoon core moves the battery axes of the arms already in it, so introducing a sub-core later would shift the `%baloon` battery — and that is the parent axis every sub-core jet resolves against. This is Racoon's Q5, applied up front rather than retrofitted.

There are **three** sub-cores, not four: 𝔽p is ℤ/n with n prime, so it shares `$mmat` and the `+mm` door, exactly as Racoon serves both from `+mx`. Nor is there any `kind` tag or dispatch — `raccoon-spec` §16 records the generic-ring design as considered and rejected in favor of concrete per-ring cores, and Baloon does not relitigate it.

Note also that no new polynomial types are needed. `+charpoly` produces `qol` over ℚ, `zol` over ℤ (monic, integer coefficients), and `mol` over ℤ/n — all three already exist in Racoon's `sur`. Likewise `+det` produces `frac`, `@s`, and `@ud` respectively. The per-core signatures differ; no shared type does.

Private helpers live in `+pv`, outside the `%baloon` core, so helper churn cannot disturb a hinted core's layout.

## 7. Canonical conventions (normative)

| Item | Convention |
|---|---|
| `$qmat` | Nonempty, rectangular, entries canonical `frac`. The 0×n and n×0 cases do not exist; a matrix has at least one row and one column |
| Indexing | Zero-based. `(get m i j)` is row `i`, column `j` |
| Dimensions | Derived: `rows = (lent m)`, `cols = (lent (snag 0 m))` |
| `+canon` | The only arm accepting non-canonical input: re-canonicalizes every entry through `+new:qq`. Does **not** repair raggedness — a ragged input is outside the supported domain |
| `+rref` (`qm`) | The reduced row echelon form: leading entry of every nonzero row is 1, is the only nonzero in its column, and pivots strictly advance; zero rows sort last. Unique for a given matrix. `.piv` lists pivot columns ascending |
| `+rank` | `(lent piv:(rref m))` |
| `+det` | Crashes on non-square. `det` of a 1×1 is its entry. Canonical |
| `+inv` | Crashes on non-square and on singular. `inv(m) * m` is the identity exactly |
| `+solve` | `[a=qmat b=qmat] -> (unit qmat)`. Requires `a` square and `rows(b) = rows(a)`; crashes otherwise. Produces `~` **iff** `a` is singular, and the unique solution otherwise. Not a least-squares or parametric solver |
| `+nullspace` | Basis derived from the RREF, pinned: for each non-pivot (free) column `j`, one basis vector with 1 at `j`, 0 at every other free column, and `-(rref entry)` at each pivot position. Vectors ordered by ascending `j`. Empty list iff the matrix has full column rank. This convention is what makes the output canonical |
| `+charpoly` | `det(xI - A)` as a `qol`, monic of degree `n`. **Not** `det(A - xI)`, which differs by `(-1)^n` and agrees only in even dimension. Crashes on non-square |
| `+eigen` | The **rational** eigenvalues only, as `(list [val=frac mult=@ud])` sorted ascending by `+cmp:qq`. Obtained by clearing denominators of the characteristic polynomial and factoring over ℤ through `factor:zx`; each linear factor `ax + b` contributes the root `-b/a` with its multiplicity. Irrational and complex eigenvalues are not representable and are silently absent — the arm name and its documentation must say so plainly |
| `+pow` | Non-negative integer exponent; `m^0` is the identity of matching size. Binary square-and-multiply |
| Vector shape | A column vector is `n×1`, a row vector is `1×n`. There is no separate vector type in `$qmat`; `$qvec` appears only where a product is genuinely a bare list |

## 8. Crash table (normative — every row gets a test)

| Arm | Condition | Behavior |
|---|---|---|
| `+get` `+put` `+row` `+col` | index out of bounds | crash |
| `+add` `+sub` | dimension mismatch | crash |
| `+mul` | `cols(a) != rows(b)` | crash |
| `+det` `+inv` `+charpoly` `+pow` | non-square input | crash |
| `+inv` | singular input | crash |
| `+solve` | `a` non-square, or `rows(b) != rows(a)` | crash |
| `+solve` | `a` singular | **no crash**: product is `~` |
| `+idn` | `n = 0` | crash (the empty matrix is not representable) |
| `+zeros` | `r = 0` or `c = 0` | crash |
| `+nullspace` | full column rank | **no crash**: product is `~` |
| `+eigen` | no rational eigenvalues | **no crash**: product is `~` |
| any arm | ragged or empty input | outside the supported domain (§2, §5 B5): the Hoon computes deterministically, jets fall back; not asserted per-arm |

No `~|` anywhere (B3).

## 9. Public API by phase

Every arm is `free`: the product is canonical, so a Milestone B jet may use any algorithm. This is the whole table — there is no `pinned` column because there are no pinned arms.

### Phase 0 — shape and construction (`qm`)

| Arm | Signature | Notes |
|---|---|---|
| `canon` | `qmat -> qmat` | Re-canonicalizes entries; the only arm accepting non-canonical input |
| `dims` | `qmat -> [r=@ud c=@ud]` | Derived |
| `get` | `[qmat @ud @ud] -> frac` | Zero-based |
| `put` | `[qmat @ud @ud frac] -> qmat` | |
| `row` `col` | `[qmat @ud] -> qvec` | |
| `transpose` | `qmat -> qmat` | |
| `idn` | `@ud -> qmat` | Identity |
| `zeros` | `[@ud @ud] -> qmat` | |
| `is-square` | `qmat -> ?` | |

### Phase 1 — arithmetic (`qm`)

`add`, `sub`, `neg`, `mul` (classical, triply nested), `scale` (scalar times matrix), `pow`. Entry arithmetic goes through `qq` throughout, so every product is canonical by construction.

### Phase 2 — elimination (`qm`)

| Arm | Signature | Spec algorithm |
|---|---|---|
| `rref` | `qmat -> qrref` | Gauss–Jordan. Pivot selection is the first nonzero in the column at or below the current row — deterministic and exact; there is no magnitude-based pivoting because there is no rounding to control |
| `rank` | `qmat -> @ud` | `(lent piv:(rref m))` |
| `det` | `qmat -> frac` | **Bareiss fraction-free elimination** over ℤ: clear denominators to an integer matrix, run Bareiss with its exact divisions, rescale. B4 — plain elimination over ℚ swells denominators badly |
| `inv` | `qmat -> qmat` | Gauss–Jordan on `[m | I]` |
| `solve` | `[qmat qmat] -> (unit qmat)` | Gauss–Jordan on the augmented matrix |
| `nullspace` | `qmat -> (list qvec)` | RREF, then the §7 basis convention |

### Phase 3 — spectral (`qm`)

| Arm | Signature | Spec algorithm |
|---|---|---|
| `charpoly` | `qmat -> qol` | Faddeev–LeVerrier, or interpolation, or expansion — the product is canonical either way. Output is monic of degree `n` |
| `eigen` | `qmat -> (list [val=frac mult=@ud])` | Clear denominators of `charpoly`, factor over ℤ through `factor:zx`, collect the linear factors' roots |

`eigen` is where Baloon and Racoon compose: exact eigenvalues fall out of polynomial factorization, which is the whole reason Racoon's Phase 3 was worth building.

## 10. Jet-readiness obligations

- Registration mirrors `/lib/racoon.hoon`, which in turn mirrors `urbit/numerics` `/lib/math.hoon`: one root `~%  %non  ..part  ~`, then `~/` per nested core, per-arm `~/` on the heavy arms. Follow the file, not any prose that contradicts it — see Racoon's Q4.
- Arms carrying `~/` hints: `qm`: `mul rref det inv solve charpoly`.
- All sub-cores declared up front (§6, B6).
- Battery freeze applies at each phase gate to that core's completed arms; the interface freezes entirely when P3 closes.

## 11. Testing requirements

1. **Framework.** `/lib/test`, arms `++test-p0-*` through `++test-p3-*`. Every §8 crash row gets a dedicated expected-crash test, and every non-crash row gets a matching expected-success test. §8 is a two-sided contract.
2. **Reference vectors.** `tools/genvec.py`, SymPy as oracle: `Matrix.det`, `.rref`, `.rank`, `.inv`, `.nullspace`, `.charpoly`. ≥ 40 cases per public arm **where the arm's input space warrants it**; an arm parameterized only by a dimension may instead use exhaustive small-case coverage, documented in the decision log. Deterministic from a pinned seed. Adversarial families: singular matrices, rank-deficient of every rank, 1×1, wide and tall, matrices with large denominators, matrices whose Bareiss intermediates swell, identity and zero, permutation matrices, and matrices with rational eigenvalues of multiplicity > 1.
3. **Verify SymPy's conventions, do not assume them.** Racoon lost time to `sympy.resultant` silently normalizing its argument order, which produced a wrong sign for `deg a < deg b` and would have baked that into the vectors. Before pinning any convention against SymPy, confirm it against the definition. Already confirmed: `charpoly` is `det(xI - A)`; `rref` returns `(matrix, pivot-tuple)`; the `nullspace` basis matches §7's convention.
4. **Property tests**, in-ship, `++og` from seeds pinned in the test file. Minimum: `inv(m) * m = I` exactly; `det(a*b) = det(a) * det(b)`; `det(transpose m) = det m`; `rank(m) + (lent (nullspace m)) = cols(m)` (rank–nullity); every nullspace basis vector satisfies `m * v = 0`; `solve` products satisfy `a * x = b`; `charpoly` is monic of degree `n` and `charpoly(A)` evaluated at each rational eigenvalue is zero; RREF is idempotent.
5. **Benchmarks.** `det`, `inv`, `rref`, and `mul` at sizes 4/8/16 over ℚ with moderate denominators, plus `charpoly` at size 8. Plain table, no gates; baselines recorded in `README.md`.

## 12. Phase gates

A phase closes when: the library compiles clean; all tests for this and prior phases pass; vector minimums met; crash rows covered on both sides; bench baselines recorded; battery freeze applied; decision log updated. Phases land as separate reviewed changes.

- **P0**: shape and construction complete.
- **P1**: arithmetic complete.
- **P2**: elimination complete, including fraction-free `det`.
- **P3**: `charpoly` and `eigen` complete; rank–nullity and `inv*m = I` green at all sampled sizes.

## 13. Out of scope — hard fence

No floating point (Lagoon owns it). No matrices over ℤ or ℤ/n in Milestone A — `+zm` and `+mm` are declared but empty, and are Milestone C. No Hermite or Smith normal form. No LLL. No LU/QR/SVD decompositions. No eigenvectors, and no eigenvalues outside ℚ. No sparse representation. No symbolic matrix entries. No performance work beyond recording baselines. No jets.

Milestone C candidates, for context: integer linear algebra with HNF and SNF; matrices over ℤ/n and 𝔽p; eigenvectors for rational eigenvalues; minimal polynomial; PLU with a deterministic pivot convention.

Two notes for whoever picks up ℤ and ℤ/n, recorded now while the reasoning is fresh:

- **The ℤ machinery is largely built already.** `+det:qm` is specified as Bareiss, which clears denominators, eliminates over ℤ, and rescales. `+zm` therefore mostly *promotes* private `+pv` helpers to public arms rather than writing them fresh.
- **`+mm` likely needs no primality assertion.** Racoon's factorization genuinely requires a field, so `sqfree`, `ddf`, `edf`, and `factor` assert it. Linear algebra needs strictly less: elimination requires only that each pivot it actually uses be a unit. So `+rref:mm` should crash on a non-unit pivot — the same discipline as `+divmod:mx` crashing on a non-unit leading coefficient — and over 𝔽p that crash is unreachable, since every nonzero element is a unit. That is a §8 crash row, not a §5 invariant.

## 14. Escalation and decision authority

**Delegated**: private helper structure and naming; test-file organization; vector counts above minimums; script and README details.

**Escalate**: any change to §6–§10 pinned material — types, canonical conventions, crash rows, public signatures; reuse of kernel arms beyond B8; any place this spec appears mathematically wrong, with the counterexample.

Silence is not acceptance for pinned material.

## 15. Style

Kernel style, as Racoon: `::` header per arm stating the mathematical contract, explicit `^-`, `?>` guards, 80 columns, no `~|`, no wet gates without justification. Follow §9's table order within each core.

## 16. References

- `raccoon-spec.md` — the sibling specification, and the source of this document's structure.
- Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination" (1968) — the fraction-free determinant.
- von zur Gathen & Gerhard, *Modern Computer Algebra* — linear algebra over rings, §5 and §25.
- `urbit/numerics` `/lib/lagoon` — the approximate sibling; precedent for array-library shape, not for representation.

---

# Milestone C — ℤ and ℤ/n

**Engineering Specification v0.2 — Milestone C: the remaining rings**

Milestone B (jets) is deferred until there are more clients; Milestone C
proceeds ahead of it. Nothing here is jetted, so the freeze discipline
below is about keeping the *option* of jets, not about serving existing
ones.

## C1. Why this costs no escalation

`+zm` and `+mm` were declared empty in §6 for exactly this moment. Adding
arms *inside* them leaves `%baloon`'s own battery at three arms, so `+qm`'s
axes — frozen when Milestone A's P3 closed — do not move. Milestone C adds
no arm to `%baloon` and no arm to `+qm`.

Two consequences follow, and they are load-bearing:

- **`+qm` stays shut.** `minpoly` and rational eigenvectors are Milestone C
  candidates (§13) but are *not* added to `+qm`. They go in
  `/lib/baloon-spectral`, a consumer, computed from `qm`'s public arms
  alone — the pattern `/lib/racoon-rs` and `/lib/racoon-fp3` have now
  established twice. A frozen interface that gets reopened for every good
  idea was never frozen.
- **`$qmat`, `$zmat`, `$mmat` are unchanged.** §6 settled the
  representation for all three at once. Milestone C adds no matrix type.

## C2. Canonical conventions (normative)

Everything in §7 carries over unchanged where it is ring-generic:
nonempty, rectangular, dense, row-major, zero-based, dimensions derived,
`+canon` the only arm accepting non-canonical input.

| Item | Convention |
|---|---|
| `$zmat` | Entries are `@s`. There is no normalization beyond `@s` itself — every integer is its own canonical form |
| `$mmat` | Entries lie in `[0, n)`. The modulus is the `+mm` door's sample, never the matrix's |
| `+det:zm` | Bareiss, exact. Result `@s`. Crashes on non-square |
| `+det:mm` | **Lift to ℤ, take the integer determinant, reduce mod n.** The determinant is a polynomial with integer coefficients in the entries, so this is exact for *any* representatives and any `n`, prime or not. Bareiss's exact divisions are unavailable in ℤ/n — a divisor need not be a unit — and this sidesteps that entirely rather than working around it |
| `+charpoly:zm` | `det(xI − A)` as a `zol`, monic of degree `n` |
| `+charpoly:mm` | `det(xI − A)` as a `mol`. Same lift-and-reduce argument as `+det:mm`: the coefficients are integer polynomials in the entries |
| `+rref:mm` | Gauss–Jordan. **Pivot selection is the first entry at or below the current row that is a UNIT mod n** — not merely the first nonzero. If a column has nonzero entries at or below the current row but no unit among them, the arm crashes (§C3). Over 𝔽p every nonzero element is a unit, so the search always succeeds on the first nonzero and the crash is unreachable |
| `+rank:mm` `+nullspace:mm` | **Require `n` prime, asserted.** Over a field the kernel is a vector space and §7's basis convention transfers exactly. Over composite ℤ/n the kernel is not free, rank is not well defined, and a unit-pivot echelon form does not generate the whole kernel — producing a plausible-looking submodule basis would be silently wrong, which is worse than crashing |
| `+inv:mm` `+solve:mm` | Need only that `det` be a **unit** mod n, which is decidable without primality. No assertion |
| `+to-q` `+of-q` | The ring bridges live in the *later* core, never in frozen `+qm`. `to-q:zm` embeds exactly. `of-q:zm` clears denominators and returns `[m=zmat d=@ud]`, the common denominator alongside, since the map ℚ → ℤ loses information otherwise |
| `+to-z:mm` | Lifts to the **symmetric** representatives, in `(−n/2, n/2]`. `of-z:mm` reduces. `to-z ∘ of-z` is not the identity; that is what "representative" means and the arms say so |

## C3. Crash table (normative — every row gets a test)

Every §8 row carries over to `+zm` and `+mm` with the same behavior. New
rows:

| Arm | Condition | Behavior |
|---|---|---|
| `+rref:mm` `+inv:mm` `+solve:mm` | a column needing a pivot has nonzero entries but no unit among them | crash |
| `+inv:mm` | `det` is not a unit mod n | crash |
| `+solve:mm` | `det` is not a unit mod n | **no crash**: product is `~` |
| `+rank:mm` `+nullspace:mm` | `n` not prime | crash |
| `+of-q:zm` | ragged or non-canonical input | outside the supported domain |
| `+mm` any arm | `n < 2` | outside the supported domain |

`+canon`, `+rref`, `+inv`, `+solve`, and `+nullspace` **do not exist on
`+zm`.** `+canon` has nothing to normalize, as §C4 records. `+rank` and
`+det` do exist — both are well defined over ℤ. For the rest: over ℤ a pivot cannot be scaled to 1 without leaving the
ring, so there is no RREF; the row-canonical form is the Hermite normal
form and they belong to it. Declaring them and crashing would be worse
than their absence.

## C4. Phases

- **C0 — `+zm` shape and arithmetic.** `dims is-square get put row col
  transpose idn zeros add neg sub scale mul pow to-q of-q`, in `+qm`'s
  order so the two cores read side by side. **No `+canon`**: over ℚ the
  entries carry a normal form `+new:qq` imposes, but every `@s` is already
  its own canonical form, so the arm would be the identity. An arm that
  does nothing is worse than an absent one.
- **C1 — `+zm` over ℤ.** `det rank charpoly`. `+det` promotes
  `bareiss:pv` to a public arm rather than writing it fresh, as §13
  anticipated. `rank` needs no qualifier: the rank of an integer matrix
  is its rank over ℚ, equivalently the size of its largest nonvanishing
  minor, and the two agree. That is exactly the property composite ℤ/n
  lacks, which is why `+rank:mm` asserts primality and this one does
  not.
- **C2 — `+zm` normal forms.** Hermite, and Smith if C2's escalation
  lands. **Blocked on the §6 reservation** — see `SPEC-QUESTIONS.md` B1.
- **C3 — `+mm` complete.** Shape, arithmetic, and elimination in one
  phase: it is `+qm`'s arm set over a different ring, and splitting it
  would create phase gates with nothing to decide.

## C5. Testing

§11 carries over. Additions:

- SymPy oracles: `Matrix.det`, `.charpoly`, `.rref` and `.nullspace` over
  `GF(p)` via `Matrix.rref(iszerofunc=...)` or `polys.matrices`, and
  `.hermite_normal_form`. **Verify each convention against the definition
  before pinning it** (§11.3) — SymPy's HNF is column-style by default,
  which is not what C2 specifies.
- Cross-ring property tests, which are the cheapest real check Milestone C
  affords: `det:zm` of an integer matrix equals `det:qm` of its embedding;
  `det:mm` equals `det:zm` reduced; `charpoly:mm` equals `charpoly:zm`
  reduced; `inv:mm` times the matrix is the identity. Milestone A's ℚ arms
  are already trusted, so they serve as the oracle for the new rings
  without any external dependency at all.
- 𝔽p exhaustive coverage where it is affordable: all 2×2 matrices over
  𝔽₂ and 𝔽₃ (16 and 81 of them) checked for `det`, `inv` where it exists,
  and rank–nullity.
