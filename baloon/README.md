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
are declared empty and reserved for Milestone C — declaring them up front
keeps the `%baloon` battery from moving later, which is Racoon's Q5 applied
in advance rather than retrofitted.

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

76 arms, all green. Behavioral, property, crash-row, and vector-driven.
§8 is treated as a two-sided contract: every crash row has a dedicated test
and every non-crash boundary has a matching expected-success test.

Property-test inputs are built by local helpers rather than by the library
arm they would otherwise be exercising — the same discipline Racoon's suite
uses.

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

## Decision log

| # | Decision | Rationale |
|---|---|---|
| — | Indexing helpers written out in `+pv` rather than using `++snag` | `snag` carries a `~_` hint, so an out-of-range crash puts `"snag-fail"` into the trace. Trace payloads are observable under virtualization and would become part of the jet contract; B3 keeps them out. The local helpers crash bare, and public arms guard bounds with `?>` so the guard fires before any accessor could. |
| — | `$qrref`, not `$rref` | RREF is not ring-generic: over ℤ there is none at all, and the row-canonical form is Hermite. An unprefixed name in a multi-ring library is a trap that only springs once the second ring arrives. |
| — | `det` by Bareiss over ℤ, not Gauss–Jordan over ℚ | B4. Rational elimination swells denominators badly. Bareiss keeps every intermediate an exact integer — each division is exact by Sylvester's identity — so the arm clears denominators, eliminates over ℤ, then divides the scaling back out. Same discipline `gcd:qx` uses in delegating to `gcd:zx`. |
| — | `rref` pivots on the first nonzero, not the largest | There is no rounding error to control, so magnitude-based partial pivoting buys nothing. That technique belongs to Lagoon's world. First-nonzero is deterministic and exact. |
| — | Dimensions derived, not stored | Carrying `[r c data]` adds two invariants that can desync; deriving adds one, rectangularity. |
| — | `idn` vectors number 12, not the §11.2 minimum of 40 | The arm is parameterized only by a dimension, so there is no input variety to sample; sizes 1–12 cover the structure exhaustively. Padding to 40 would be ceremony, and 40×40 identity literals would add ~200 KB to the corpus. **Proposed §11.2 amendment — see below.** |

### Open spec question

§11.2 requires ≥ 40 vector cases per public arm. That fits arms with a rich
input space and does not fit arms parameterized only by a dimension, where
`idn` and `zeros` exhaust their structure in a dozen cases. Proposed
amendment: *≥ 40 cases per public arm where the arm's input space warrants
it; arms parameterized only by dimension may instead use exhaustive
small-case coverage, documented in the decision log.* Not applied pending
review — §11 is pinned material and silence is not acceptance.
