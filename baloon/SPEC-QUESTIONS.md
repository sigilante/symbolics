# Baloon — escalation log

Per `baloon-spec.md` §14, pinned material (§6–§10, and §C2–§C3 for
Milestone C) changes only by escalation. Silence is not acceptance.

## B1 — Hermite and Smith normal form: what does the arm return? (RESOLVED)

**Status: resolved — carry the transform. Phase C2 is built, and
`+nullspace:zm` now consumes the transform, which was reason 2 below.**

`+hnf` returns `[h=zmat u=zmat]` with `u · m = h`; `+snf` returns
`[d=zmat u=zmat v=zmat]` with `u · m · v = d`. Both forms and both
conventions below are now pinned in §C2. The original argument follows.

§6 reserved this deliberately:

> RESERVED, deliberately not declared: the Hermite and Smith normal form
> products for `+zm`. Whether they carry their unimodular transform
> (`[h=zmat u=zmat]` against a bare `h`) depends on design work not yet
> done, and guessing would pin a convention S14 would rather see
> escalated.

The design work is now done, and the question is ready to answer.

**Recommendation, accepted: carry the transform.** `+hnf` returns
`[h=zmat u=zmat]` with `u * m = h`, and `+snf` returns `[d=zmat u=zmat
v=zmat]` with `u * m * v = d`.

Three reasons, in order of weight:

1. **It makes the arm checkable.** A bare `h` can only be verified against
   another implementation. With the transform, correctness is a property
   the test suite can assert directly and exactly: `u * m = h` and
   `det u = ±1`. That is the difference between a tested arm and a
   transcribed one, and this project has twice caught real bugs that way.
2. **The kernel and the ℤ-solve need it.** `nullspace` and `solve` over ℤ
   are the reason to have HNF at all, and both read the transform, not the
   form. Returning only `h` would mean computing it twice.
3. **It is nearly free.** The transform is the same row operations applied
   to an identity alongside — a constant factor, not a complexity change.

The cost is that a caller wanting only `h` carries an n×n matrix it will
discard. That is a smaller harm than an untestable arm.

**Conventions to pin at the same time**, all row-style, since Baloon is
row-major and §7 is row-indexed throughout:

- `+hnf`: upper triangular; every pivot strictly positive; each entry
  *above* a pivot reduced into `[0, pivot)`; zero rows last.
- `+snf`: diagonal, non-negative, with `d_i | d_{i+1}` — the elementary
  divisors in the usual order.

Note SymPy's `hermite_normal_form` is **column**-style, so it cannot be
used as an oracle without transposing. §C5 records this. In the event the
Hermite shape is checked STRUCTURALLY instead — the conditions above are
decidable directly — while the Smith diagonal is checked against SymPy's
`invariant_factors`, which *are* canonical up to sign and so are
convention-independent. That turned out to be the better test anyway: it
verifies the definition rather than agreement with another program.

## B2 — `+qm` stays frozen (RESOLVED, no escalation needed)

Recorded so the reasoning is not relitigated. `minpoly` and rational
eigenvectors are §13 Milestone C candidates, but adding either to `+qm`
would move the battery axes of arms frozen at Milestone A's P3 gate. They
are computable from `qm`'s public arms alone, so they go in
`/lib/baloon-spectral` as a consumer — the pattern `/lib/racoon-rs` and
`/lib/racoon-fp3` established. No escalation required, and the freeze
holds.

---

## V1 — the lattice pass, and what made it work (RESOLVED)

**Status:** resolved. Phase V1 beats Zassenhaus on `SD_5` by a factor of
twenty. This entry previously recorded the opposite, and is rewritten
rather than appended to because the finding was not a nuance that needed
qualifying — it was wrong, and the machine said so.

Measured both ways, same inputs, same machine:

| | Zassenhaus | van Hoeij (before) | van Hoeij (after) |
|---|---:|---:|---:|
| `SD_3` | 21.3 ms | 99.4 ms | 43.2 ms |
| `SD_4` | 282.3 ms | 2161.3 ms | 463.2 ms |
| `SD_5` | 197.9 s | 239.2 s | **9.6 s** |

`raccoon-spec.md` §V0 named `SD_5`'s 204 s as the number to beat.

**The algorithm never changed. The arithmetic under it did.** The earlier
entry concluded that the lattice could not separate the Swinnerton–Dyer
family because separation needs many trace columns and columns cost more
than the enumeration they replace. The first half was right and the
second was an artifact of a slow `+lll`:

- four columns at `r = 16` cost **221.7 s** on the rational Gram–Schmidt,
  against an enumeration of 197.9 s — so the budget was pinned at two,
  and two cannot separate;
- the same lattice reduces in **2.3 s** on the integral one, so the budget
  became eight, and eight separates.

**Why eight and not four.** Four columns separate `SD_3` — it proposes
`{0,1,2,3}` and concludes irreducibility with no enumeration. They do not
separate `SD_5`, whose offending subsets have size 8: their indicators are
*shorter* than the all-ones vector, so they survive four conditions and
are excluded only by eight. The general shape is that the subsets which
satisfy the trace conditions honestly, without being factors over ℚ, are
factorizations over a subfield; each additional power sum is one more
condition they must survive.

**What the fix was.** `+lll` now runs on integer Gram determinants and
scaled `λ` rather than on `$frac`, so the gcd traffic that dominated it is
gone structurally. Dimension 9 went 315 s → 52 s → 3.4 s → **0.135 s**
across the four versions, and every one of them produces bit-identical
output — the fingerprint in `/gen/lllfp` has read 1.514.599.515 through
all of it, which is what `pinned` requires (SPEC V2).

**Recorded so it is not re-derived:** the two dead ends were real and are
still true in isolation. `s_1` alone is useless on this family (an even
polynomial's modular factors have roots summing to zero, so every odd
power sum vanishes identically — `+pcols` skips them), and column count is
genuinely the binding cost. What changed is the price of a column.

**Still open, minor:** `+lat-min` is 16, the measured win. `r = 12` is
untested; lowering it should be measured rather than assumed.
