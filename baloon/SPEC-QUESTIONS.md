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

## V1 — the lattice pass does not beat Zassenhaus (OPEN, not blocking)

**Status:** open, and recorded rather than worked around. Phase V1 is
built and correct; it is not yet faster. **Blocks:** nothing — `+factor:vh`
agrees with `+firr:zx` on every input, so this is a performance question
only.

Measured both ways, same inputs, same machine:

| | Zassenhaus | van Hoeij |
|---|---:|---:|
| `SD_3` | 21.3 ms | 99.4 ms |
| `SD_4` | 282.3 ms | 2161.3 ms |
| `SD_5` | 197.9 s | 239.2 s |

`raccoon-spec.md` §V0 named `SD_5` as the number to beat. It is not beaten.

**The pass is not broken.** On every reducible input tested it proposes
exactly the true factor indicators, immediately and with no enumeration —
`(x−1)(x−2)(x−3)` gives `{0},{1},{2}`, `x^6−1` gives all four singletons,
and irreducible `SD_2` correctly gives only `{0,1}`. Those are pinned in
`++test-v1-lattice-proposes`.

**The problem is which inputs are slow.** Zassenhaus is fast on reducible
polynomials — it finds each factor at low cardinality. It is slow only on
the irreducible-but-totally-split family, where every proper subset must
be rejected. That is exactly where the lattice fails: on `SD_3` the
subsets `{1,2}` and `{0,3}` satisfy the trace conditions *honestly*, being
factorizations over a subfield rather than over ℚ, and no number of
correct trace conditions of the kind used here excludes them — only trial
division does. So the lattice proposes, `+cand` rejects, and `+zass` runs
the full enumeration anyway, having charged for the reduction first.

Two things were tried and are recorded so they are not retried blindly:

- **`s_1` alone is useless on this family.** A Swinnerton–Dyer polynomial
  is even, so every modular factor's roots sum to zero and every odd power
  sum vanishes identically. `+pcols` now skips dead columns.
- **More columns cost more than they save.** LLL's cost tracks big-entry
  columns rather than dimension: `r=16, m=4` costs 221.7 s against
  `r=32, m=1` at 49.1 s. Going from two live columns to four would exceed
  the enumeration being replaced.

**What would actually resolve it**, in rough order of expected value:

1. **A cheaper LLL.** The three `+gso` removals bought 91× at dimension 9;
   an integer-preserving reduction (de Weger / Kannan–Bachem) removes the
   `$frac` gcd traffic structurally rather than merely reducing it. If
   columns were cheap enough, four or six of them would separate.
2. **Milestone B jets on `%qq`.** The inner loop is bigint rational
   arithmetic, which is what jets accelerate.
3. **The real van Hoeij column strategy** — iterating, adding columns only
   when the previous round failed to separate, rather than fixing the count
   up front.

Until one of those lands, `+lat-min` is 32: at `r = 32` Zassenhaus
enumerates ~2.1e9 subsets and does not finish, so the lattice cannot make
things worse and on a reducible input makes them possible.
