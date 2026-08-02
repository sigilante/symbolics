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
