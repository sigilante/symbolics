# SPEC-QUESTIONS — escalation log

Per SPEC §14. Each entry states the question, the pinned material it touches,
and a proposed resolution. Unanswered entries block their phase gate.

---

## Q1 — comparison product type is used but not declared (§6, §7)

**Status:** RESOLVED ~2026.8.1 — approved as proposed, applied to
`desk/sur/racoon.hoon`. §6's type block is amended to include `$ord`.

§7 pins `+pcmp`'s product type as `?(%lt %eq %gt)`, but the §6 `sur` block
declares no name for it. `hoon.hoon` has no such type: `++cmp:si` produces an
`@s` in `{-1, --0, --1}`, and `++aor`/`++dor` produce a `?`. Left as-is, the
literal `?(%lt %eq %gt)` is repeated in three `+pcmp` casts and in every
sorting helper.

**Proposed resolution:** add to `sur/racoon.hoon`:

```hoon
::    $ord:  result of a total-order comparison
+$  ord  ?(%lt %eq %gt)
```

This names an existing pinned type; it adds no new representation and changes
no arm signature. Not applied pending approval — §6 is pinned and silence is
not acceptance. Until then `/lib/racoon` will spell the union out inline.

---

## Q2 — `+cmp:qq` product type (§9 Phase 0)

**Status:** RESOLVED ~2026.8.1 — approved. `cmp:qq` produces `$ord`, and
`+pcmp` on `qol` delegates to it.

§9 lists `cmp` among the `qq` arms on `frac` but gives no product type. §7
defines `+pcmp` on `frac` coefficients by comparing `p1*q2` vs `p2*q1` via
`++cmp:si`, which implies the same three-valued result.

**Proposed resolution:** `cmp:qq` produces the same type as `+pcmp`
(`$ord` if Q1 is approved, else `?(%lt %eq %gt)`), and `+pcmp` on `qol`
delegates to it rather than reimplementing the cross-multiplication.

---

## Q3 — `+new:qq` with `q = 0` is not in the crash table (§8)

**Status:** RESOLVED ~2026.8.1 — approved. §8 gains the row `+new` (`qq`),
`q = 0`, crash; implemented as `?<  =(0 q)`.

§8 gives `+div` and `+inv` (`qq`) a crash on a zero divisor/operand, but says
nothing about the constructor `+new` receiving `q = 0`. There is no
non-crashing answer that respects the `$frac` invariant: `gcd(|p|, 0) = |p|`,
so reducing yields `q' = 0` and a value outside the type. Letting it through
would put a non-canonical `$frac` into circulation, which R5 then propagates
silently through every downstream arm.

**Proposed resolution:** add a §8 row — `+new` (`qq`), `q = 0`, crash. This is
implemented now as `?<  =(0 q)`, because shipping the alternative (a
type-violating product) is worse than shipping a flagged deviation. Revert if
rejected.

---

## Q4 — §10 says nested `~%`, the file it says to copy uses `~/`

**Status:** RESOLVED ~2026.8.1 — approved; follow the file, not the prose.

§10 requires registration that "mirrors `/lib/math.hoon` **exactly**", and
also describes "nested `~%` per sub-core". Those conflict:
`libmath/desk/lib/math.hoon` uses a single root `~%  %non  ..part  ~` and then
plain `~/  %name` on every nested core (`~/  %math`, `~/  %rs`, ...). Lagoon
does the same.

**Resolution taken:** followed the file, per §10's operative instruction —
root `~%  %non  ..part  ~`, then `~/  %racoon`, `~/  %nz`, `~/  %qq`. Flagging
in case the prose was the intent and the precedent is the accident.

Building the library prints `fund: in racoon, parent 4bc26355 not found at 7`.
This is expected and not a defect: no jets exist until Milestone B, so the
runtime has nothing to resolve the `%racoon` core's parent against. Confirmed
normal by the reviewer ~2026.8.1; do not chase it.

---

## Q5 — R6's freeze is not achievable for `%racoon` one phase at a time

**Status:** resolved — the proposed resolution below was adopted. All five
sub-core arms are declared in §6's order and the `%racoon` battery is fixed
for the milestone; Baloon applied the same pattern up front for `+zm` and
`+mm`. **Blocks:** nothing.

R6 freezes a hinted core's arm set and order once its phase gate closes. That
works for `%nz` and `%qq`, which are complete. It cannot work for `%racoon`
itself: adding an arm to a Hoon core changes the battery axes of the arms
already in it, so introducing `+zx`, `+mx`, and `+qx` as their phases land
would move the `%racoon` battery at every gate — and `%racoon` is the parent
axis each sub-core jet resolves against. Freezing `%nz` internally while the
axis at which `%nz` itself lives keeps moving buys nothing for a jet author.

Milestone A has no jets, so nothing is broken today. But §10 is titled
jet-readiness, and this is the obligation it exists to create.

**Proposed resolution (implemented):** declare all five sub-core arms now, in
§6's order — `nz`, `qq` under `+|  %scalars`; `zx`, `mx`, `qx` under
`+|  %polynomials` — with the three unbuilt cores empty. The `%racoon` battery
is then fixed for the milestone, and each sub-core's own layout freezes at its
own gate. Cost is nine lines of empty core; `+|` chapters are included because
they also partition the battery.

The alternative reading — that R6 binds only sub-cores, and `%racoon` is
expected to churn until P3 closes — is defensible and costs nothing now.
Say so and I will revert the reservation.

---

## Notes (delegated, recorded not escalated)

- **Spelling.** §3 spells every path `raccoon`; the repository directory and
  file names are `racoon` (single `c`), intentionally. Paths in this repo are
  `racoon/desk/sur/racoon.hoon` etc., and the library is imported as
  `/-  *racoon`. The prose name remains "Raccoon". §3 is outside the pinned
  §6–§10 range, so this is recorded here rather than escalated.
- **Toolchain.** §4.1's pinned environment is Vere **4.6** (the binary at
  `~/urbit/ships/emissary-dev/urbit`), fake `~zod` pier in that same
  directory, `%base` kelvin `[%zuse 409]`. `sur/racoon.hoon` builds clean
  there. `~nec` in the same directory is a live ship and is off limits.
- **`$ord` member order.** Hoon's fork bunt does not follow declaration
  order: `*?(%lt %eq %gt)` is `%gt`, whereas `*?(%lt %gt %eq)` is `%eq`.
  `$ord` is declared in the latter order so that a bunted comparison reads
  as "equal" rather than "greater than". Do not reorder the members.

---

## R1 — should `+deriv` be public on `%zx`? (RESOLVED — promoted)

**Status:** resolved. `+deriv` is public on `%zx`, delegating to
`+zderiv:pv`, and `/lib/racoon-roots` calls it instead of carrying its own.
The revisit condition below fired exactly as written: phase V1 opened `%zx`
for a batch — `+zmod` and `+hdata`, plus six promotions out of the
delegated set — so the battery axes moved regardless, and Milestone B has
still not opened, which is the only window in which that is free.

The `+tderiv` copies in `tests/lib/racoon-rs` and `tests/lib/racoon-zfac`
were deliberately **not** removed. A squarefreeness check that borrowed the
library's own derivative would be checking less than it appears to; those
duplicates are test independence, not accident.

The formal derivative is `+zderiv` in `+pv`, private. `/lib/racoon-roots`
needs it for the Sturm chain and, being a consumer, cannot reach it — so it
recomputes it in four lines.

**Recommendation: leave it private for now, and duplicate.** Promoting it
means adding an arm to `%zx`, which moves the battery axes of every arm
frozen at the P2 gate — the ones Milestone B jets resolve against. Four
lines of duplication is a smaller harm than reopening a frozen core for a
convenience, and the derivative is cheap enough that no jet would want it
anyway.

**Revisit if** a Milestone C escalation opens `%zx` for a batch of changes.
`deriv` is genuinely public-shaped — it is a total, canonical, ordinary
operation on `zol` — and if that core is being reordered regardless, it
should go in then. Not for this alone.

## R2 — `$ivl` and `$rrt` are declared in the consumer, not `sur` (RESOLVED)

Recorded so it is not relitigated. §6 is pinned, and `/lib/racoon-roots` is
a consumer; declaring its two result types locally costs nothing and needs
no escalation. `$ord` is reused from §6 unchanged for sign tests, which is
what that type is for. Types carry no battery-axis consequence, so this can
be revisited freely if the shapes ever need to be shared.

## R3 — §R3's "divided out" clause was wrong (CORRECTED)

**Status:** corrected in `raccoon-spec.md` §R3 while building phase R2.
Recorded because it changes pinned material, and because the reasoning is
not obvious from the outside.

§R3 originally said rational roots are "divided out before any
subdivision happens." Building it showed that breaks the **pairwise
disjointness** the same section requires.

Dividing them out leaves `q` with only irrational roots, and the
subdivision then isolates those. But a node isolating an irrational root
of `q` can still *contain* a rational root of `p` — they were removed from
`q`, not from the number line. That node and the degenerate interval for
the rational root then overlap, and the reported intervals are no longer
disjoint. Concretely, `(x - 1)(x^2 - 2)` has `B = 3` for the reduced
`x^2 - 2`, and the node isolating `sqrt 2` can be a range whose closure
holds the rational root 1.

**The fix:** subdivide the whole squarefree part, so every node counts
*every* distinct real root, and collapse a node whose single root is
rational to that exact point. The point replaces the node it sat in, so
it cannot overlap a sibling, and the canonical-interval definition is
unchanged — still the shallowest node holding exactly one root.

No arm signature changed and the products are the same shape; only the
route to them, and the guarantee, differ.

## R4 — is van Hoeij a hard dependency of phase A? (RESOLVED)

**Status: resolved, and answered by measurement rather than by the
argument below.** Both phases of §V are built, `/lib/racoon-alg` calls
van Hoeij through `+facz`, and the answer to the title question turned
out to be **no** — see the closing section. The original entry is kept
because its *placement* conclusion was right and is what got built.

The LLL fence in §13 of both specs **has since been lifted**
(`raccoon-spec.md` §V, `baloon-spec.md` §13) and
`baloon/desk/lib/vanhoeij.hoon` provides both `+lll` and `+factor`.

**Resolved:** LLL does **not** go in Racoon. Racoon cannot import Baloon,
so putting it there would mean duplicating integer matrices, `det`, and
the Hermite form that Baloon Milestone C already provides. Instead van
Hoeij lives in a consumer library importing both — the same shape every
other capability here has taken. Racoon stays the lower layer and gains
nothing it does not need.

§A8 works it out: `deg(α·β) <= deg α · deg β`, so two degree-4 algebraic
numbers give a resultant of degree 16, and extracting the minimal
polynomial means factoring it. §9 already fences `SD_4` and beyond out of
scope pending van Hoeij — and `SD_4` is degree 16. The two limits are the
same limit.

**Recommendation: build phase A anyway, and let it hit the cliff.**
Degrees 2 and 3 cover every quadratic and cubic irrational, which is the
overwhelming majority of what anyone computes with, and they are entirely
unaffected. Deferring the whole capability for a case it does not yet
need would be the wrong trade.

**What that requires of the implementation:** the factorization step must
be a single call, so that van Hoeij drops in without restructuring A2.
`+factor:zx` is already marked `free` in §9 with the note that jets may
use van Hoeij or anything else, so the interface is right; this is about
keeping the *consumer* equally replaceable.

**The escalation, since made and accepted**, was §13's LLL fence, which both
this spec and `baloon-spec.md` stated. Note the substrate now partly exists:
Baloon Milestone C provides integer matrices with `det`, `mul`, and
Hermite and Smith normal forms, which is what LLL operates on. But
`/lib/baloon` depends on `/lib/racoon`, so Racoon cannot import it —
either LLL lives in Racoon, duplicating matrix machinery, or van Hoeij
lives in a consumer that imports both. **That choice should be made
before any LLL code is written, not after.**

### Closed by measurement

**The title question's answer is no.** Van Hoeij is not a dependency of
phase A at degree 4 — it is a dependency at degree 32, which is a
different rung than §A8 identified, and A2 was never blocked at all.

Measured with `/gen/racoon-alg-bench`, timing the sum of two algebraic
numbers, before and after the swap:

| the sum | degrees | `factor:zx` | van Hoeij |
|---|---:|---:|---:|
| `(√2+√3) + (√5+√7)` → `SD_4` | 4 + 4 | 3.34 s | 3.34 s |
| `(√2+√3+√5+√7) + √11` → `SD_5` | 16 + 2 | 281.9 s | **90.4 s** |

The first row is the case §A8 is about, and the factorization is 0.3 s of
it. The rest is the **bivariate resultant** — `deg p · deg q + 1`
univariate resultants and an interpolation over ℚ — which van Hoeij does
not touch and which nothing in §V was ever going to help. The two limits
were not the same limit; they only looked alike because both are indexed
by degree 16.

This is §V0's lesson landing a second time, and by the same mechanism: a
cost was attributed from theory, the theory named the exponential step
because that is the step theory notices, and the measurement found the
cost somewhere else entirely. §11.3 says confirm a convention before
pinning it; this says confirm a bottleneck before designing around it.

**What changed in the code.** `/lib/racoon-alg` gained `+facz`, which is
`factor:zx`'s pipeline — Yun's squarefree decomposition, then
recombination per part — with `factor:vh` in place of `firr:zx`. `+make`
calls it, and `+make` is the only factorization site in the library,
which is what §A8 asked A2 to guarantee. Below `lat-min = 16` modular
factors `factor:vh` degenerates to `firr:zx` exactly, so the swap cannot
be the slower choice; the first row above is that degeneracy, measured.

**The dependency, stated plainly.** `/lib/racoon-alg` now imports
`/lib/vanhoeij`, which imports Baloon. So one file in `racoon/desk`
requires Baloon on the desk to build. `/lib/racoon` is untouched and
still depends on nothing, and no frozen core moved — this is a consumer
importing a consumer, which is the shape R4 chose in the first place. The
alternative considered was promoting `+bires` and the root-selection loop
to racoon-alg's public API and building a second `add`/`mul`/`div` next
to `/lib/vanhoeij`; it keeps Racoon's desk self-contained at the cost of
duplicating the arithmetic, and was rejected as the worse trade.

**Left open.** The bivariate resultant is now ~90% of the degree-32 sum
and 100% of the degree-16 one. Evaluation–interpolation was chosen in §A3
because it needs only frozen arms, not because it is fast, and it is
where any further work on phase A belongs.
