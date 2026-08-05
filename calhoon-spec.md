# CALHOON — CALculus in hOON

**Engineering Specification v0.1 — the symbolic layer**

Racoon is exact algebra: canonical objects, structural equality, every
arm `free`. Baloon is exact linear algebra on the same terms. Calhoon is
the layer above them where **that discipline stops being available**, and
this document is mostly about what replaces it.

Spelling: **Calhoon**, one `l` and the doubled `oo`, matching Racoon's
single `c` and Baloon's single `l`. The backronym reads "CALculus in
hOON".

Phases are lettered **K0–K6** rather than C0–C6, because `baloon-spec.md`
already uses §C2 and §C3 for its Milestone C sections and two documents
in one repository should not both own §C.

---

## 1. What it is, and why it cannot be part of Racoon

`raccoon-spec.md` §F10 states the reason and this section does not
soften it.

Racoon's design rests on one property: **every product is a unique
mathematical object**. That is what makes `=(a b)` decide equality, what
makes every arm `free` so a jet may use any algorithm, and what makes the
five `pinned` arms a documented exception rather than the rule.

A symbolic expression language cannot have that property. By
**Richardson's theorem**, deciding whether an expression built from the
rationals, `π`, `x`, `exp`, `log`, `sin`, and `abs` is identically zero is
**undecidable**. There is no canonical form to name, no normalization that
terminates on all inputs with a unique answer, and therefore no `=(a b)`
that decides equality.

So Calhoon inverts the project's disposition rather than extending it,
and it does so in a way that would contaminate Racoon if the two shared a
library:

| | Racoon and Baloon | Calhoon |
|---|---|---|
| output | canonical | **normal, not canonical** |
| equality | structural, decides | **semi-decides — see §2** |
| arms | `free`, jets choose freely | **`pinned`, procedure is the contract** |
| a wrong answer | impossible by construction | impossible **by verification** — §7 |

It stands on Racoon the way Baloon does: as a consumer, importing the
frozen interface, adding nothing to it.

## 2. No canonical form, and what is used instead

**A normal form is pinned, and it is not claimed to be canonical.**
`+norm` is deterministic — the same input always produces the same
output — but two expressions denoting the same function may normalize
differently. Every arm producing a general expression is therefore
`pinned`: the procedure is the contract, exactly as it is for `egcd:nz`
and `lll:vh`, except that here it is the rule and not the exception.

**Equality semi-decides, and the signature says so:**

```hoon
++  equiv  |=([a=expr b=expr] ^-((unit ?)))
```

| product | meaning |
|---|---|
| `[~ %.y]` | proven equal |
| `[~ %.n]` | proven unequal |
| `~` | **not decided** — and this is a legitimate answer, not a failure |

**`+equiv` is `pinned`, and this is the subtlest consequence in the
document.** A jet that decided a case the reference left as `~` would be
*mathematically better* and still **wrong**, because Urbit's jet contract
is noun equality and `[~ %.y]` is not `~`. So the boundary of what
Calhoon proves is itself part of the specification. Widening it is a
version change, not an optimization.

**The escape is to decide as much as possible in Racoon.** Equality *is*
decidable on fragments, and Calhoon's normalizer is built to push work
into them:

| fragment | decided by | decidable? |
|---|---|---|
| rational functions of `x` | `racoon-rf`, canonical | **yes** |
| real algebraic numbers | `racoon-alg`, canonical | **yes** |
| rational functions of the kernels (§3) | same, once independence is known | **yes** |
| the general elementary class | — | **no**, Richardson |

That is the design thesis of this whole document: **normalize toward
Racoon, and let the undecidable part be as small as the input allows.**

## 3. Representation — a differential field tower

The naive representation is a syntax tree over `%add`, `%mul`, `%sin`,
and friends, simplified by rewriting. It is what everyone writes first
and it is the wrong one here: rewrite systems on that shape do not
terminate, do not confluence, and make zero-testing hopeless even on
fragments where it is decidable.

Calhoon uses the representation that integration theory already requires:
a **tower of transcendental and algebraic extensions of ℚ(x)**.

```hoon
::    $kern: one generator of the tower, above everything before it
+$  kern
  $%  [%exp e=expr]          ::  e^(that expression)
      [%log e=expr]          ::  log of it
      [%alg p=(list expr) i=@ud]   ::  a root of that polynomial
  ==
::    $expr: a rational function of x and of the kernels below it
+$  expr  [ks=(list kern) f=mpoly-quotient]
```

An expression is a **rational function whose variables are `x` and the
kernels**, with each kernel's argument an expression over the kernels
*before* it. `sin` and `cos` are not primitive: they are
`(e^{ix} ± e^{−ix})` over the complexified base (§8), which is what makes
one algorithm cover trigonometric and exponential inputs instead of two.

**Three things this buys, and they are the reason for the complexity:**

1. **Zero-testing becomes decidable on the transcendental fragment.** By
   the **Risch structure theorem**, one can decide whether a set of
   `exp`/`log` kernels is algebraically independent; when it is, an
   expression is zero exactly when its rational-function representation
   is, which `racoon-rf` decides.
2. **Differentiation is a derivation on a field**, which is mechanical
   and total — §K1 — rather than a case analysis over syntax.
3. **Integration has a decision procedure.** Risch's algorithm is stated
   on exactly this structure and on no other.

**Canonical within, normal without.** For a *fixed* tower with known
independent kernels, the representation is canonical and equality is
structural. What is not canonical is the choice of tower: `log(x²)` and
`2·log(x)` build different towers for the same function. `+norm` pins a
tower-construction procedure; it does not claim it is the only one.

## 4. Dependencies, and the one that does not exist

Calhoon imports `/lib/racoon`, `/lib/racoon-alg`, `/lib/racoon-rf`, and
`/lib/racoon-lt`. It is a consumer of all four and adds nothing to any.

**It also needs multivariate polynomial arithmetic over ℚ, which no
library in this repository has.** §3's representation is a rational
function in `x` *and every kernel* — that is multivariate by
construction, and `%zx`/`%qx` are univariate.

`raccoon-spec.md` §13 lists sparse multivariate as a Milestone C
candidate and it remains unspecified. **It is a hard prerequisite for
Calhoon phase K2 onward**, and it belongs in Racoon rather than here:
multivariate polynomials are canonical objects with `free` arms, which is
Racoon's business and not this document's. Building them inside Calhoon
would put canonical algebra above the layer that gave up canonicality.

Phase K0 and K1 are univariate and can proceed before it; everything
after cannot. **Sequencing conclusion: specify and build Racoon's sparse
multivariate phase before Calhoon K2.**

### 4.1 Baloon interop, precisely

Three algorithms below need to solve linear systems whose entries are
**rational functions, not rationals**: undetermined coefficients in the
heuristic layer (K3), Risch's parametric problems (K4), and Zeilberger's
creative telescoping (K5).

`+qm:baloon` is a core over `$frac`, not a door over a field, so it
cannot be pointed at ℚ(x). There are two ways and this document does not
pick one:

1. **Calhoon does its own elimination** over the tower's field. It has
   division, so this is ordinary Gaussian elimination — perhaps forty
   lines — and it costs nothing outside Calhoon.
2. **Baloon grows a door over a field**, and `+qm` becomes the instance
   at ℚ. That is the better structure and it is a Baloon escalation
   touching a frozen core, which needs a second client to justify.

**Recommendation: (1) until there is a second client, then (2).** This
mirrors how `/lib/racoon-alg` reached van Hoeij — locally first, promoted
when a second caller appeared. Recorded so the decision is not made by
accident.

## 5. Canonical conventions (normative)

| Item | Convention |
|---|---|
| **`pinned` is the default** | Every arm producing an `$expr` is `pinned`. The `free` exceptions are named individually in §6 and are exactly the arms whose product lands in a Racoon-canonical type |
| **Tower construction** | Kernels are added in order of first appearance in a left-to-right, depth-first walk of the input. Deterministic, and stated so that two normalizations of the same input agree |
| **`log` and `exp` are primitive; `sin`, `cos`, `tan` are not** | They are defined over the complexified base as combinations of `exp`. One algorithm then covers both families. `+show` prints trigonometric form back — presentation, not representation |
| **Kernel arguments are normalized first** | A kernel's argument is an expression over the kernels strictly below it, normalized before the kernel is created. Without this the tower is not well-founded |
| **No automatic domain assumptions** | `√(x²)` is not `x`, `log(e^x)` is not `x`, and `x/x` is not `1` without knowing `x ≠ 0`. Assumptions are an explicit argument (§6 `+with`), never inferred. This is where most CAS quietly become wrong |
| **The constant of integration is 0** | As `raccoon-spec.md` §F3 pins it for `+integrate` on `$rfun` |
| **Every heuristic result is verified** | §7. Not a convention so much as the thing the design rests on |

## 6. Public API

| Arm | Signature | `pinned`? |
|---|---|---|
| `parse` `show` | `@t -> (unit expr)` / `expr -> @t` | pinned |
| `norm` | `expr -> expr` | pinned |
| `equiv` | `[expr expr] -> (unit ?)` | pinned — §2 |
| `is-zero` | `expr -> (unit ?)` | pinned |
| `to-rf` | `expr -> (unit rfun)` | **free** — lands in a canonical type |
| `to-alg` | `expr -> (unit anum)` | **free** — same |
| `deriv` | `[expr @tas] -> expr` | pinned |
| `integrate` | `[expr @tas] -> (unit expr)` | pinned. `~` means *no elementary antiderivative was found*; §K4 makes that "does not exist" on the transcendental fragment |
| `defint` | `[expr @tas expr expr] -> (unit expr)` | pinned |
| `series` | `[expr @tas expr @ud] -> (unit expr)` | pinned — truncated, order given |
| `hsum` | `[expr @tas] -> (unit expr)` | pinned — Gosper |
| `laplace` `inverse-laplace` | `[expr @tas] -> (unit expr)` | pinned |
| `fourier` `inverse-fourier` | `[expr @tas] -> (unit expr)` | pinned |
| `with` | `[expr (list assum)] -> expr` | pinned — attach domain assumptions |

`~` is a legitimate product throughout and never means "crashed".

## 7. Correctness does not depend on the heuristics

**This is the load-bearing design decision, and it is `raccoon-spec.md`
§V4 applied to a new problem.**

The integration table, integration by parts, and substitution search are
heuristics. They are tried first because they are fast and because they
produce the forms a human expects. **Every result they return is
confirmed by differentiating it and comparing against the integrand**,
and a candidate that fails the check is discarded, not returned.

So a wrong table entry, a bad substitution, or a by-parts loop that
picks the wrong factor can make `+integrate` **slower**, or make it
return `~` where an answer exists. **None of them can make it wrong.**

Two consequences worth stating:

- The comparison is `+equiv`, which semi-decides — so verification can
  itself return `~`. A candidate whose check is undecided is **rejected**.
  Conservative, and the only safe reading.
- The table needs no proof of correctness to be safe. It needs proof only
  to be *useful*. That is a much cheaper obligation and it is why the
  "standard textbook appendix" of shortcuts can be added incrementally
  without a correctness review each time.

The same discipline covers the transforms: a table-derived Laplace or
Fourier pair is checked by transforming back where an inverse is
available, and reported as `~` when it cannot be.

## 8. Complex numbers, and what they cost

`raccoon-spec.md` §A9 fences complex algebraic numbers out of Racoon, and
§F6 records what that costs: `∫ 1/(x²+1)` is out of range because its
residues are `∓i/2`.

**Calhoon lifts that fence for itself, and only to ℚ(i) and its algebraic
extensions.** `i` is a kernel of kind `%alg` with polynomial `x² + 1`;
nothing in Racoon changes. Two things fall out:

1. **Trigonometric functions become exponentials**, which is what §5's
   convention rests on.
2. **§F6's arctangent case becomes reachable.** The residues are
   rational over ℚ(i), so the logarithmic part is computable there and
   recombined into `arctan` on the way out.

**What it does not buy.** Fourier transforms in the general case need
**distributions** — `δ`, the transform of a constant — and **convergence
conditions**, which are analytic statements and not algebraic ones. Both
are fenced in §11. Calhoon's Fourier is the algebraic fragment: functions
whose transforms exist classically and are expressible in the tower.

## 9. Phases

- **K0 — the tower.** `$expr`, `$kern`, `parse`, `show`, `norm`, `equiv`,
  `to-rf`, `to-alg`, `with`. Univariate; no calculus. The phase where the
  Risch structure theorem's independence check lands, because everything
  after depends on it.
- **K1 — differentiation.** `deriv`, total on the tower. A derivation is
  determined by its action on the generators, so this is short, complete,
  and the verifier every later phase uses.
- **K2 — integration, rational.** Delegates to `integrate:racoon-rf`.
  Already built and already complete; this phase is the bridge, not the
  algorithm. **First phase needing multivariate — see §4.**
- **K3 — integration, heuristics.** The table, integration by parts,
  substitution. Every result verified per §7. This is the phase that
  makes Calhoon *feel* like a CAS, and the one that cannot make it wrong.
- **K4 — integration, Risch.** The transcendental case: a genuine
  decision procedure, so `~` strengthens from "not found" to **"no
  elementary antiderivative exists"**. The algebraic case is fenced —
  §11.
- **K5 — series and hypergeometric summation.** Truncated power series
  over the tower; then **Gosper's algorithm**, which decides indefinite
  hypergeometric summation and rests on exactly the rational-function
  arithmetic §F already provides — the term ratio `t_(n+1)/t_n` is a
  rational function of `n`. Then Zeilberger for the definite case.
- **K6 — transforms.** Laplace and Fourier by table and by the algebraic
  rules, over the complexified tower, verified per §7. `racoon-lt`
  already covers the rational-transform fragment and is the base case.

## 10. Testing

1. **Integration is verified by differentiating the answer**, as
   `raccoon-spec.md` §F9.1 does for rational functions and for the same
   reason: an antiderivative is not unique, so no other program's output
   is an oracle. Here it is stronger than a test — §7 makes it part of
   the algorithm, and the suite asserts that the check is actually
   reached rather than skipped.
2. **Differentiation is verified against the definition on the
   generators** and by the sum, product, quotient, and chain rules on
   random towers. Total, so every input is a test case.
3. **`+equiv`'s three answers each get adversarial cases.** In
   particular: pairs that are equal but that the normalizer cannot
   prove equal, asserted to produce `~`. **A test suite that only used
   decidable pairs would pass with the whole semi-decision collapsed to
   a decision**, which is the failure mode this arm invites.
4. **Falsification is exact, not numerical.** Two expressions are proven
   *unequal* by evaluating both with the kernels replaced by independent
   rational values — valid exactly when the structure theorem has
   confirmed independence, and exact arithmetic throughout. No floating
   point, here as everywhere.
5. **SymPy is an oracle only where the answer is canonical**: `to-rf`,
   `to-alg`, minimal polynomials, and hypergeometric certificates. It is
   **not** an oracle for antiderivatives or for simplified forms, and
   §11.3's rule applies — confirm the convention before pinning against
   the tool.
6. **Benchmarks.** `integrate` on the table cases, on Risch cases, and on
   the rational fragment, through `scripts/bench.sh`. Recorded, no gates.

## 11. Out of scope — hard fence

**Risch's algebraic case.** The transcendental case is K4; integrating
over algebraic extensions needs Trager–Bronstein and function-field
machinery well beyond what this document specifies. Every real CAS
treats it as a separate project and so does this one.

**Distributions.** No `δ`, no principal values, no tempered
distributions — so no Fourier transform of a constant, a polynomial, or a
periodic function. §8 says why: they are analytic objects and this is an
algebraic layer.

**Convergence and analytic conditions.** No claim about where a transform
or a series converges; no asymptotic analysis; no branch-cut tracking
beyond the domain assumptions a caller supplies explicitly under §5.

**Limits.** Not specified. They want either series with error control or
a Gruntz-style algorithm, and both are their own phase.

**Differential equations beyond `racoon-lt`'s constant-coefficient
case.** No variable coefficients, no systems, no PDEs.

**Multivariate calculus.** No partial derivatives beyond the single
`@tas` argument, no gradients, no multiple integrals, no vector calculus.
`+deriv` takes a variable name because the tower is multivariate; the
*calculus* here is univariate.

**No floating point.** Unchanged from every other document in this
repository: Lagoon owns the approximate case.

**No assumption inference.** §5 makes this a convention; it is repeated
here as a fence because it is the single most common way a CAS becomes
quietly wrong, and because "just simplify √(x²) to x" will be proposed.

## 12. Open questions for the first escalation round

1. **Does sparse multivariate go in Racoon, and under which milestone?**
   §4 argues yes and that it blocks K2. It needs a Racoon spec section
   before Calhoon can proceed past K1.
2. **Does Baloon grow a door over a field?** §4.1 recommends deferring
   until a second client exists. If K3, K4, and K5 each want it, that is
   arguably three clients inside one library and the answer changes.
3. **How much does `+equiv` promise?** §2 makes the boundary part of the
   contract. The first version should promise *less* than it can prove,
   since widening is a version change and narrowing is a bug.
4. **Is `%alg` in the tower, or does it delegate to `racoon-alg`?** The
   latter is cleaner and only covers *real* algebraic numbers; §8 needs
   ℚ(i), which `racoon-alg` fences out. Probably both, with `%alg`
   carrying the general case and `to-alg` bridging to the real one.
