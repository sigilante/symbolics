#   Symbolic Libraries for Urbit

**Status ~2026.8.2:  Racoon Milestone A and Baloon Milestones A and C are
complete, and both interfaces are frozen.  351 tests green.  Jets are
next.**

![An evocative scene of a mysterious futuristic castle in the style of Flash Gordon](./img/hero.jpeg)

The Urbit symbolics stack covers the mathematics of:

* $ℤ$ represents the set of integers (e.g., $\{-2, -1, 0, 1, 2, ...\}$).
* $ℚ$ denotes the set of rational numbers, which are quotients of integers (fractions like $\frac{1}{2}$ or $-\frac{7}{3}$), including all integers as a subset.
* $𝔽p$ (also written as $Z/pZ$ or $GF(p)$) is a finite field consisting of integers modulo a prime number $p$; it is used in modular arithmetic where addition and multiplication wrap around after reaching $p$. 
* $ℤ/n$ (standardly written as $ℤ/nℤ$ or $ℤ/(n)$) represents the ring of integers modulo $n$, containing $n$ residue classes ${0, 1, ..., n-1}$ where operations are performed by taking the remainder of division by $n$.

Everything here is **exact**.  There is no floating point anywhere in this
repository: Lagoon owns the approximate case, these libraries own the exact
one, and the two are siblings rather than layers.

##  Status

| | Milestone A | Milestone B | Milestone C | Tests |
|---|---|---|---|---:|
| **Racoon** | complete, frozen | deferred | in progress — see below | 239 |
| **Baloon** | complete, frozen | deferred | complete | 112 |

**Milestone A** is the Hoon library as authoritative specification, with
tests, reference vectors, and jet registration hints in place.  **Milestone
B** is native jets; it is deferred until there are more clients, and
everything in A and C was written to be jettable — canonical outputs, pinned
conventions, two-sided crash tables, no `~|`.  **Milestone C** is scope
beyond the first ring.

Both interfaces are frozen.  Baloon's Milestone C landed without moving a
single existing battery axis, because the `+zm` and `+mm` sub-cores were
declared empty from the outset for exactly that purpose.

Racoon's Milestone C is under way rather than done: integer factorization
is built, real-root isolation (§R) and algebraic number arithmetic (§A)
are specified and complete, van Hoeij is specified (§V) with its LLL
phase built, and sparse multivariate remains unspecified.

##  Libraries

### Racoon (Real AlgebraiCs in hOON)

Integers, rationals, and polynomials over ℤ, ℚ, and ℤ/n — number theory,
division, GCD, resultants, and factorization.

- [`racoon/README.md`](./racoon/README.md)
- [`raccoon-spec.md`](./raccoon-spec.md) — normative

The backronym reads "Real AlgebraiCs in hOON" despite the single `c`.  The
spelling is deliberate everywhere except the spec document's filename.

### Baloon (Basic linear ALgebra in hOON)

Exact linear algebra over ℚ, ℤ, and ℤ/n — elimination, determinants,
inverses, kernels, characteristic polynomials, rational eigenvalues, and the
Hermite and Smith normal forms.

- [`baloon/README.md`](./baloon/README.md)
- [`baloon-spec.md`](./baloon-spec.md) — normative

`/lib/baloon` depends on `/lib/racoon` and nothing else, the same
relationship `/lib/lagoon` has to `/lib/math`.

##  Layout

Both projects have the same shape.

```
racoon/
  desk/
    sur/racoon.hoon             shared types
    lib/racoon.hoon             the library -- nz qq zx mx qx
    lib/racoon-vectors.hoon     generated vectors -- never hand-edited
    lib/racoon-fmt.hoon         rendering and parsing
    lib/racoon-rs.hoon          Reed-Solomon codec over F_p
    lib/racoon-fp3.hoon         extension fields F_p[x]/(m)
    lib/racoon-zfac.hoon        integer factorization, totient, order
    lib/racoon-roots.hoon       exact real-root counting and isolation
    lib/racoon-alg.hoon         real algebraic number arithmetic
    tests/lib/racoon.hoon       test suite
    gen/                        dojo generators: bench factor gcd rs fp3
  tools/genvec.py               SymPy vector generator
  scripts/sync.sh               copy desk/ into the pier
  SPEC-QUESTIONS.md             escalation log

baloon/
  desk/
    sur/baloon.hoon             shared types
    lib/baloon.hoon             the library -- qm zm mm
    lib/baloon-vectors.hoon     generated vectors -- never hand-edited
    lib/baloon-fmt.hoon         rendering and parsing, all three rings
    lib/vanhoeij.hoon           LLL lattice reduction -- imports both
    tests/lib/baloon.hoon       test suite
    gen/                        dojo generators: bench det
  tools/genvec.py               SymPy vector generator
  scripts/sync.sh               copy desk/ into the pier
  SPEC-QUESTIONS.md             escalation log
```

The `*-fmt`, `racoon-rs`, `racoon-fp3`, `racoon-zfac`, `racoon-roots`, and
`racoon-alg` libraries are **consumers**: they
import the frozen library like any other caller and are not part of it.  That
is the pattern for anything built on top — a frozen interface reopened for
every good idea was never frozen.

There are no `vere/` directories yet.  The C jets are Milestone B, and will
land there when that milestone opens.

##  Building

Each project syncs into a fake `~zod` and is tested in the dojo.  See either
README for the pinned environment and the full edit–test loop.

```
scripts/sync.sh
|commit %base                          # dojo
-test /=base=/tests/lib/racoon ~       # dojo
```

##  Escalation

`raccoon-spec.md` and `baloon-spec.md` are normative for types, canonical
conventions, crash tables, and public signatures.  Those sections change only
by escalation, recorded in each project's `SPEC-QUESTIONS.md`.  Silence is not
acceptance.
