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
is built; real-root isolation (§R), algebraic number arithmetic (§A), and
van Hoeij recombination (§V) are specified and complete; **the rational
function field (§F) is specified and not yet built**; and sparse
multivariate remains unspecified.

§F is where the stack turns into a calculus engine — rational functions,
partial fractions, integration by Hermite reduction and Rothstein–Trager,
and the Laplace transform — and it needs no primitive that does not
already exist. §F10 records why the *symbolic* half cannot follow it into
Racoon: Richardson's theorem makes canonical form undecidable for
elementary expressions, and canonical outputs are what this library is.

That symbolic half is **Calhoon**, specified in `calhoon-spec.md` and not
yet built.

##  Cascabel

`cascabel/` is an example application: a `/lib/shoe` agent that answers the
`%eval-command` poke, so [caderno](https://github.com/sigilante/caderno) can
drive it as a notebook kernel. It is stateless — every command is answered
from its own text — and reaches both libraries through symlinks.

- [`cascabel/README.md`](./cascabel/README.md)

##  Nockapp

`nockapp/` is a second example, and a different kind: **Tip5 as an
independent witness**. Tip5 is the algebraic sponge hash Nockchain uses,
and it already has an authoritative Hoon implementation with a Rust jet —
but those two share a lineage, so their agreeing mostly confirms that one
reading of the paper was transcribed consistently. `/lib/tip5` is built
from Racoon's modular arithmetic and Baloon's matrices instead, and agrees
with 300 of Nockchain's own published vectors for a different reason.

It has already earned its keep: **"Tip5 with 5 rounds" names two different
functions in nockchain-official**, and a round count alone does not say
which one you get.

- [`nockapp/README.md`](./nockapp/README.md)

##  Calhoon

`calhoon-spec.md` specifies the symbolic layer — expression trees,
differentiation, integration by parts and the textbook table, Risch,
hypergeometric summation, and the Laplace and Fourier transforms.
**Specified, not built.**

It is a sibling rather than a Racoon phase, and §1 of that document says
why: Racoon rests on canonical outputs and structural equality, and by
Richardson's theorem an elementary expression language cannot have
either. Calhoon's arms are `pinned` where Racoon's are `free`, its
equality *semi*-decides, and its heuristics are made safe by verifying
every answer rather than by being correct — the same discipline §V4 uses
for the van Hoeij lattice.

Two things block it, both recorded in `calhoon-spec.md` §4 and §12:
**sparse multivariate polynomials do not exist in Racoon** and are a hard
prerequisite from phase K2 on, and linear algebra over ℚ(x) needs either
a local elimination or a Baloon door over a field.

- [`calhoon-spec.md`](./calhoon-spec.md) — normative

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
    tests/lib/                  test suites, one per library:
                                racoon racoon-fmt racoon-rs racoon-fp3
                                racoon-zfac racoon-roots racoon-alg
    gen/                        dojo generators: bench factor gcd rs fp3
                                zfac roots alg
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
    tests/lib/                  test suites: baloon vanhoeij
    gen/                        dojo generators: bench det lll
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

##  Testing

`scripts/test.sh` runs every suite headlessly and exits nonzero on failure,
which is what makes it usable from a hook or a CI job:

```
racoon/scripts/sync.sh && baloon/scripts/sync.sh
|commit %base                          # dojo
scripts/test.sh                        # pass / FAIL, exit 0 / 1
```

`cascabel/` has no test suite and is not run by `scripts/test.sh` or by CI.
It is an example application, and the libraries it calls are covered by their
own suites.

It drives a **running** fake ship through [`click`][click], which sends a
`%fyrd` card to `conn.c` — urbit/urbit's own CI mechanism, from
`nix/test-fake-ship.nix`. The `%test` thread returns a loobean, so the exit
code is exact rather than inferred; per-arm lines are `%slog` and appear in
the ship's output.

[click]: https://github.com/urbit/tools/tree/master/pkg/click

This replaced scraping the tmux pane, which was a real source of error and
not merely inconvenience: timing skew between a commit and the command
after it, and `OK` lines swallowed by terminal redraws — which undercounted
this project's test totals for several commits before it was noticed.

`scripts/nc-unix` is a stand-in for `nc -U -W 1`. click shells out to
netcat, and macOS ships a BSD netcat with `-U` but no `-W`.

Both directions are verified: a deliberately failing arm was added, the
runner reported `FAIL` and exit 1, and reverting restored `pass` and exit
0. An untested failure path in a test gate is worse than no gate.

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
