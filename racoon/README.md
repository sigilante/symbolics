# Racoon — Real AlgebraiCs in hOON

A deterministic computer algebra kernel for Urbit: exact arithmetic over ℤ, ℚ,
and ℤ/n, and univariate polynomial arithmetic, division, GCD, resultants, and
factorization over 𝔽p and ℤ. Sibling to [`urbit/numerics`][numerics].

The Hoon library **is** the specification. `SPEC.md` (`../raccoon-spec.md`) is
normative; `SPEC-QUESTIONS.md` is the escalation log. Milestone A delivers the
Hoon library with tests, reference vectors, and jet-registration hints in
place. Native jets are Milestone B.

Note on spelling: the library is `racoon` with one `c` in every path, import,
and file name. Only the spec document spells it `raccoon`.

## Status

| Phase | Contents | State |
|---|---|---|
| **P0** | `nz`, `qq` — integers, number theory, rational scalars | complete |
| P1 | `zx`/`mx` polynomial arithmetic | not started |
| P2 | division, GCD, resultants | not started |
| P3 | factorization | not started |

## Layout

```
racoon/
  desk/
    sur/racoon.hoon           shared types
    lib/racoon.hoon           the library
    lib/racoon-vectors.hoon   generated vectors -- never hand-edited
    tests/lib/racoon.hoon     test suite
    gen/racoon-bench.hoon     benchmark generator
  tools/genvec.py             SymPy vector generator
  tools/requirements.txt      pinned SymPy version
  scripts/sync.sh             copy desk/ into the pier
  README.md                   this file
  SPEC-QUESTIONS.md           escalation log
```

## Pinned environment

| | |
|---|---|
| Vere | **4.6** (`~/urbit/ships/emissary-dev/urbit`) |
| Pier | fake `~zod` at `~/urbit/ships/emissary-dev/zod` |
| Kernel | `%zuse` **409** |
| Python | 3.12.7 |
| SymPy | 1.13.2 (`tools/requirements.txt`) |

Do not chase newer kelvins mid-milestone.

## Edit–test loop

Once, in the dojo:

```
|mount %base
```

Then, per iteration:

```
scripts/sync.sh                       # host
|commit %base                         # dojo
-test /=base=/tests/lib/racoon ~      # dojo
```

`sync.sh` copies only the five files this project owns; it never boots or
commits, because conflating the copy with the commit makes a failed build hard
to attribute. Override the pier with `RACOON_PIER=/path/to/zod`.

For interactive work:

```
=r -build-file /=base=/lib/racoon/hoon
(egcd:nz:r 240 46)
```

Building the library slogs `fund: in racoon, parent ... not found at 7`. This
is expected: no jets exist until Milestone B, so the runtime has nothing to
resolve the `%racoon` core's parent against.

## Reference vectors

`desk/lib/racoon-vectors.hoon` is generated and **never hand-edited**:

```
pip install -r tools/requirements.txt
python3 tools/genvec.py > desk/lib/racoon-vectors.hoon
```

Deterministic: the PRNG seed is pinned in the script, so regeneration is
byte-identical. 14 families, 44–56 cases each, against the §11.2 minimum of 40.

Oracles are independent implementations — `math.gcd`, `math.isqrt`,
`sympy.isprime`, `sympy.ntheory.modular.crt`, `fractions.Fraction`. For the two
arms where §9 pins the *algorithm* rather than the value (`egcd`, `ratrec`),
the pinned algorithm is transcribed in Python and cross-checked against an
independent invariant — the Bézout identity against `math.gcd`, and the
congruence `q*u ≡ p (mod m)`. That keeps the vectors a check on the Hoon
transcription rather than a copy of it.

This is not ceremony. A hand-written `isqrt` expectation in the first draft of
the test suite was wrong (`isqrt(4.294.836.224)` is 65.534, not 65.535); the
generated vectors exist so that hand-arithmetic never gates a phase again.

## Benchmarks

```
+racoon-bench
```

Each row wraps a fold over a precomputed input list in `~>(%bout ...)`, which
slogs `took ...` and returns the accumulator. Inputs are built outside the
timed region so list construction is not charged to the arm; returning the
accumulator keeps the work from being elided.

**There are no performance gates in Milestone A.** These numbers are the
denominator for Milestone B speedup claims.

### Recorded baselines

Vere 4.6, `%zuse` 409, fake `~zod`, `--loom 33`, Darwin arm64. 100 iterations
per row unless noted. Per-call figures are derived, not measured directly.

| Arm | Input | Total | Per call |
|---|---|---:|---:|
| `gcd:nz` | 60-bit × 50-bit | 1.157 ms | ~11.6 µs |
| `egcd:nz` | 60-bit × 50-bit | 36.217 ms | ~362 µs |
| `isqrt:nz` | 64-bit | 608 µs | ~6.1 µs |
| `is-prime:nz` | ~20-bit | 3.079 ms | ~30.8 µs |
| `is-prime:nz` | 61-bit primes (10 iter) | 11.420 ms | ~1.14 ms |
| `crt:nz` | four coprime moduli | 15.873 ms | ~158.7 µs |
| `ratrec:nz` | 20-bit modulus | 4.540 ms | ~45.4 µs |
| `add:qq` | | 1.359 ms | ~13.6 µs |
| `mul:qq` | | 1.045 ms | ~10.5 µs |
| `div:qq` | | 1.476 ms | ~14.8 µs |
| `cmp:qq` | | 529 µs | ~5.3 µs |

Two observations worth carrying into Milestone B:

- **`egcd` costs ~31× `gcd`** on identical inputs. Both run the same division
  sequence; the difference is the signed cofactor bookkeeping through `++si`,
  which allocates on every step. That ratio is the single most interesting
  number in this table, and `egcd` is a `pinned` arm, so a jet must reproduce
  the cofactors exactly rather than route around them.
- **The `is-prime` rows differ by 37×** between 20-bit and 61-bit inputs, but
  the 61-bit row deliberately feeds *primes*. A random 61-bit odd number is
  almost always rejected by trial division against the witness schedule, so
  sampling the range measures early exit, not Miller–Rabin. An earlier draft of
  this table did exactly that and reported the 61-bit case as *faster* than the
  20-bit one.

The §11.4 polynomial rows — `mul`/`gcd` over a 61-bit 𝔽p at degrees 16/64/256,
`gcd:zx` at degree 64, `factor:zx` at degree 32 — require arms that do not
exist until Phases 1–3. `+polynomial-rows` in the generator is where they land
and is deliberately empty rather than faked.

## Testing

```
-test /=base=/tests/lib/racoon ~
```

49 arms, all green. Three kinds:

- **Behavioral** — known values and adversarial families. `is-prime` gets eight
  Carmichael numbers and five strong pseudoprimes rather than random odds,
  since a Fermat test passes every Carmichael and random odds are almost all
  trivially composite.
- **Crash rows** — every §8 row naming a Phase 0 arm has a dedicated
  `++test-p0-crash-*`, and matching `++test-p0-nocrash-*` arms pin the edges
  that must *not* crash. §8 is a two-sided contract; both halves are jettable.
- **Vector-driven** — one `++test-p0-vec-*` per generated family. Each reports
  *every* mismatching case rather than stopping at the first.

Property tests use `++og` from seeds pinned in the `%seeds` section of the test
file.

## Decision log

| # | Decision | Rationale |
|---|---|---|
| Q1 | Add `+$ ord ?(%lt %gt %eq)` to `sur` | §7 pins `+pcmp`'s product as `?(%lt %eq %gt)` but §6 names no type for it, and `hoon.hoon` has none to borrow — `++cmp:si` produces an `@s` in `{-1, --0, --1}`. Member order is deliberate: Hoon's fork bunt does not follow declaration order, and `?(%lt %gt %eq)` bunts to `%eq`. Do not reorder. |
| Q2 | `+cmp:qq` produces `$ord` | Same three-valued result as `+pcmp`; `+pcmp` on `qol` delegates to it rather than reimplementing the cross-multiplication. |
| Q3 | Add a §8 crash row: `+new:qq` on `q = 0` | No product respects the `$frac` invariant — `gcd(|p|, 0) = |p|` reduces to `q' = 0` — and R5 forbids downstream arms from re-canonicalizing, so a bad value would propagate silently. |
| Q4 | Jet registration follows `/lib/math.hoon`, not §10's prose | §10 demands mirroring that file "exactly" while also describing "nested `~%` per sub-core"; the file and Lagoon both use one root `~%` under `%non` and plain `~/` below. Followed the file, per §10's operative instruction. |
| — | Private helpers live in `+pv`, outside the `%racoon` core | Helper churn cannot disturb the battery layout of a hinted core when the R6 freeze lands, and `=<` keeps them genuinely private. |
| — | `sync.sh` copies an explicit file list, not a blanket `rsync` | `%base` carries the kernel; being explicit means a stray file here can never shadow a `sys/` file there. |

[numerics]: https://github.com/urbit/numerics
