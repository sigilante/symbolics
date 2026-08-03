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
| **P0** | `nz`, `qq` — integers, number theory, rational scalars | **complete, frozen** |
| **P1** | `zx` — ℤ[x] arithmetic | **complete, frozen** |
| **P1** | `mx` — (ℤ/n)[x] arithmetic and ℤ/n scalars | **complete, frozen** |
| **P2** | division, GCD, resultants; `qx` | **complete, frozen** |
| **P3** | factorization; `SD_3` passes | **complete, frozen** |

**Milestone A is complete and the interface is frozen.** All six hinted
cores — `%racoon`, `%nz`, `%qq`, `%zx`, `%mx`, `%qx` — have their arm sets and
order fixed under R6: no reordering, renaming, or insertion without
escalation. `%racoon` itself is frozen at five arms; see Q5 in the decision
log for why that had to happen up front rather than phase by phase.

This is the contract Milestone B jets are written against.

**Milestone B is deferred** until there are more clients. There are now
three — `racoon-fmt`, `racoon-rs`, and `racoon-fp3` — plus Baloon, which
depends on Racoon and nothing else. Everything in Milestone A was written to
be jettable: canonical outputs, five pinned algorithms where the output was
underdetermined, two-sided crash tables, and no `~|` anywhere.

**Milestone C has not started.** The candidates, in §13 of the spec:

| Candidate | Note |
|---|---|
| ~~Integer factorization~~ | **Built**, as `/lib/racoon-zfac` — see below. It did not need `nz` reopened |
| Real-root isolation, Sturm/Descartes | The *Real* in Real AlgebraiCs, which the library does not yet deliver. Builds on frozen `zx`/`qx` — `gcd`, `deriv`, and `res` are all in place. Listed as a candidate, not a design; it wants a spec section before code |
| van Hoeij recombination | Would attack the known cost cliff — Zassenhaus is exponential in the worst case, and `SD_4`+ is out of scope until this lands. Needs LLL, which both specs fence out, so it requires escalation first |
| Sparse multivariate | The largest and least specified |

## Layout

```
racoon/
  desk/
    sur/racoon.hoon           shared types
    lib/racoon.hoon           the library
    lib/racoon-vectors.hoon   generated vectors -- never hand-edited
    tests/lib/racoon.hoon     test suite
    lib/racoon-fmt.hoon       rendering and parsing
    lib/racoon-rs.hoon        Reed-Solomon codec over F_p
    lib/racoon-fp3.hoon       extension fields F_p[x]/(m)
    lib/racoon-zfac.hoon      integer factorization and its consequences
    gen/racoon-bench.hoon     benchmark generator
    gen/racoon-factor.hoon    factor a polynomial from the dojo
    gen/racoon-gcd.hoon       gcd of two polynomials from the dojo
    gen/racoon-rs.hoon        Reed-Solomon round-trip demonstration
    gen/racoon-fp3.hoon       Goldilocks extension field demonstration
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

For interactive work there is a human-readable surface — `/lib/racoon-fmt`
renders and parses conventional notation, so nothing has to be read as a
little-endian ZigZag list:

```
+racoon-factor 'x^4 - 1'
"x^4 - 1  =  (x - 1) * (x + 1) * (x^2 + 1)"

+racoon-factor 'x^2 - 1', =p 7
"x^2 + 6  =  (x + 1) * (x + 6)   (mod 7)"

+racoon-gcd 'x^4 - 1' 'x^2 - 1'
"gcd(x^4 - 1, x^2 - 1)  =  x^2 - 1"
```

Or against the library directly:

```
=r -build-file /=base=/lib/racoon/hoon
(egcd:nz:r 240 46)
```

`racoon-fmt` is a CONSUMER of `/lib/racoon`, not part of it: the Milestone A
interface is frozen, so the formatter imports the library like any other
caller. `print . parse` is asserted as an identity over the whole generated
vector corpus, which is a free property test the parser buys us — and it
immediately caught the printer emitting `(1/2)x^2` while the parser had no
rule for parentheses.

Building the library slogs `fund: in racoon, parent ... not found at 7`. This
is expected: no jets exist until Milestone B, so the runtime has nothing to
resolve the `%racoon` core's parent against.

## Integer factorization

`/lib/racoon-zfac` factors integers, which `nz` does not: that core is
`gcd egcd isqrt is-prime crt ratrec` and nothing else. The gap blocked the
multiplicative order of a unit, primitive roots, Euler's totient, and the
divisor set — all downstream of a factorization and none expressible
without one.

```
factor         @ud -> (list [p=@ud m=@ud])   primes ascending, canonical
is-prime-power @ud -> ?
radical        @ud -> @ud                    product of distinct primes
totient        @ud -> @ud                    Euler's phi
divisors       @ud -> (list @ud)             ascending
order       [a n] -> @ud                     least e with a^e = 1 mod n
primitive-root @ud -> (unit @ud)             least generator, or ~
```

**It is a consumer, and `nz` stayed frozen.** Adding a seventh arm would
have moved the battery axes of the six that Milestone B jets resolve
against, and nothing inside the frozen library calls this — so nothing
needed it there. Same pattern as `racoon-rs` and `racoon-fp3`, and the same
reasoning as Baloon's resolved question B2. Promote it into `nz` if a
Milestone C escalation ever opens that core for a batch of changes; not for
this alone.

**Every arm is `free`.** A factorization into primes is unique, so the
sorted output is canonical however it was found, and a jet may use Brent,
ECM, or a sieve. Only the *search* is pinned, and only because Hoon has no
randomness: Pollard's rho runs with `c = 1, 2, 3, …` in order, so an
unlucky first attempt is reproducible rather than merely unlikely.

**Termination is guaranteed, not probabilistic.** Rho can fail for any
given `c`, so after 32 attempts the search falls back to trial division,
which cannot fail on a composite. A caller waits longer; it never gets a
wrong answer or a crash. Small primes are stripped by division below
65,536 first, which is both faster at that size and what keeps rho's
degenerate cases (4, 8, and the like) from ever reaching it.

`factor(1)` is `~`, the empty product — the right answer, not an edge case.
`factor(0)` **crashes**: every prime divides zero, so there is no
factorization to return and no sentinel that would not be a lie. `order`
asserts that its argument is a unit, since a non-unit has no order at all.

Checked against SymPy's `factorint`, `totient`, `divisors`, `n_order`, and
`primitive_root`, plus the identities a fixed table cannot catch: the
factors multiply back, every listed factor is prime, the divisor count is
`∏(m+1)`, every divisor divides, `order` divides `φ(n)` and no proper
divisor of it works, and a primitive root really does generate every unit.

## Reference vectors

`desk/lib/racoon-vectors.hoon` is generated and **never hand-edited**:

```
pip install -r tools/requirements.txt
python3 tools/genvec.py > desk/lib/racoon-vectors.hoon
```

Deterministic: the PRNG seed is pinned in the script, so regeneration is
byte-identical. 61 families, 44–64 cases each, against the §11.2 minimum of 40.
Moduli cover §11.2's required set: `p = 2`, `p = 3`, a 61-bit prime, and the
composites 6, 12, 100, and 256.

Oracles are independent implementations — `math.gcd`, `math.isqrt`,
`sympy.isprime`, `sympy.ntheory.modular.crt`, `fractions.Fraction`, and
`sympy.Poly` over `ZZ`, `GF(p)`, and `QQ` for the polynomial rings. For the
two arms where §9 pins the *algorithm* rather than the value (`egcd`,
`ratrec`), the pinned algorithm is transcribed in Python and cross-checked
against an independent invariant — the Bézout identity against `math.gcd`, and
the congruence `q*u ≡ p (mod m)`. Identity-defined arms (`pdiv`, `divmod`,
`pp`) are likewise checked against their defining identity rather than a
reimplementation of the loop. That keeps the vectors a check on the Hoon
transcription rather than a copy of it.

**`res` does not use `sympy.resultant`.** SymPy normalizes its two arguments
by degree, so when `deg a < deg b` it returns `res(b, a)` — which differs in
sign whenever both degrees are odd. On a random sample it disagreed with the
definition on 19 of 300 pairs, every one of them `deg a < deg b`. The oracle is
the determinant of the Sylvester matrix instead: it is the definition, it
satisfies `res(a, b) = (-1)^(deg a · deg b) · res(b, a)` exactly, and it
reproduces §9's degree-0 convention `lc(a)^(deg b)` for free.

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
| `add:zx` | degree 64 | 15.032 ms | ~150 µs |
| `mul:zx` | degree 16 | 156.787 ms | ~1.57 ms |
| `mul:zx` | degree 64 (10 iter) | 238.026 ms | ~23.8 ms |
| `mul:zx` | degree 256 (1 iter) | 388.148 ms | ~388 ms |
| `mul:mx` | degree 16, 61-bit 𝔽p | 62.256 ms | ~623 µs |
| `mul:mx` | degree 64, 61-bit 𝔽p (10 iter) | 84.885 ms | ~8.49 ms |
| `mul:mx` | degree 256, 61-bit 𝔽p (1 iter) | 128.047 ms | ~128 ms |
| `gcd:mx` | degree 16, 61-bit 𝔽p (10 iter) | 90.318 ms | ~9.03 ms |
| `gcd:mx` | degree 64, 61-bit 𝔽p (1 iter) | 42.234 ms | ~42.2 ms |
| `gcd:zx` | degree 64 (1 iter) | 104.967 ms | ~105 ms |
| `res:zx` | degree 16 (1 iter) | 4.727 ms | ~4.73 ms |
| `factor:zx` | degree 32, 16 modular factors (1 iter) | 775.095 ms | ~775 ms |

Observations worth carrying into Milestone B:

- **`egcd` costs ~31× `gcd`** on identical inputs. Both run the same division
  sequence; the difference is the signed cofactor bookkeeping through `++si`,
  which allocates on every step. That ratio is the single most interesting
  number in this table, and `egcd` is a `pinned` arm, so a jet must reproduce
  the cofactors exactly rather than route around them.
- **Both `mul` arms are cleanly quadratic**: `mul:zx` runs 1.57 ms → 23.8 ms →
  388 ms and `mul:mx` runs 0.62 ms → 8.49 ms → 128 ms across degrees
  16/64/256, both close to 16× per 4× of degree, which is what classical
  convolution should cost. That the measured curve matches the algorithm means
  the baseline measures what it claims to, so Karatsuba/NTT in Milestone B have
  an honest curve to beat.
- **`mul:mx` is ~2.5× faster than `mul:zx`** at equal degree, despite doing a
  modular reduction on every coefficient operation. The modular arithmetic is
  plain `@ud` add/mul/mod, all jetted; `zx` routes every operation through
  `++si`, whose ZigZag encode/decode allocates. This is the same effect the
  `egcd`-vs-`gcd` row shows, and together the two say that in Milestone A the
  dominant cost of signed work is `++si`, not the mathematics.
- **The `is-prime` rows differ by 37×** between 20-bit and 61-bit inputs, but
  the 61-bit row deliberately feeds *primes*. A random 61-bit odd number is
  almost always rejected by trial division against the witness schedule, so
  sampling the range measures early exit, not Miller–Rabin. An earlier draft of
  this table did exactly that and reported the 61-bit case as *faster* than the
  20-bit one.

Every §11.4 row named by degree is now present.

`gcd:mx` at degree 64 costs *less* than at degree 16 (42 ms against 90 ms for
ten runs, so ~42 ms against ~9 ms per call — the per-call figures are the ones
to compare). Both are single measurements of one input pair, and Euclid's cost
depends on how fast the remainder degrees collapse, not on the starting degree
alone. Do not read a trend into two points.

## Testing

```
-test /=base=/tests/lib/racoon ~
```

210 arms, all green. Three kinds:

- **Behavioral** — known values and adversarial families. `is-prime` gets eight
  Carmichael numbers and five strong pseudoprimes rather than random odds,
  since a Fermat test passes every Carmichael and random odds are almost all
  trivially composite.
- **Crash rows** — every §8 row naming an implemented arm has a dedicated
  `++test-*-crash-*`, and matching `++test-*-nocrash-*` arms pin the edges that
  must *not* crash. §8 is a two-sided contract; both halves are jettable. For
  `zx` that means `deg` and `lc` crash on `~` while the other nine arms must
  not.
- **Vector-driven** — one `++test-*-vec-*` per generated family. Each reports
  *every* mismatching case rather than stopping at the first.

Property tests build their inputs with local helpers — `+to-zol`, `+to-mol`,
`+to-qol`, `+ipow`, `+tderiv` — rather than calling the library arm they would
otherwise be exercising. A squarefreeness check that borrowed the library's own
derivative would be checking less than it appears to.

**Exact reconstruction is the load-bearing factorization test** (§11.3): the
reassembled product must equal the input noun-for-noun, over both ℤ and 𝔽p.
Irreducibility of individual factors is certified by the SymPy vectors, not
in-ship. The Swinnerton–Dyer polynomials are the adversarial case — irreducible
over ℤ yet split mod *every* prime, so recombination must reject every proper
subset before concluding. §13 requires SD_3; it passes, and SD_4 and beyond are
out of scope until a van Hoeij milestone.

Property tests use `++og` from seeds pinned in the `%seeds` section of the test
file.

## Reed–Solomon

`/lib/racoon-rs` is a systematic Reed–Solomon codec over 𝔽p — the live
workload the library was built to be exercised against. Correctness is
self-evident: data either round-trips through deliberate corruption or it
does not.

```
+racoon-rs 'hello', =errs 2
"message   hello"
"codeword  ~[104 101 108 108 111 69 88 106 119]"
"corrupted ~[201 101 108 205 111 69 88 106 119]  (2 errors)"
"recovered hello"

+racoon-rs 'hello', =errs 3
"recovered UNCORRECTABLE"
```

**Prime field, not GF(2⁸).** Classical byte-oriented RS uses an extension
field, which Racoon does not implement — `mx` is ℤ/n, and 𝔽p only when n is
prime. With p = 257 every byte 0–255 is a distinct field element, so byte
data is representable; a parity symbol may come out as 256, which is a field
element but not a byte, and callers on a byte channel must account for it.

**The decoder needed one thing the frozen interface does not supply.** The
key equation is solved by an extended Euclid *stopped early*, once the
remainder degree drops below `nsym/2`. `egcd:mx` runs to completion and would
pass straight through the solution, so that loop is written locally over
`divmod:mx`. Everything else — syndromes, Chien search, Forney — is `mx`
arithmetic unchanged.

**Beyond capacity the answer may be wrong, not merely absent.** A word far
enough from every codeword can land nearer a *different* one, and the decoder
returns that with every syndrome satisfied.

This cannot be fixed inside the decoder, and that was measured rather than
assumed. The two consistency checks one would reach for — requiring every
located position to have nonzero magnitude, and requiring `deg(Ω) < deg(Λ)` —
change **nothing**: over 20,000 trials at each of `nsym = 2` and `4`, adding
either or both left the miscorrection count byte-identical, while never
losing a within-capacity correction. That is the theory confirmed. A
miscorrection is a genuine valid codeword whose error pattern is entirely
self-consistent relative to the wrong answer, so the information needed to
reject it is not present in the received word.

What works is policy, and the rate falls steeply with parity:

| `nsym` | miscorrection rate |
|---|---:|
| 2 | 426 / 20,000 = 2.1% |
| 4 | 9 / 20,000 = 0.045% |

Three levers, in increasing order of certainty: spend two more parity
symbols; use `decode-upto` to refuse corrections heavier than a chosen
weight, trading correction power for detection; or carry an outer integrity
check over the message. Only the last is certain.

## Extension fields

`/lib/racoon-fp3` builds 𝔽p[x]/(m) — a finite field as a quotient of the
polynomial ring by a monic irreducible modulus. The motivating case is the
cubic 𝔽p[x]/(x³ − x − 1) over the Goldilocks prime 2⁶⁴ − 2³² + 1, which is
Nockchain's `$felt`; hence the file name. **The door is general in the
modulus and works at any degree** — the tests run it as a quadratic too. The
name describes the instance that prompted it, not a restriction.

```
+racoon-fp3 [3 4 5]
"field:    F_p[x]/(x^3 - x - 1), p = 2^64 - 2^32 + 1"
"rank:     3"
"irred:    %.y"
"a:        ~[3 4 5]"
"a^-1:     ~[17.402.588.744.730.739.926 ... ]"
"a a^-1:   ~[1]"
"a^2:      ~[49 89 71]"
"a^(p^3):  ~[3 4 5]"
"N(a):     53"
```

Instantiate it on any prime and any irreducible modulus:

```
=gl3  %~  .  fp3
      :-  18.446.744.069.414.584.321
      ~[18.446.744.069.414.584.320 18.446.744.069.414.584.320 0 1]
```

**It is a consumer, not an extension of the library.** Racoon has no
extension fields by design — `mx` is (ℤ/n)[x], and 𝔽p only when n is prime.
This fills that gap from outside the frozen interface, using nothing but
`mx` polynomial arithmetic, which is the shape the freeze is meant to
permit.

**Inversion uses `egcd:mx` run to completion**, exactly as written: for
nonzero *a* of degree below deg(m) with m irreducible, gcd(a, m) = 1, so the
cofactor *u* in *ua* + *vm* = 1 is *a*⁻¹. That is the clean contrast with
Reed–Solomon, whose key equation needed the same algorithm *stopped early*
and so had to be written locally. Between them the two clients exercise both
halves of that arm.

**Irreducibility is a precondition, not an invariant.** A reducible modulus
makes the quotient a ring with zero divisors, and `inv` then crashes on
those divisors — honest, but not a diagnosis. `+irreducible` checks it once,
up front, by delegating to Racoon's certified factorization; the Goldilocks
cubic was verified against SymPy before the library was written and is
re-checked in-ship by the test suite.

**`+canon` reduces further than `canon:mx` does.** Racoon takes coefficient
range as a precondition of the `$mol` form, and its `canon` only strips
trailing zeros. Here `canon` is the boundary where outside data enters the
field, so it folds coefficients into [0, p) *and* brings the degree below
deg(m). Every other arm assumes its arguments are already field elements.

**Verification.** Goldilocks vectors for `mul`, `inv`, `frob`, `norm`, and
`pow` were computed independently in Python and transcribed, as the
Reed–Solomon vectors were; the norm was cross-checked against SymPy's
resultant. 𝔽₂₇ and 𝔽₄₉ are checked *exhaustively* — at 27 and 49 elements,
trying everything is a better test than sampling.

## Decision log

| # | Decision | Rationale |
|---|---|---|
| Q1 | Add `+$ ord ?(%lt %gt %eq)` to `sur` | §7 pins `+pcmp`'s product as `?(%lt %eq %gt)` but §6 names no type for it, and `hoon.hoon` has none to borrow — `++cmp:si` produces an `@s` in `{-1, --0, --1}`. Member order is deliberate: Hoon's fork bunt does not follow declaration order, and `?(%lt %gt %eq)` bunts to `%eq`. Do not reorder. |
| Q2 | `+cmp:qq` produces `$ord` | Same three-valued result as `+pcmp`; `+pcmp` on `qol` delegates to it rather than reimplementing the cross-multiplication. |
| Q3 | Add a §8 crash row: `+new:qq` on `q = 0` | No product respects the `$frac` invariant — `gcd(|p|, 0) = |p|` reduces to `q' = 0` — and R5 forbids downstream arms from re-canonicalizing, so a bad value would propagate silently. |
| Q4 | Jet registration follows `/lib/math.hoon`, not §10's prose | §10 demands mirroring that file "exactly" while also describing "nested `~%` per sub-core"; the file and Lagoon both use one root `~%` under `%non` and plain `~/` below. Followed the file, per §10's operative instruction. |
| Q5 | Reserve all five sub-core slots now; `%nz`/`%qq` frozen at the P0 gate | R6 freezes a hinted core once its phase closes, but adding an arm to a Hoon core moves the battery axes of the arms already there. Introducing `zx`/`mx`/`qx` as their phases land would shift the `%racoon` battery at every gate — and that is the parent axis each sub-core jet resolves against, so freezing `%nz` internally would buy a jet author nothing. Declaring all five arms now fixes `%racoon` for the milestone; each sub-core freezes at its own gate. |
| — | Interface frozen at the P3 gate | R6. `%zx`, `%mx`, and `%qx` join `%nz`, `%qq`, and `%racoon`; every hinted core's arm set and order is now fixed for the milestone. Each core's header comment records its public API, so a jet author can tell the public arms from the delegated helpers without consulting §9. |
| — | `factor:zx` monic-izes nothing; recombination multiplies by `lc` | Follows §9's pinned pipeline literally. The lifted factors are kept monic by dividing `f` through by its leading coefficient mod `p^k` — valid because `p ∤ lc(f)`, so `lc` is a unit at every power of `p`. |
| — | Delegated private helpers in `zx` beyond §9's public list | `lift`, `crt-lift`, `xdiv`, `combos`, `mprod`, `hstep`, `hlift`, `firr`; and `npow`, `mstrip`, `mderiv`, `mproot`, `remod` in `pv`. §14 delegates helper structure and naming. `xdiv` is worth noting: Z is not a field, so exact division goes through `pdiv` and then divides the quotient by `lc(b)^e`. |
| — | `res` oracle is the Sylvester determinant, not `sympy.resultant` | SymPy normalizes argument order by degree and so loses the sign when `deg a < deg b` and both degrees are odd; it disagreed with the definition on 19/300 sampled pairs. The determinant is definitional and self-consistent. The library correspondingly swaps to `deg a >= deg b` with the `(-1)^(mn)` sign, which the subresultant recurrence requires. |
| — | `gcd:qx` clears denominators and delegates to `gcd:zx` | Running Euclid over `$frac` directly invites rational coefficient swell — the classic failure mode. Delegating inherits both `gcd:zx`'s modular algorithm and its trial-division certification. |
| — | Private helpers live in `+pv`, outside the `%racoon` core | Helper churn cannot disturb the battery layout of a hinted core when the R6 freeze lands, and `=<` keeps them genuinely private. |
| — | `sync.sh` copies an explicit file list, not a blanket `rsync` | `%base` carries the kernel; being explicit means a stray file here can never shadow a `sys/` file there. |

[numerics]: https://github.com/urbit/numerics
