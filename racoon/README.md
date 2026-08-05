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

**Milestone C is well under way.** The candidates, in §13 of the spec:

| Candidate | Note |
|---|---|
| ~~Integer factorization~~ | **Built**, as `/lib/racoon-zfac` — see below. It did not need `nz` reopened |
| ~~Real-root isolation, Sturm/Descartes~~ | **Complete** — specified in `raccoon-spec.md` §R, all three phases built. See below |
| ~~Algebraic number arithmetic~~ | **Complete**, as `/lib/racoon-alg` — §A, all four phases. Not on §13's original list; it is what real-root isolation was for |
| ~~van Hoeij recombination~~ | **Complete** (§V), in `baloon/desk/lib/vanhoeij.hoon`, since it consumes both libraries. **The benchmark was wrong and was measured**: `factor:zx` does `SD_4` in 302 ms, not "out of scope". The cliff was `SD_5` at 204 s — now 9.4 s. See §V0 and Baloon's README |
| van Hoeij recombination, original entry | Would attack the known cost cliff — Zassenhaus is exponential in the worst case, and `SD_4`+ is out of scope until this lands. Needs LLL, which both specs fence out, so it requires escalation first |
| Rational function field | **Specified (§F); F0–F3 built** as `/lib/racoon-rf` and `/lib/racoon-lt`, repeated poles included. Rational functions, partial fractions, integration by Hermite + Rothstein–Trager, and the Laplace transform. Needs no primitive that does not exist — phase A's real algebraic numbers are what name the residues |
| Sparse multivariate | The largest and least specified |

## Layout

```
racoon/
  desk/
    sur/racoon.hoon           shared types
    lib/racoon.hoon           the library
    lib/racoon-vectors.hoon   generated vectors -- never hand-edited
    tests/lib/racoon.hoon     test suite -- core, P0 through P3
    tests/lib/racoon-fmt.hoon     rendering and parsing
    tests/lib/racoon-rs.hoon      Reed-Solomon
    tests/lib/racoon-fp3.hoon     extension fields
    tests/lib/racoon-zfac.hoon    integer factorization
    tests/lib/racoon-roots.hoon   real roots
    tests/lib/racoon-alg.hoon     algebraic numbers
    tests/lib/racoon-rf.hoon      rational functions
    tests/lib/racoon-lt.hoon      the Laplace transform
    lib/racoon-fmt.hoon       rendering and parsing
    lib/racoon-rs.hoon        Reed-Solomon codec over F_p
    lib/racoon-fp3.hoon       extension fields F_p[x]/(m)
    lib/racoon-zfac.hoon      integer factorization and its consequences
    lib/racoon-roots.hoon     real roots -- Milestone C, phase R complete
    lib/racoon-alg.hoon       real algebraic numbers -- phase A, a door
    lib/racoon-rf.hoon        rational functions -- phase F, also a door
    lib/racoon-lt.hoon        the Laplace transform -- phase F3
    gen/racoon-bench.hoon     benchmark generator
    gen/racoon-factor.hoon    factor a polynomial from the dojo
    gen/racoon-gcd.hoon       gcd of two polynomials from the dojo
    gen/racoon-rs.hoon        Reed-Solomon round-trip demonstration
    gen/racoon-fp3.hoon       Goldilocks extension field demonstration
    gen/racoon-zfac.hoon      factor an integer and its consequences
    gen/racoon-roots.hoon     isolate the real roots of a polynomial
    gen/racoon-alg.hoon       arithmetic on two algebraic numbers
    gen/racoon-alg-bench.hoon what that arithmetic costs, by degree
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

`sync.sh` copies an explicit list of the files this project owns; it never
boots or commits, because conflating the copy with the commit makes a failed
build hard to attribute. Override the pier with `RACOON_PIER=/path/to/zod`.

**Every file here builds from Racoon's desk alone**, `/lib/racoon-alg`
included — it reaches van Hoeij through a door sample rather than an
import, so Baloon binds it in from that side. See below.

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

## Real roots

`/lib/racoon-roots` is Milestone C phase R, complete: an **exact count** of
the distinct real roots of an integer polynomial in any rational range,
the **exact rational roots**, and a **canonical isolating interval** for
every root with refinement on demand. The library is named for real
algebraic numbers and, until this, produced none.

```
bound   zol -> frac              Cauchy bound; every root is inside (-B, B)
sign-at [zol frac] -> ord        sign of p(x); %eq exactly at a root
sturm   zol -> (list zol)        the Sturm chain of a squarefree p
count   [zol frac frac] -> @ud   distinct real roots in (a, b]
nroots  zol -> @ud               distinct real roots, all of R
sqpart  zol -> zol               squarefree part, p / gcd(p, p')
lowz    zol -> [k=@ud q=zol]     split off the factor x^k

rational-roots  zol -> (list [r=frac m=@ud])    exact, ascending
isolate         zol -> (list ivl)               canonical, disjoint
roots           zol -> (list rrt)               plus multiplicities
refine    [zol ivl @ud] -> ivl                  bisect k times
```

**Every arm is `free`.** Counting roots has one right answer, so a jet may
use Descartes with Taylor shifts, VCA, or anything else. Sturm is the
reference because it is simpler and more obviously correct — this
project's stated order of priorities.

**Signs are the whole difficulty, and they are silent when wrong.** Racoon
has no exact remainder over ℤ, only the pseudo-remainder `pdiv:zx`, whose
identity is

```
lc(b)^e * a = q*b + r,     e = deg a - deg b + 1
```

so `r` is the true remainder scaled by `lc(b)^e` — and **that factor is
negative when `lc(b) < 0` and `e` is odd**. A Sturm chain needs each term
to be `-rem` up to a strictly *positive* factor, so the sign of `lc(b)^e`
has to be undone rather than assumed away. Getting it wrong does not
crash; it silently miscounts. Terms are then reduced to their primitive
part, which is safe only because `pp:zx` carries its input's sign.

**`sturm` and `count` require a squarefree input and assert it** — the
chain's count is valid only there, and a silently wrong count is worse
than a crash. `nroots` accepts any nonzero polynomial and takes the
squarefree part itself, so a repeated factor is counted once.

**No floating point, now or later.** Every endpoint is an exact `frac` and
stays one; `refine` in phase R2 narrows on demand. Lagoon owns
approximation.

### What an isolated root is

**A root isolated to an interval is an exact object, not an
approximation.** The pair (polynomial, interval) determines one real
algebraic number and no other, which is how every serious system
represents them — SymPy's `CRootOf`, PARI, Maple. `refine` narrows the
interval to any width without ever leaving ℚ, so there is no precision to
lose and no rounding to accumulate.

```
isolate(x^2 - 2)          -> [[-3 0] [0 3]]
refine(x^2 - 2, [0 3], 6) -> [45/32, 93/64]      width exactly 3/2^6
isolate(x^3 - x)          -> [[-1 -1] [0 0] [1 1]]   all rational, exact
```

**Isolation is canonical**, which is what keeps every arm `free`. Given
the Cauchy bound B, the interval for a root is the *shallowest* node of
the binary subdivision tree of (−B, B] that holds it and no other root —
unique by construction, and a function of the polynomial alone. A jet may
use Descartes or VCA and must land on the same intervals.

**The half-open convention is what makes this exact.** A node `(lo, hi]`
splits into `(lo, mid]` and `(mid, hi]`, which partition it with no
overlap and no gap — so a root can be neither double-counted nor lost
between children, *including* one landing exactly on `mid`. A closed
convention needs a special case there; this needs none.

**A node whose one root is rational collapses to that exact point.** That
is also what keeps the intervals pairwise disjoint, and it is a
correction to the spec made while building: §R3 originally said rational
roots were *divided out* before subdividing, which breaks disjointness —
a node isolating an irrational root of the reduced polynomial can still
contain a rational root that was removed from the polynomial but not from
the number line. `SPEC-QUESTIONS.md` R3 records it.

### Arithmetic on them lives next door

`/lib/racoon-alg` — see below. Phase R deliberately stops at isolation;
adding and multiplying roots is phase A.

**Rational roots come back exact, and that is load-bearing.**
`rational-roots` returns values, never intervals — which is precisely the
clause phase R2's canonical isolation depends on: dividing the rational
roots out first removes the only way a root could land on a subdivision
boundary. Candidates come from the rational root theorem, so the candidate
set *is* `divisors:zfac` — which is why integer factorization had to be
built first, and the two pieces compose rather than merely coexist.

Two subtleties it handles rather than assumes. **`x^k` is split off
first**: the rational root theorem says nothing when `a_0 = 0`, since every
integer divides zero, and `divisors` crashes there anyway — so 0 is found
structurally and never by the divisor search. And **multiplicities come
from dividing each root out over ℚ** as many times as it goes, which makes
a repeated candidate self-cancelling: the second sighting divides zero
times and contributes nothing.

**Verification.** SymPy `Poly.count_roots` is the oracle for counts, and
`Poly.ground_roots` — which returns `{root: multiplicity}` over ℚ — for
the rational roots — confirmed
first, per §11.3, to count *distinct* roots: `(x-1)²(x+2)` gives 2, not 3.
Range endpoints in the vectors are chosen off the root set, since SymPy's
`count_roots` is inclusive on both ends while `count` here is half-open,
and that difference would otherwise be silent. The adversarial corpus is
different from Milestone A's: `SD_3` is in the factorization tests because
Zassenhaus is exponential on it, and here because its eight real roots sit
in a narrow band. Chebyshev polynomials have every root real in (−1, 1);
cyclotomics have none.

A test of mine caught exactly what this is for: a range of (−5, 7] excludes
one root of `SD_3`, whose extreme roots are ±(√2+√3+√5) ≈ ±5.382. `count`
reported 7 and was right; the test's assumption was wrong.

## Algebraic numbers

`/lib/racoon-alg` is Milestone C phase A: **arithmetic on real algebraic
numbers**. `√2 + √3` is a value here, not a polynomial someone had to
know to write down.

```
+of-q +to-q +make +deg +approx +cmp +sign +is-zero +is-rational
+neg +inv +add +sub +mul +div +pow +root
```

A number is `[minimal polynomial, canonical isolating interval]`. Both
halves are unique, so the form is canonical — and that buys two things:

- **Equality is structural.** `=(a b)` decides it. No refinement loop, no
  tolerance, no separate `equals` arm.
- **Every arm is `free`**, so a jet may use any algorithm at all.

The price is that every operation reduces to the minimal polynomial,
which means factoring. Paid deliberately: carrying whatever polynomial
happens to vanish at α would make equality undecidable without a gcd per
comparison, and make nothing canonical.

```
√2 · √3  →  x² − 6        degree 2, from a degree-4 resultant
√2 + √3  →  x⁴ − 10x² + 1  which is SD_2
1/√2     →  2x² − 1
√2 · √2  →  2              exactly rational, not a degree-1 anum
```

**Bivariate resultants by evaluation–interpolation.** `res:zx` is
univariate over ℤ, and `Res_y` of a polynomial in ℤ[x][y] cannot be
formed with the frozen arms — Baloon's polynomial-entry determinants are
unreachable, since Baloon depends on Racoon and not the reverse. But
`Res_y` has degree at most `deg p · deg q` in x, and **every evaluation of
it at an integer x is an ordinary univariate integer resultant**. So:
evaluate at that many points plus one, and interpolate. Nothing new was
needed in the frozen library.

**Three traps, each silent when wrong**, and each pinned in §A3 before
being coded:

- Interval multiplication is the min and max of the **four corner
  products**, not `[lo₁·lo₂, hi₁·hi₂]` — which fails for any interval
  straddling zero.
- `cmp` tests structural equality **first**. Without that the refinement
  loop never terminates on equal inputs.
- Degree-collapse cases must return exact **rationals**. `√2·√2` is 2,
  not a degree-1 algebraic number in disguise.

**The cost cliff was in the wrong place, and it was measured.** §A8
argued that `deg(α·β) ≤ deg α · deg β` puts two degree-4 numbers on a
degree-16 resultant, that `SD_4` is degree 16 and §9 fences it out, and
so **the two limits are the same limit**. The placement was right; the
attribution was not.

```
+racoon-alg-bench 'x^4 - 10x^2 + 1' 'x^4 - 24x^2 + 4'
```

| the sum | degrees | with `factor:zx` | with van Hoeij |
|---|---:|---:|---:|
| `(√2+√3) + (√5+√7)` → `SD_4` | 4 + 4 | 3.34 s | 3.34 s |
| `(√2+√3+√5+√7) + √11` → `SD_5` | 16 + 2 | 281.9 s | **90.4 s** |

**At the rung §A8 was actually describing, factoring is not the cost.**
Degree-4 plus degree-4 spends 0.3 s of its 3.34 s on the factorization
and the rest on the bivariate resultant — 17 univariate resultants and an
interpolation, none of which van Hoeij touches. It is the *next* rung
that inverts: at degree 32, Zassenhaus was 202.5 s of the 281.9 s and van
Hoeij does that part in 9.4 s, which leaves the resultant as ~90% of what
remains.

So degree 4 was never blocked, degree 32 no longer is, and the next
thing worth optimizing here is the evaluation–interpolation resultant
rather than the factorization.

**The factorization is one call, and the call is the door's sample.**
`/lib/racoon-alg` is a door over `fir`, which takes a primitive
squarefree polynomial to its irreducible factors. `+facz` — Yun's
squarefree decomposition, then `fir` per part — is the only arm that
reads it, and `+make` is the only arm that calls `+facz`:

```hoon
/+  al=racoon-alg               ::  firr:zx, the default; Racoon only
/+  ba=baloon-alg               ::  ~(. al factor:vh), the same door bound
```

Two arms already have that contract natively: `firr:zx`, which is
Zassenhaus and is bound as the default, and `factor:vh`, which is van
Hoeij. Below sixteen modular factors `factor:vh` *is* `firr:zx` — it
falls through the `lat-min` gate to the identical enumeration — so
neither binding can be the slower choice on any input.

**This is why the dependency runs the right way.** An import would have
made `racoon/desk` need Baloon to build; a sample does not, because
`+add`, `+mul`, `+div`, and `+root` all reach factorization through
`+make`, and an arm calling another arm of its own door resolves against
that door's sample. Setting it once at the top reaches everything
underneath, with nothing threaded through the arms.

`/lib/baloon-alg` is the bound instance as a file, so the fast path is
also a plain import — a caller who forgets to bind gets the right answer
slowly and silently, which is worth a two-line file to prevent.
`SPEC-QUESTIONS.md` R4 records this and the decision before it, that van
Hoeij lives in a consumer importing both libraries rather than
duplicating Baloon's integer matrices inside Racoon.

**Verification.** SymPy `minimal_polynomial` is the oracle — it *is* the
canonical form §A2 pins. Confirmed before pinning, per §11.3, that
`minimal_polynomial(√2·√3)` is `x² − 6`: **degree 2 where the resultant is
degree 4**. A suite built only from degree-preserving cases would pass
with the factor-and-select step deleted, so the collapsing cases carry
the weight.

## Driving it from the dojo

Every library has a generator now. Nothing below is floating point: the
decimals are exact digits of exact rationals, produced by repeated exact
division.

```
+racoon-zfac 360
360  =  2^3 * 3^2 * 5
radical        30
totient        96
primitive root none (not cyclic)

+racoon-roots 'x^3 - x - 1'
distinct real     1
Cauchy bound      2
  1.324717957244...  in [-2, 2]

+racoon-alg 'x^2 - 2' 'x^2 - 3'
a        1.414213562373...  root of x^2 - 2
a + b    3.146264369941...  root of x^4 - 10x^2 + 1
a * b    2.449489742783...  root of x^2 - 6
a^2      2
deg a*b 2 -- not the product
```

**`+shoapp` refines until both endpoints truncate alike**, and only then
prints. Taking the lower endpoint alone gives a *bound*, not the
expansion — √2 came out as `1.414213562372`, one in the last place below
the true value, and a trailing `...` would then be claiming digits that
are not right. It terminates because an irrational root is never exactly
a k-digit decimal, so some neighbourhood of it truncates uniformly.

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

### Numbers that come back as data

`~>(%bout ...)` is a **slog**: it prints to the ship's output and returns
nothing, so reading it back means scraping the terminal. That is fine for
a person and bad for a script — it produced four distinct failures in one
afternoon, the worst being a `-test` that ran *before* its `|commit`
landed and reported a negative control as passing.

```
scripts/bench.sh nop                                    the harness floor
scripts/bench.sh alg 'x^4 - 10x^2 + 1' 'x^4 - 24x^2 + 4'
scripts/bench.sh alg -f 'x^4 - 10x^2 + 1' 'x^4 - 24x^2 + 4'
```

`/ted/racoon-bench` is a thread; `%fyrd` is synchronous and returns the
thread's product, so none of the four failures is possible. It reports
microseconds *and* a check derived from the answer — for `alg`, the
degree of the sum's minimal polynomial — because a benchmark that
measured a crash is exactly what a bare duration cannot show.

The `-f` flag picks the **thread**, not a flag on the job:
`/ted/racoon-bench` is Racoon-only and gets `firr:zx` from the door's
default, while `/ted/baloon-bench` binds `factor:vh`. That is the same
split `/gen/racoon-alg-bench` and `/gen/baloon-alg-bench` use, and it is
what keeps `racoon/desk` building alone.

The clock is two zero-length sleeps around the work, since Arvo's `now`
is fixed within an event. It costs about **10 ms**, which `nop` measures
rather than assumes and which is *not* subtracted — read sub-millisecond
readings as "small", not as exact. Above that it agrees with `%bout`
across two orders of magnitude, which is the check that matters:

| | `bench.sh` − floor | `%bout` |
|---|---:|---:|
| `vh 3 0` | 21 ms | 22.4 ms |
| `vh 4 0` | 288 ms | 298.7 ms |
| `lll 8 1 136` | 135 ms | 0.135 s |
| `lll 16 1 136` | 634 ms | 0.641 s |
| `alg` deg 4 + 4 | 3.31 s | 3.34 s |

### Integration, both factorizer bindings — §F9.6

```
scripts/bench.sh int 16 0        1/∏(x−i), default binding
scripts/bench.sh int -f 16 0     the same, van Hoeij bound
```

Two families are needed, because **"expensive to factor" and
"integrable" pull against each other**: the denominators Zassenhaus
finds hard are irreducible with many modular factors, and an irreducible
denominator of degree above 2 usually has irrational residues, which
§F6 puts out of range. Floor subtracted, best of two:

| denominator | deg | `r` | `firr:zx` | van Hoeij |
|---|---:|---:|---:|---:|
| `1/∏(x−i)` | 4 | 4 | 18 ms | 20 ms |
| | 8 | 8 | 60 ms | 66 ms |
| | 16 | **16** | **259 ms** | **477 ms** |
| `g′/g`, `g = x^d+1` | 4 | 2 | 8 ms | 9 ms |
| | 8 | 2 | 12 ms | 14 ms |
| | 16 | 2 | 26 ms | 27 ms |

**The interesting row is the third, and it is about `lat-min` rather
than about `integrate`.** A denominator that splits into sixteen
distinct linear factors has `r = 16`, so the gate engages and van Hoeij
runs — and it is **1.8× slower**, because sixteen linear factors
recombine at cardinality *one*. Zassenhaus finds every factor on its
first pass and the lattice is pure overhead.

That does not make `lat-min = 16` wrong for `SD_5`, where it is worth
21×. It makes the *predictor* wrong: `r` alone cannot distinguish
sixteen factors that recombine trivially from sixteen that need 39,202
subsets, and those are the two ends of the same number.
`baloon/SPEC-QUESTIONS.md` V1 records it as open, with the cheap
mitigation — try cardinality one first, engage the lattice only for what
survives.

**The second family measures something else than intended, and the
comment in `/ted/racoon-bench` now says so.** `x^d + 1` was reached for
as the factorization-expensive case; measured, it has `r = 2` at every
degree, so the gate never engages and both bindings agree. What those
rows actually show is the single-factor path — Hermite and one residue
on a high-degree denominator, with no partial-fraction spread.

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

239 arms, all green. Three kinds:

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
subset before concluding. §13 requires SD_3; it passes. `SD_4` and `SD_5` were
declared out of scope and then measured — 302 ms and 204 s through `firr:zx`,
not out of scope at all (§V0) — and `SD_5` now factors in 9.42 s through
`/lib/vanhoeij`. Neither is in the suite, because a 9-second arm is not worth
paying for on every run; `/gen/baloon-vh-bench` is where they live.

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
| — | Delegated private helpers in `zx` beyond §9's public list | `crt-lift`, `hstep`, `hlift`, `firr`; and `npow`, `mstrip`, `mderiv`, `mproot`, `remod` in `pv`. §14 delegates helper structure and naming. `xdiv`, now public, is worth noting: Z is not a field, so exact division goes through `pdiv` and then divides the quotient by `lc(b)^e` — and it returns a wrong answer rather than crashing on an inexact division, which is why its docstring points callers at `pdiv` when exactness is not already known. |
| — | `%zx` unfrozen once for phase V1; six helpers promoted and two arms added | `+zmod` and `+hdata` added, and `xdiv`, `lift`, `combos`, `mprod` promoted out of the delegated set, because `/lib/vanhoeij` consumes all of them across a desk boundary and §14 lets delegated helpers change without escalation — a cross-desk consumer cannot rest on that. `+deriv` was promoted in the same batch, which is exactly the condition SPEC-QUESTIONS R1 named for revisiting it. The batch moves the battery axes of every arm after `+eval`, which is free only because Milestone B has not opened; any further insertion belongs in this window or not at all. |
| — | `/lib/racoon-alg` is a door over its recombination step, not an importer of one | Reaching van Hoeij by import made `racoon/desk` need Baloon to build. As a sample it does not, and the injection needs no threading: every arithmetic arm reaches factorization through `+make`, and an arm calling its own door's arm resolves against that door's sample. `firr:zx` is the default, `/lib/baloon-alg` is the same door with `factor:vh` bound. Measured, the binding is worth nothing at degree 16 — where the bivariate resultant is the whole cost — and takes the degree-32 sum from 281.9 s to 90.4 s. The rejected alternative was promoting `+bires` and the selection loop and duplicating `add`/`mul`/`div` next to `/lib/vanhoeij`. |
| — | The default binding is `firr:zx`, which is delegated rather than public | §14 lets delegated helpers change without escalation, so a default standing on one is a thread worth naming. It is the same desk, which is the hazard §14 is not about, and the alternative — defaulting to public `factor:zx` — would run Yun's decomposition twice on every call to save nothing. Revisit if `%zx` is ever unfrozen again. |
| — | `res` oracle is the Sylvester determinant, not `sympy.resultant` | SymPy normalizes argument order by degree and so loses the sign when `deg a < deg b` and both degrees are odd; it disagreed with the definition on 19/300 sampled pairs. The determinant is definitional and self-consistent. The library correspondingly swaps to `deg a >= deg b` with the `(-1)^(mn)` sign, which the subresultant recurrence requires. |
| — | `gcd:qx` clears denominators and delegates to `gcd:zx` | Running Euclid over `$frac` directly invites rational coefficient swell — the classic failure mode. Delegating inherits both `gcd:zx`'s modular algorithm and its trial-division certification. |
| — | Private helpers live in `+pv`, outside the `%racoon` core | Helper churn cannot disturb the battery layout of a hinted core when the R6 freeze lands, and `=<` keeps them genuinely private. |
| — | `sync.sh` copies an explicit file list, not a blanket `rsync` | `%base` carries the kernel; being explicit means a stray file here can never shadow a `sys/` file there. |

[numerics]: https://github.com/urbit/numerics
