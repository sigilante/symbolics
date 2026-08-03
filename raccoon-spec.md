# RACOON — Real AlgebraiCs in hOON

**Engineering Specification v0.1 — Milestone A: the Hoon-normative kernel**

Status: **normative**. Sections 5–10 are pinned. Deviations require escalation per §14 before any code is written against the deviation. This document is the source of truth; the decision log in `README.md` records approved amendments.

Audience: an agentic coding assistant (Claude Code / Opus) with a human reviewer. Assume competence; assume no prior context beyond this document and the referenced precedents.

---

## 1. Mission

A deterministic computer algebra kernel for Urbit, sibling to `urbit/numerics`. Exact arithmetic over ℤ, ℚ, ℤ/n; univariate polynomial arithmetic, division, GCD, resultants, and factorization over 𝔽p and ℤ. Scope is von zur Gathen & Gerhard, *Modern Computer Algebra* (hereafter **vzGG**), Parts I–III, univariate only.

Milestone A delivers the **Hoon library as authoritative specification**, with tests, reference vectors, and jet registration hints in place. Native jets (FLINT-backed) are Milestone B and are out of scope here except as constraints on A.

## 2. Platform contract — read before writing any code

1. Urbit computes over nouns: an atom is an arbitrary-precision natural; a cell is a pair of nouns. All computation is deterministic and reproducible to the bit across hosts.
2. The Hoon library is the specification. A **jet** is a native reimplementation that must be Kleene-equal to the Hoon on **every** input: same value, or same deterministic crash, or same divergence. Crashes are observable through Nock's virtualization tower; they are part of the interface, not an afterthought.
3. **Canonical-output principle.** Exact algebra has unique answers: a product in ℤ[x], a monic GCD, a factorization into irreducibles. Any arm whose output is canonicalized leaves future jets free to use *any* algorithm. Therefore: **every public arm either (a) returns a canonical value, or (b) has its algorithm pinned in this spec.** Prefer (a). §9 classifies every arm as `free` or `pinned`.
4. **Crash discipline.** Every crash condition is enumerated in §8. Edge-case crash mismatch is the historical jet-bug class (atom parsing, zero cases, degree conventions). Pin them now; test them all.
5. **Modular-first.** Prefer algorithms that compute modulo word-sized primes and reconstruct (CRT, rational reconstruction), with a certification step that makes the output algorithm-independent. This controls intermediate expression swell against a bounded loom and matches vzGG's own methodology.
6. **Supported-domain policy.** Public arms require canonical inputs (§7) and stated preconditions. On violation, the Hoon computes whatever it computes (deterministically); Milestone B jets will detect the violation cheaply and fall back to Nock, preserving the universal contract. Consequence for A: do **not** add defensive re-canonicalization inside arms. Keep preconditions O(1)-checkable where possible.

## 3. Deliverables

| # | Path | Contents |
|---|------|----------|
| 1 | `desk/sur/racoon.hoon` | Shared types (§6) |
| 2 | `desk/lib/racoon.hoon` | The library. Single file, nested cores (§6) |
| 3 | `desk/lib/racoon-vectors.hoon` | Generated reference vectors. Never hand-edited |
| 4 | `desk/tests/lib/racoon.hoon` | Test suite (§11) |
| 5 | `desk/gen/racoon-bench.hoon` | Benchmark generator: timing table, no perf gates |
| 6 | `tools/genvec.py` | SymPy-based vector generator emitting deliverable 3 |
| 7 | `README.md` | Setup, test loop, pinned versions, recorded baselines, decision log |

Repository layout:

```
racoon/
  desk/
    sur/racoon.hoon
    lib/racoon.hoon
    lib/racoon-vectors.hoon
    tests/lib/racoon.hoon
    gen/racoon-bench.hoon
  tools/genvec.py
  tools/requirements.txt        :: pinned sympy version
  scripts/sync.sh               :: rsync desk/ into the pier
  scripts/test.sh               :: convenience wrapper if useful
  README.md
  SPEC.md                       :: this document
  SPEC-QUESTIONS.md             :: escalation log (§14)
  .gitignore                    :: zod/ pier, *.pill, __pycache__
```

## 4. Development environment and loop

1. Obtain a Linux x86_64 `urbit` (Vere) binary, latest stable release. Pin the exact version in `README.md`.
2. Boot a fake ship once: `./urbit -F zod` (supply `-B <pill>` only if the binary demands it). The pier `zod/` persists across sessions. Gitignore it.
3. Record the Hoon/Zuse kelvins of the booted `%base` in `README.md`. Target whatever the pinned Vere release ships; do not chase newer kelvins mid-milestone.
4. Edit–test loop:
   - `|mount %base` (once, in dojo)
   - `scripts/sync.sh` — copy `desk/*` over `zod/base/`
   - `|commit %base`
   - `-test /=base=/tests/lib/racoon ~`
5. All tests run **inside the ship** via the standard `/lib/test` framework: arms named `++test-*`, product `tang`, using `++expect-eq` and the framework's crash-expectation helper. If `-test`, `|commit`, or `/lib/test` misbehave in ways you cannot resolve from `%base` source, escalate (§14). Do not build a bespoke harness.
6. `tools/genvec.py` runs on the host (Python 3 + SymPy, versions pinned in `tools/requirements.txt`) and regenerates `lib/racoon-vectors.hoon` deterministically (fixed PRNG seed inside the script). The ship never shells out; vectors are Hoon constants.
7. Dojo is available for interactive debugging: `=r -build-file /=base=/lib/racoon/hoon` then poke at arms.

## 5. Design invariants (restated as rules)

- **R1.** Canonical value or pinned algorithm, per arm. No third option.
- **R2.** All crash conditions enumerated (§8) and tested.
- **R3.** No `~|` (crash-trace hints) anywhere in `lib/racoon.hoon`. Trace payloads are observable under virtualization; keeping them out keeps the jet contract to bare crash-vs-value. Use plain `?>` / `!!`.
- **R4.** Modular-first for ℤ[x] algorithms, with mandatory certification steps (trial division) so outputs are algorithm-independent.
- **R5.** Canonical inputs are the supported domain (§7); no defensive normalization inside arms.
- **R6.** After a phase gate closes, the battery layout of hinted cores is frozen (§10). No arm reordering, renaming, insertion into frozen cores without escalation.
- **R7.** Dry gates only. A wet gate requires a written justification in the decision log. Every arm carries an explicit `^-` product cast.
- **R8.** No dependencies beyond: `hoon.hoon` standard arms (notably `++si`, `++og`), and `/lib/test` in the test file only. Reuse of any other kernel arm requires verification against `%base` source and a decision-log entry.

## 6. Types and library structure

`desk/sur/racoon.hoon`:

```hoon
|%
::  $frac: rational number.
::  Invariant: q > 0, gcd(|p|, q) = 1. Zero is [--0 1]; one is [--1 1].
::
+$  frac  [p=@s q=@ud]
::  Dense univariate polynomials, little-endian:
::  index i holds the coefficient of x^i.
::  Canonical form: no trailing zero coefficient. Zero polynomial = ~.
::
+$  zol   (list @s)     ::  Z[x]     (trailing element, if any, != --0)
+$  mol   (list @ud)    ::  (Z/n)[x] (coefficients in [0, n); trailing != 0)
+$  qol   (list frac)   ::  Q[x]     (trailing element != zero frac)
::  $zfac: factorization over Z.  input = c * prod(p_i ^ m_i).
::  Each p_i primitive with positive leading coefficient, irreducible in Z[x];
::  |c| = content of input; sign(c) = sign of input's leading coefficient.
::  fs sorted ascending by +pcmp (§7); m_i >= 1; p_i pairwise distinct.
::
+$  zfac  [c=@s fs=(list [p=zol m=@ud])]
::  $mfac: factorization over F_p (n prime).  input = c * prod(p_i ^ m_i).
::  c = leading coefficient of input; each p_i monic irreducible; sorted; distinct.
::
+$  mfac  [c=@ud fs=(list [p=mol m=@ud])]
--
```

`desk/lib/racoon.hoon` skeleton:

```hoon
/-  *racoon
::  Jet registration: mirror the registration structure of
::  urbit/numerics /lib/math.hoon exactly (root ~% hint named %racoon,
::  nested ~% per sub-core, per-arm ~/ per §10). Copy the working pattern
::  from that file; do not invent a variant.
::
|%
+|  %scalars
++  nz                  ::  integers and number theory
  |%
  ++  gcd      ::  ...
  ++  egcd     ::  ...
  ++  isqrt    ::  ...
  ++  is-prime ::  ...
  ++  crt      ::  ...
  ++  ratrec   ::  ...
  --
++  qq                  ::  rational scalars
  |%
  ::  new add sub mul div neg inv cmp  (and constants zero, one)
  --
+|  %polynomials
++  zx                  ::  Z[x]
  |%
  ::  Phase 1: canon is-zero deg lc pcmp add sub neg mul shift scale eval
  ::  Phase 2: pdiv content pp gcd res disc mig
  ::  Phase 3: sqfree factor
  --
++  mx                  ::  (Z/n)[x] and Z/n scalar arithmetic
  |_  n=@ud             ::  precondition n >= 2 on all arms (§8)
  ::  scalars (c- prefix): cadd csub cmul cneg cinv cpow
  ::  Phase 1: canon is-zero deg lc add sub neg mul shift scale eval
  ::  Phase 2: divmod gcd egcd powmod
  ::  Phase 3 (n prime, asserted): sqfree ddf edf factor
  --
++  qx                  ::  Q[x]
  |%
  ::  Phase 2: canon is-zero deg lc add sub neg mul divmod gcd eval
  --
--
```

Notes:
- Single library file. Nested cores keep one jet-registration tree and mirror how `hoon.hoon` itself scales. Split only via escalation.
- `@s` is Hoon's ZigZag-coded signed integer; all signed scalar arithmetic goes through `++si`.
- One `++mx` door serves both 𝔽p and ℤ/n. Field-only arms assert primality at runtime (§8). There is no separate `fx` core.

## 7. Canonical conventions (normative)

| Item | Convention |
|---|---|
| `frac` | `q > 0`, fully reduced; zero `[--0 1]`, one `[--1 1]` |
| ℤ/n element | `@ud` in `[0, n)`; `n >= 2` |
| Polynomial rep | Dense, little-endian, no trailing zero coefficient; zero poly = `~` |
| `+deg` | Degree of nonzero poly = `(dec (lent p))`. Undefined (crash) on `~` |
| `+content` (zx) | `content(~) = 0`; otherwise gcd of `|coefficients|`, always `>= 0` |
| `+pp` (zx) | Primitive part; `pp(~) = ~`; `content * pp = input` exactly, so `pp` carries the input's sign |
| `+gcd` (mx) | Monic. `gcd(~, ~) = ~`; `gcd(a, ~) = monic(a)` |
| `+gcd` (zx) | `gcd(cont a, cont b) * G` where `G` is the primitive gcd with **positive leading coefficient**. `gcd(~, ~) = ~`; `gcd(a, ~) = a` normalized to positive lc |
| `+gcd` (qx) | Monic; via denominator-cleared reduction to zx |
| `+egcd` (nz) | Input `[a=@ud b=@ud]`, output `[d=@ud u=@s v=@s]` with `d = u*a + v*b`. Algorithm pinned: textbook EEA (vzGG Alg. 3.6), base case `egcd(a, 0) = [a --1 --0]`. The standard EEA cofactors satisfy `|u| <= b/(2d)`, `|v| <= a/(2d)` for `a, b > 0` (test as property, not assertion) |
| `+egcd` (mx) | `[g u v]`, `g` monic, `(u, v)` = EEA-computed cofactors scaled by the inverse of the final remainder's lc. Algorithm pinned |
| `+pcmp` | Total order on polynomials, defined once per coefficient type and reused everywhere: (1) shorter list (lower degree, with `~` least) first; (2) equal length: compare coefficients from highest index down — `++cmp:si` for `@s`, numeric for `@ud`, and for `frac` compare `p1*q2` vs `p2*q1` via `++cmp:si`. Product type: `?(%lt %eq %gt)` |
| Factor lists | Sorted ascending by `+pcmp`; multiplicities `>= 1`; factors pairwise distinct |
| `+pow`-style arms | Binary left-to-right square-and-multiply (pinned for clarity; outputs are canonical regardless) |
| `+is-prime` | Deterministic Miller–Rabin, witness schedule `[2 3 5 7 11 13 17 19 23 29 31 37]` in that order. Provably exact for `n < 3.317e24` (Sorenson–Webster); above that bound the same schedule runs and the result is deterministic but heuristic — document this in the arm comment and README |
| `+mig` (zx) | Landau–Mignotte-style factor-coefficient bound, pinned formula: for `f` of degree `n` with max absolute coefficient `A`: `B(f) = (bex n) * (+((isqrt +(n)))) * A` i.e. `2^n * (isqrt(n+1)+1) * A`. Sufficient, not tight. Lifting target in `+factor` is the least `p^(2^k) > 2 * B(f) * |lc(f)|` |

## 8. Crash table (normative — every row gets a test)

| Arm | Condition | Behavior |
|---|---|---|
| `+deg`, `+lc` (all rings) | input `~` | crash |
| `+div`, `+inv` (`qq`) | divisor / operand zero | crash |
| `+cinv` (mx) | non-unit (including 0) mod n | crash |
| `+cpow` (mx) | `0^0` | returns `1` (pinned, no crash) |
| `+divmod` (mx) | `b = ~` | crash |
| `+divmod` (mx) | `lc(b)` not a unit mod n | crash |
| `+divmod` (qx) | `b = ~` | crash |
| `+pdiv` (zx) | `b = ~` | crash |
| `+powmod` (mx) | modulus `f` with `deg f < 1`, or `f = ~` | crash |
| `+crt` (nz) | moduli not pairwise coprime, any modulus `< 2`, or empty list | crash |
| `+ratrec` (nz) | no solution within bounds | **no crash**: product is `(unit frac)`, `~` on failure |
| `+sqfree` `+ddf` `+edf` `+factor` (mx) | `n` fails `+is-prime` | crash (assert primality; cost is negligible against factoring) |
| `+factor` (zx / mx) | input `~` | crash (factorization of zero is undefined) |
| `+factor` (zx / mx) | input degree 0 | returns `[c ~]` (no crash) |
| `++mx` door generally | `n < 2` | outside supported domain (§2.6): Hoon computes deterministically, jets will fall back; not asserted per-arm |

No `~|` anywhere (R3). Crash via `?>` guards or structural `!!`/`+snag`-style failure — whichever the arm's logic makes natural. What is pinned is *that* it crashes, not the trace.

## 9. Public API by phase

Column key — **Jet**: `free` = output canonical, Milestone B jets may use any algorithm; `pinned` = jets must replicate the pinned algorithm exactly.

### Phase 0 — scalars and number theory (`nz`, `qq`)

| Arm | Signature | Spec algorithm | Jet |
|---|---|---|---|
| `gcd:nz` | `[a=@ud b=@ud] -> @ud` | Euclid; `gcd(0,0) = 0` | free |
| `egcd:nz` | `[a=@ud b=@ud] -> [d=@ud u=@s v=@s]` | EEA per §7 | pinned |
| `isqrt:nz` | `[a=@ud] -> @ud` | floor sqrt; Newton iteration from `bex((met 0 a)+1/2)`-style seed, monotone clamp; result `r` satisfies `r^2 <= a < (r+1)^2` | free (output canonical) |
| `is-prime:nz` | `[n=@ud] -> ?` | MR per §7 | pinned |
| `crt:nz` | `[(list [r=@ud m=@ud])] -> [r=@ud m=@ud]` | left fold, pairwise via `egcd`; result `r` in `[0, prod m)` | free |
| `ratrec:nz` | `[u=@ud m=@ud nb=@ud db=@ud] -> (unit frac)` | Wang / EEA on `(m, u)`: stop at first remainder `<= nb`; accept iff corresponding `|t| <= db` and `gcd(r?, t)` compatible (vzGG §5.10); default caller bound `nb = db = isqrt((m-1)/2)` | pinned |
| `qq` arms | `add sub mul div neg inv cmp new` on `frac` | Schoolbook + reduce to canonical form | free |

### Phase 1 — polynomial arithmetic (`zx`, `mx`; `qx` arithmetic may land here or in Phase 2)

Per ring: `canon` (strip trailing zeros; the only arm that accepts non-canonical input), `is-zero`, `deg`, `lc`, `pcmp`, `add`, `sub`, `neg`, `mul` (classical convolution — vzGG §2), `shift` (`[p=poly k=@ud]`, multiply by `x^k`), `scale` (scalar times poly), `eval` (Horner). `mx` additionally: scalar arms `cadd csub cmul cneg cinv cpow`.

All Phase 1 arms: **free** (canonical outputs). The classical spec algorithms exist to be readable and correct, not fast; jets bring Karatsuba/NTT later.

### Phase 2 — division, GCD, resultants

| Arm | Signature | Spec algorithm | Jet |
|---|---|---|---|
| `divmod:mx` | `[a=mol b=mol] -> [q=mol r=mol]` | Scale through `cinv(lc b)`, schoolbook division; `a = q*b + r`, `deg r < deg b` or `r = ~` | free |
| `gcd:mx` | `[a=mol b=mol] -> mol` | Euclid, monic normalization at end | free |
| `egcd:mx` | `[a=mol b=mol] -> [g=mol u=mol v=mol]` | EEA per §7 | pinned |
| `powmod:mx` | `[a=mol e=@ud f=mol] -> mol` | reduce `a` mod `f`, then square-and-multiply with reduction each step | free |
| `pdiv:zx` | `[a=zol b=zol] -> [q=zol r=zol]` | Pseudo-division: `lc(b)^(deg a - deg b + 1) * a = q*b + r` (vzGG §6.12 area); pinned exponent exactly that | free (identity fixes q, r uniquely) |
| `content:zx` / `pp:zx` | per §7 | elementwise via `gcd:nz` / exact division | free |
| `gcd:zx` | `[a=zol b=zol] -> zol` | **Modular (small-primes / Brown)**, pinned spec procedure: strip to `c = gcd(cont a, cont b)` and primitive parts; scan odd primes ascending skipping `p | lc(a')*lc(b')`; per prime compute monic gcd in `mx p`; track minimal degree, discard larger-degree images, restart accumulation on strictly smaller degree; CRT coefficient-wise with symmetric lift into `(-m/2, m/2]`; scale candidate to leading coefficient `gcd(lc a', lc b')` before lift (Brown's lc correction), take `pp`, normalize `lc > 0`; **certify by trial division into both `a'` and `b'`** — loop with more primes until certified; return `c * G`. Certification makes the output the true gcd, hence algorithm-independent | free (because certified) |
| `res:zx` | `[a=zol b=zol] -> @s` | Subresultant PRS (vzGG §6.10–6.11); `res` with either arg `~` = `--0`; either arg degree 0: pinned to the standard convention `res(a, b) = lc(a)^(deg b)` for `deg a = 0` (and symmetrically) | free (resultant is canonical) |
| `disc:zx` | `[a=zol] -> @s` | `(-1)^(n(n-1)/2) * res(a, a') / lc(a)`, exact division; crash if `deg a < 1` | free |
| `mig:zx` | `[a=zol] -> @ud` | Bound formula per §7 | pinned (it *is* a formula) |
| `qx` arms | `divmod`, `gcd` (monic) | clear denominators, delegate to `zx`/schoolbook, rescale | free |

### Phase 3 — factorization

| Arm | Signature | Spec algorithm | Jet |
|---|---|---|---|
| `sqfree:mx` | `[a=mol] -> mfac`-shaped squarefree decomposition | Classic char-p recursion: `gcd(f, f')`; if `f' = ~` then `f = g(x^p)`, recurse on p-th root (coefficient Frobenius: `c^(p^(k-1))` as needed — for prime fields the p-th root of `g(x^p)` is obtained by index division by p) | free |
| `ddf:mx` | distinct-degree splitting | iterate `h <- powmod(h, p, f)` from `h = x`; split off `gcd(h - x, f)` per degree | free |
| `edf:mx` | equal-degree splitting, degree `d` | **Deterministic trial sequence**, pinned: odd `p`: candidates `a_j = x + j` for `j = 0, 1, 2, …` (as `mol`), split via `gcd(powmod(a_j, (p^d - 1)/2, f) - 1, f)`, recurse on both parts; `p = 2`: trace-map splitting with candidates `c_j = x^j`, `j = 1, 2, …`, `T(c) = c + c^2 + c^4 + … + c^(2^(d-1))` computed mod `f`, split via `gcd(T(c_j), f)` (vzGG §14.3 area) | free (final factor **set** is unique; the pinned sequence guarantees the *spec* terminates deterministically, but any correct jet reaches the same sorted output) |
| `factor:mx` | `[a=mol] -> mfac` | assert prime; `c = lc`; monic-ize; sqfree → ddf → edf; assemble sorted | free |
| `sqfree:zx` | Yun's algorithm (char 0) | standard Yun | free |
| `factor:zx` | `[a=zol] -> zfac` | Pinned pipeline: (1) strip sign/content into `c`; (2) `sqfree`; (3) per squarefree part `g`: choose `p` = smallest odd prime with `p ∤ lc(g)` and `g mod p` squarefree, scanning ascending; (4) `factor:mx p` on `g mod p`; (5) multifactor **quadratic** Hensel lift (vzGG §15.4–15.5), balanced factor tree splitting the factor list at `⌈r/2⌉` recursively, lift to the least `p^(2^k) > 2 * mig(g) * |lc(g)|`; (6) **Zassenhaus recombination**, pinned enumeration: subsets by cardinality ascending (up to `⌊r/2⌋`, complement rule for the rest), within a cardinality lexicographic ascending on index tuples; candidate = symmetric lift of `lc(g) * prod(subset)`, take `pp`, trial-divide into remaining `g`; on success remove indices and continue at same cardinality; (7) assemble `zfac`, sorted, factors primitive `lc > 0` | free (a factorization into irreducibles over ℤ is unique up to the pinned ordering; jets may use van Hoeij or anything else) |

Known cost cliff: Zassenhaus recombination is exponential in the worst case. Swinnerton–Dyer `SD_3` must pass in the test suite; `SD_4`+ is explicitly out of scope until a van Hoeij milestone (see §13).

Also, at this point move /lib/racoon-vectors.hoon into /tests/lib and update any path references in the test file. The vectors are now part of the test suite, not the library.

## 10. Jet-readiness obligations (Milestone A)

- Registration mirrors `urbit/numerics` `/lib/math.hoon` **exactly**: root `~%` named `%racoon`, nested `~%` per sub-core (`%nz`, `%qq`, `%zx`, `%mx`, `%qx`), per-arm `~/` hints. Read that file first; copy the working parent-axis pattern; do not improvise.
- Arms carrying `~/` hints: `nz`: `gcd egcd crt is-prime`; `zx`: `mul gcd pdiv res factor`; `mx`: `mul divmod gcd egcd powmod factor`; `qx`: `mul divmod gcd`.
- Battery freeze (R6): once a phase gate closes, hinted cores' arm sets and order are frozen for the milestone.
- Keep the canonical-form check O(1): non-emptiness plus trailing coefficient nonzero. This is the check B-jets will use to decide native-vs-fallback. Do not choose representations that make it more expensive.

## 11. Testing requirements

1. **Framework.** `/lib/test`, arms `++test-p0-*`, `++test-p1-*`, etc. Every §8 crash row has a dedicated expected-crash test.
2. **Reference vectors.** `tools/genvec.py` (SymPy as oracle: `sympy.gcd`, `sympy.resultant`, `sympy.factor_list`, `GF(p)` polys, `QQ`/`ZZ` domains) emits `lib/racoon-vectors.hoon` as typed constants, ≥ 40 cases per public arm, deterministic (fixed seed in script). Include adversarial families: zero and degree-0/1 polys; `x`, `x^k`; negative leading coefficients; non-primitive inputs; non-monic divisors; repeated factors; `p = 2`, `p = 3`, and a 61-bit prime; composite `n` for the mx arms that permit it; `gcd(0, 0)`; cyclotomics Φ₁…Φ₂₀ and `x^k - 1` for `k ≤ 24`; Mignotte-adjacent tight cases; Swinnerton–Dyer `SD_2` and `SD_3` for `factor:zx`.
3. **Property tests**, in-ship, `++og` with pinned literal seeds recorded in the test file. Sizes bounded (degree ≤ 32, coefficients < 2^64) to keep interpreted runtime tolerable. Minimum properties: ring axioms sampled (associativity, commutativity, distributivity); `eval` is a homomorphism; `divmod` reconstruction `a = q*b + r` with the degree bound; `egcd` Bézout identity and §7 cofactor bounds; constructed-gcd checks (`gcd(g*a, g*b)` is divisible by the normalized `g`); `res(a, b) = 0` iff `gcd` nonconstant (sampled); `factor` **exact reconstruction** — reassembled product equals input noun-for-noun. Reconstruction is the load-bearing factorization test; irreducibility of individual factors is certified by the SymPy vectors, not in-ship.
4. **Benchmarks.** `gen/racoon-bench` times `mul`/`gcd` at degrees 16/64/256 over a 61-bit 𝔽p, `gcd:zx` at degree 64 with 64-bit coefficients, `factor:zx` at degree 32. Output a plain table. No performance gates in Milestone A; record baselines in `README.md` — they are the denominator for Milestone B speedup claims.

## 12. Phase gates

A phase closes when: library compiles clean; all tests for this and prior phases green; vector minimums met; crash rows covered; bench baselines recorded; battery freeze applied; decision log updated. Phases land as separate reviewed changes — do not batch Phase 2 and 3 into one drop.

- **P0**: `nz`, `qq` complete.
- **P1**: `zx`/`mx` arithmetic complete (qx arithmetic may ride with P2).
- **P2**: division/GCD/resultants complete, including the modular `gcd:zx` with certification.
- **P3**: factorization complete; `SD_3` passes; exact-reconstruction property green at all sampled sizes.

## 13. Out of scope — hard fence

No floating point (numerics owns it). No multivariate polynomials, no Gröbner bases. No symbolic expression front end, no simplifier, no integration/Risch. No LLL / van Hoeij. No primality *proving*. No performance work beyond recording baselines. No C/Rust jets, no runtime modifications. No `%base` changes beyond adding the listed files. Milestone C candidates, for context only: van Hoeij recombination; real-root isolation via Sturm/Descartes (the "Real" in the backronym); sparse multivariate.

## 14. Escalation and decision authority

**Delegated** (proceed, note in decision log where non-obvious): private helper structure and naming; test-file internal organization; vector counts above minimums; script and README details.

**Escalate** (stop that thread, file an entry in `SPEC-QUESTIONS.md` with a proposed resolution, continue only on unblocked work): any change to §6–§10 pinned material — types, canonical conventions, crash rows, public signatures, pinned algorithms; reuse of kernel arms beyond R8's whitelist; `/lib/test` or `-test` failures you cannot resolve from source; out-of-loom conditions in tests; any place this spec appears mathematically wrong — bring the counterexample, that entry gets priority review.

Silence is not acceptance for pinned material. An unanswered question blocks its phase gate.

## 15. Style

Kernel style throughout: `::` comment header per arm stating the mathematical contract (domain, codomain, conventions, crash conditions); explicit `^-` on every arm; `?>` guards for preconditions; alphabetical arm order is *not* required — follow the §9 table order within each core; 80-column discipline; no `~|` (R3); no wet gates without justification (R7).

## 16. References

- von zur Gathen & Gerhard, *Modern Computer Algebra*, 3rd ed. Chapter map: Euclid/EEA §3; CRT and modular techniques §5; resultants, subresultants, Mignotte §6; fast multiplication §8 (Milestone B context); division §9; finite-field factorization §14; Hensel lifting and Zassenhaus §15; LLL §16 (out of scope).
- `urbit/numerics` — precedent for the whole shape: Hoon-normative library, jet registration in `/lib/math.hoon`, testing style, benchmark discipline.
- Davis, "Jet-Accelerated Code and the Co-Design Problem" (USTJ) — the three-valued jet contract this spec is written against.
- Davis, "A Deterministic Numerical Stack" (USTJ) — the sibling project; Lagoon's kind-dispatch informed the (rejected, for now) generic-ring design; concrete per-ring cores won on simplicity.

---

# Milestone C — real-root isolation

**Engineering Specification v0.2 — Milestone C, phase R: the Real in Real AlgebraiCs**

Milestone B (jets) is deferred; C proceeds ahead of it. This section
specifies one of §13's three candidates. The other two — van Hoeij
recombination and sparse multivariate — remain unspecified, and van Hoeij
additionally needs an LLL escalation before any code (§R7).

The library is named for real algebraic numbers and does not yet produce
any. This closes that.

## R1. Where it lives, and why not in `+zx`

**`/lib/racoon-roots`, a consumer.** `%zx` and `%qx` froze under R6 at
Milestone A's P2 gate, and adding an arm to either would move the battery
axes of arms that Milestone B jets resolve against. Nothing inside the
frozen library needs root isolation, so nothing needs it there.

This is now the fourth application of that rule — `/lib/racoon-fmt`,
`/lib/racoon-rs`, `/lib/racoon-fp3`, `/lib/racoon-zfac` — and Baloon's
resolved question B2. A frozen interface reopened for every good idea was
never frozen.

**Consequence, recorded rather than worked around:** the formal derivative
is `+zderiv` in `+pv`, private, so this library recomputes it in four
lines. That is a real duplication and the right trade against unfreezing
`%zx` for one arm. See `SPEC-QUESTIONS.md` R1.

**It consumes `/lib/racoon-zfac`.** Exact rational roots come from the
rational root theorem, whose candidate set is the divisors of the trailing
and leading coefficients — which is `+divisors:zfac`. Integer factorization
landing first is what makes §R3's exactness clause affordable.

## R2. Types

Declared locally, not in `sur/racoon.hoon`: §6 is pinned, and a consumer
adding to it would be an escalation for no gain. `$ord` from §6 is reused
as-is for sign tests, which is what it is for.

```hoon
::    $ivl: an isolating interval for exactly one real root.
::
::  Endpoints are canonical $frac.  lo <= hi always.  lo = hi means the
::  root is EXACTLY that rational and the interval is degenerate -- not an
::  approximation that happens to be tight.
+$  ivl  [lo=frac hi=frac]
::    $rrt: a real root, isolated, with its multiplicity in the input.
+$  rrt  [iv=ivl m=@ud]
```

## R3. Canonical conventions (normative)

The hard problem here is that **isolating intervals are not unique** — any
sufficiently small interval around a root isolates it. An arm that returned
"whatever the bisection produced" would have to be `pinned`, and every jet
would have to replicate the subdivision exactly. That is the wrong trade,
so the output is made canonical instead and every arm below is `free`.

| Item | Convention |
|---|---|
| `+bound` | The Cauchy bound `1 + max(\|a_i\|)/\|a_n\|` over `i < n`, as a `frac`. Pinned as a *value*, not an algorithm: every arm's canonical output is stated relative to it, so a different bound would give a different — equally valid, but different — answer |
| **Canonical interval** | Consider the infinite binary subdivision tree of `[−B, B]`. The nodes containing a given root α form a chain from the whole interval downward. **The canonical isolating interval for α is the shallowest node in that chain containing no other root.** Unique by construction, a function of the polynomial alone, and independent of how it was found |
| **Exact roots are exact** | A rational root is returned as a degenerate `[α α]`, never as an interval around it. Rational roots are found first, by the rational root theorem over `+divisors:zfac`; a subdivision node whose single root is one of them **collapses to that exact point** rather than being reported as a range. **Corrected from "divided out before any subdivision happens"** — dividing them out breaks pairwise disjointness, because a surviving irrational root's node can still contain a removed rational one. Collapsing the node instead keeps the products disjoint by construction, since the point replaces the node it sat in |
| **Half-open, and that is what makes it exact** | A node `(lo, hi]` splits into `(lo, mid]` and `(mid, hi]`, which partition it with no overlap and no gap — so a root can be neither double-counted nor lost between children, *including* one landing exactly on `mid`. A closed convention would need a special case there; this needs none |
| `+isolate` | Ascending by `+cmp:qq` on `lo`. Intervals are pairwise disjoint. Exactly one root per interval — that is the postcondition, not an aspiration |
| `+roots` | Ascending likewise, each carrying its multiplicity in the *input*. Obtained from `+sqfree:zx`: isolation runs on each squarefree factor, which is the only form Sturm is valid on |
| `+refine` | `[p iv k]` bisects `k` times, keeping the half that contains the root. Canonical given `k`, since the starting interval is canonical and bisection is deterministic. Returns a degenerate interval unchanged |
| `+sign-at` | `[p x] -> ord`, the sign of `p(x)` for rational `x`. `%eq` exactly when `x` is a root. Reuses §6's `$ord` |
| **Reference algorithm** | **Sturm sequences.** The chain is `p, p′, −rem(p, p′), …`; the root count in `(a, b]` is the drop in sign changes from `a` to `b`. Chosen over Descartes/VCA for the reference because it is simpler and more obviously correct, which is this project's stated order of priorities. Jets may use VCA, Descartes with Taylor shifts, or anything else — the output is canonical, so they need only agree on the answer |

## R4. Public API

| Arm | Signature | Notes |
|---|---|---|
| `bound` | `zol -> frac` | Cauchy bound; every root lies in `(−B, B)` |
| `deriv` | `zol -> zol` | Formal derivative. Duplicates private `+zderiv:pv`; see R1 |
| `sturm` | `zol -> (list zol)` | The Sturm chain of a squarefree `p` |
| `sign-at` | `[zol frac] -> ord` | |
| `count` | `[zol frac frac] -> @ud` | Distinct real roots in `(a, b]` |
| `nroots` | `zol -> @ud` | Distinct real roots, all of ℝ |
| `rational-roots` | `zol -> (list [r=frac m=@ud])` | Exact, ascending, via `divisors:zfac` |
| `isolate` | `zol -> (list ivl)` | Canonical isolating intervals, ascending |
| `roots` | `zol -> (list rrt)` | Isolation plus multiplicities, via `sqfree:zx` |
| `refine` | `[zol ivl @ud] -> ivl` | Bisect `k` times |

Every arm is **`free`**. There is no `pinned` column, by construction —
that is what §R3 buys.

## R5. Crash table (normative — every row gets a test)

| Arm | Condition | Behavior |
|---|---|---|
| any arm | `p = ~`, the zero polynomial | crash. Every real is a root; there is no list to return and no sentinel that would not be a lie — the same reasoning as `+factor:zfac` on 0 |
| `sturm` | `p` not squarefree | crash. The chain's root count is only valid there, and returning a silently wrong count is worse |
| `count` `refine` | `a > b`, or `lo > hi` | crash |
| `count` | no roots in the range | **no crash**: product is `0` |
| `isolate` `roots` `rational-roots` | `p` has no real roots | **no crash**: product is `~` |
| `isolate` `roots` | `p` is a nonzero constant | **no crash**: product is `~` |
| `refine` | degenerate interval | **no crash**: returned unchanged |

No `~|` anywhere (R3).

## R6. Phases

- **R0 — foundations.** `bound`, `deriv`, `sign-at`, `sturm`, `count`,
  `nroots`. This is the whole correctness core; everything after is
  bookkeeping on top of an exact root count.
- **R1 — exactness.** `rational-roots`. Depends on `/lib/racoon-zfac`.
- **R2 — isolation.** `isolate`, `roots`, `refine`.

## R7. Testing

1. **Oracles.** SymPy `Poly.count_roots`, `Poly.intervals`,
   `Poly.real_roots`, and `CRootOf` for exact comparison. **Verify each
   convention against the definition before pinning it** (§11.3): SymPy's
   `intervals()` does *not* use this section's canonical subdivision, so it
   is an oracle for the root *count* and for containment, **not** for the
   interval endpoints. Endpoints are checked structurally instead — each
   interval contains exactly one root by `+count`, they are disjoint and
   ascending, and no shallower dyadic node isolates.
2. **Cross-checks that need no oracle.** `nroots` ≤ `deg`; the multiplicities
   from `roots` sum to at most `deg`; `sign-at` differs at the two endpoints
   of every non-degenerate isolating interval; `refine` preserves
   containment and halves the width; `rational-roots` are genuine roots by
   `+eval:qx`; every rational root also appears in `roots` as a degenerate
   interval.
3. **Adversarial families.** Swinnerton–Dyer `SD_2` and `SD_3` — already in
   the corpus, and the point of them here is different: `SD_3` has eight
   real roots in a narrow band, which is precisely what defeats a careless
   isolator. Also: Wilkinson-style products of close linear factors,
   Chebyshev polynomials (all roots real, in `[−1, 1]`), cyclotomics (no
   real roots beyond ±1), polynomials with a rational root adjacent to an
   irrational one, repeated factors, and constants.
4. **Benchmarks.** `isolate` at degrees 8/16/32, and `SD_3`. Recorded in
   `README.md`, no gates.

## R8. Out of scope — hard fence

No complex roots. No numerical refinement to floating point — Lagoon owns
that, and the endpoints here stay exact rationals forever. No algebraic
number *arithmetic*: this isolates roots, it does not add or multiply them,
and a field ℚ(α) is a separate piece of work. No real closure, no
quantifier elimination, no Thom encodings. `+refine` narrows on demand and
that is the whole of the precision story.
