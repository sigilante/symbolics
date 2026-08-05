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

Known cost cliff: Zassenhaus recombination is exponential in the worst case. Swinnerton–Dyer `SD_3` must pass in the test suite; `SD_4`+ was declared out of scope until a van Hoeij milestone (see §13). **`SD_4` was measured and that claim is wrong — see §V0.** The cliff is real but sits one step further out than this line assumed.

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

No floating point (numerics owns it). No multivariate polynomials, no Gröbner bases. No symbolic expression front end, no simplifier, ~~no integration/Risch~~ — **the rational half is lifted, see §F; Risch, the expression front end, and the simplifier stand, and §F10 says why the last two cannot live here at all.** ~~No LLL / van Hoeij.~~ **Lifted — see §V.** This is a Milestone A fence, and §V supersedes it exactly as §R and §A supersede the real-root and algebraic-number lines above. No primality *proving*. No performance work beyond recording baselines. No C/Rust jets, no runtime modifications. No `%base` changes beyond adding the listed files. Milestone C candidates, for context only: van Hoeij recombination; real-root isolation via Sturm/Descartes (the "Real" in the backronym); sparse multivariate.

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

**Consequence, since resolved:** the formal derivative was `+zderiv` in
`+pv`, private, so this library recomputed it in four lines — the right
trade against unfreezing `%zx` for one arm alone. `SPEC-QUESTIONS.md` R1
recorded it with a revisit condition, and phase V1 met that condition by
opening `%zx` for a batch. `+deriv` is now public on `%zx` and this
library calls it; the arm is gone from §R4 below.

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
| any arm of this library | `p = ~`, the zero polynomial | crash. Every real is a root; there is no list to return and no sentinel that would not be a lie — the same reasoning as `+factor:zfac` on 0 |
| `sturm` | `p` not squarefree | crash. The chain's root count is only valid there, and returning a silently wrong count is worse |
| `count` `refine` | `a > b`, or `lo > hi` | crash |
| `count` | no roots in the range | **no crash**: product is `0` |
| `isolate` `roots` `rational-roots` | `p` has no real roots | **no crash**: product is `~` |
| `isolate` `roots` | `p` is a nonzero constant | **no crash**: product is `~` |
| `refine` | degenerate interval | **no crash**: returned unchanged |

No `~|` anywhere (R3).

## R6. Phases

- **R0 — foundations.** `bound`, `sign-at`, `sturm`, `count`, `nroots`
  (and `deriv`, until R1 promoted it to `%zx`). This is the whole correctness core; everything after is
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

---

# Milestone C — algebraic number arithmetic

**Engineering Specification v0.2 — Milestone C, phase A: arithmetic on real algebraic numbers**

Phase R isolates real roots; it does not add or multiply them, and §R8
fenced that out as separate work. This is that work.

The capability is: given two real algebraic numbers, produce their sum,
difference, product, and quotient **as real algebraic numbers**, exactly,
with no floating point anywhere. `sqrt 2 + sqrt 3` becomes a first-class
value rather than a polynomial someone had to know to write down.

## A1. Where it lives

**`/lib/racoon-alg`, a consumer**, importing `/lib/racoon` and
`/lib/racoon-roots`. Sixth application of the rule after `racoon-fmt`,
`racoon-rs`, `racoon-fp3`, `racoon-zfac`, and `racoon-roots`. `%zx` and
`%qx` stay frozen; nothing inside them needs this.

It reuses `$ivl` from `/lib/racoon-roots` rather than redeclaring it.

**It is a door, and this import list is why.** Its recombination step is
the sample rather than a seventh import, so a faster factorizer can be
bound from a desk this one does not know about — which is what
`/lib/baloon-alg` does with `+factor:vh`. See §A8 and R4.

## A2. Representation

```hoon
::    $anum: a real algebraic number.
::
::  .m is the MINIMAL polynomial: primitive, positive leading
::  coefficient, irreducible over Z.  .iv is the canonical isolating
::  interval of this root of m, exactly as +isolate:roots produces it.
+$  anum  [m=zol iv=ivl]
```

**This form is canonical, and that buys more than tidiness.** The minimal
polynomial of a real algebraic number is unique under those three
conditions, and §R3 already makes the isolating interval unique. So:

- **Equality is structural.** `=(a b)` decides it. No refinement loop, no
  tolerance, no separate `+equals` arm.
- **Every arm is `free`.** A jet may use any algorithm and must land on
  the same pair.

The price is that every operation must **reduce to the minimal
polynomial**, which means factoring (§A8). That is the central cost of
this design and it is paid deliberately: the alternative — carrying any
polynomial that happens to vanish at α — makes equality undecidable
without a gcd on every comparison, and makes nothing canonical.

## A3. Canonical conventions (normative)

| Item | Convention |
|---|---|
| **Minimal polynomial** | Primitive, `lc > 0`, irreducible over ℤ. Extracted from the resultant by `+firr:zx`, which returns `~[f]` exactly when `f` is already irreducible — so the common case costs one irreducibility test and no factorization |
| **Bivariate resultants by EVALUATION–INTERPOLATION** | `res:zx` is univariate over ℤ; the sum and product formulas need `Res_y` of polynomials in `ℤ[x][y]`, which Racoon cannot form symbolically and Baloon's polynomial-entry determinants cannot be reached (Baloon depends on Racoon, not the reverse). Instead: `Res_y` has degree at most `deg p · deg q` in `x`, so evaluate at that many integer points plus one — each evaluation is a *univariate* integer resultant — and interpolate over ℚ, then `+clear:qx`. **Only existing frozen arms are needed** |
| **Specialization is valid here** | Evaluation commutes with the resultant only when the degree in `y` does not drop at the evaluation point. For `q(x − y)` the leading `y`-coefficient is `±lc(q)`, constant in `x`, so it never drops. For `y^d · q(x/y)` it is `q(0)`, which vanishes only when `q = y`, i.e. `β = 0` — handled as a special case before any resultant is formed |
| **Sum, difference, product, inverse** | `α+β`: `Res_y(p(y), q(x−y))`. `α−β`: `α + (−β)`. `α·β`: `Res_y(p(y), y^deg q · q(x/y))`. `1/α`: the coefficient reversal of `p`. `−α`: `p(−x)`. Each yields a polynomial *having* the answer as a root; the minimal polynomial is the irreducible factor that does |
| **Root selection** | The resultant's root set is a superset of the answer. Refine `α` and `β` alternately, propagating through **interval arithmetic**, until the resulting box meets exactly one isolating interval of the minimal polynomial. Terminates because the roots are distinct and the box shrinks to a point |
| **Interval arithmetic** | Sum: `[lo₁+lo₂, hi₁+hi₂]`. Negation: `[−hi, −lo]`. Product: the min and max of the four corner products — **sign-aware, not `[lo₁·lo₂, hi₁·hi₂]`**, which is wrong whenever an interval straddles zero |
| `+cmp` | **Structural equality is tested FIRST.** Only then refine both until the intervals separate. Without that order the loop never terminates on equal inputs, which is the classic way this is written wrong |
| `+approx` | `[anum @ud] -> frac`, within `2^-k`. Pinned as the midpoint of the first canonical refinement whose width is at most `2^-k`, so the product is a function of the input and `k` alone |
| **Degeneracy to ℚ** | When the minimal polynomial is linear, the number *is* rational. `α − α`, `α · α⁻¹`, and `sqrt 2 · sqrt 2` must come back as exact rationals, not as degree-1 algebraic numbers wearing a disguise. `+to-q` produces `[~ r]` exactly then |

## A4. Public API

| Arm | Signature | Notes |
|---|---|---|
| `make` | `[zol ivl] -> anum` | Canonicalize: reduce to the minimal polynomial and re-isolate. The only entry point that accepts a non-minimal polynomial |
| `of-q` | `frac -> anum` | Embed a rational; `m` is linear |
| `to-q` | `anum -> (unit frac)` | `[~ r]` iff `deg m = 1` |
| `deg` | `anum -> @ud` | Degree of the extension ℚ(α) over ℚ |
| `approx` | `[anum @ud] -> frac` | Within `2^-k` |
| `cmp` | `[anum anum] -> ord` | Equality structural, order by refinement |
| `sign` `is-zero` | `anum -> ord` / `?` | |
| `neg` `inv` | `anum -> anum` | `inv` crashes on zero |
| `add` `sub` `mul` `div` | `[anum anum] -> anum` | `div` crashes on a zero divisor |
| `pow` | `[anum @s] -> anum` | Negative exponents via `inv` |
| `root` | `[anum @ud] -> (unit anum)` | The real `k`-th root, `~` when none exists |

Every arm is **`free`**.

## A5. Crash table (normative — every row gets a test)

| Arm | Condition | Behavior |
|---|---|---|
| `make` | `m = ~`, or `iv` holds no root of `m` | crash |
| `inv` `div` | the argument is zero | crash |
| `pow` | negative exponent of zero | crash |
| `root` | `k = 0` | crash |
| `root` | no real `k`-th root exists (even `k`, negative `α`) | **no crash**: product is `~` |
| `to-q` | the number is irrational | **no crash**: product is `~` |

No `~|` anywhere (R3).

## A6. Phases

- **A0 — representation.** `$anum`, `make`, `of-q`, `to-q`, `deg`,
  `approx`, `cmp`, `sign`, `is-zero`. No resultants yet; `make` is where
  the factor-and-select machinery first appears.
- **A1 — unary.** `neg`, `inv`, `pow`. Both formulas are coefficient
  manipulations, so this phase needs no bivariate resultant at all and is
  a cheap check on `make`.
- **A2 — binary.** `add`, `sub`, `mul`, `div`. The evaluation–
  interpolation resultant and root selection land here.
- **A3 — `root`.** The real `k`-th root, via `Res_y(p(y), y^k − x)`.

## A7. Testing

1. **Oracle.** SymPy `minimal_polynomial`, which is exactly the canonical
   form §A2 pins. Verified before pinning, per §11.3:
   `minimal_polynomial(sqrt 2 * sqrt 3)` is `x² − 6`, **degree 2 where the
   resultant has degree 4** — so the factor-and-select step is load-bearing
   and not decoration. A test suite that only used degree-preserving cases
   would pass with that step deleted.
2. **Cases that must degenerate.** `α − α = 0`, `α · α⁻¹ = 1`,
   `sqrt 2 · sqrt 2 = 2`, `sqrt 2 + (−sqrt 2) = 0`. Each must produce an
   exact rational through `+to-q`, not a degree-1 `anum`. These are the
   cases where a wrong implementation looks right until it is compared.
3. **Cross-checks needing no oracle.** `approx` brackets the value
   (`+count:roots` on the minimal polynomial, exactly — no float
   comparison); `add` is commutative and associative on triples;
   `mul`/`div` and `add`/`sub` invert each other; `cmp` is a total order
   consistent with `approx`; `deg(α+β)` divides `deg α · deg β`.
4. **Adversarial.** `sqrt 2 + sqrt 3` (degree 4, the SD_2 polynomial);
   `sqrt 2 · sqrt 3 = sqrt 6` (degree collapse); the golden ratio;
   `2^(1/3)` and its powers; nested radicals; two numbers with the *same*
   minimal polynomial but different intervals, which must never compare
   equal.
5. **Benchmarks.** `add` and `mul` at degrees 2, 3, and 4, and the point
   where §A8 bites. Recorded, no gates.

## A8. The cost cliff — read this before starting A2

**Measured, and this section is wrong in the same way §9 was.** Phase A
was built, phase V1 landed, and both rungs were then timed with
`/gen/racoon-alg-bench`:

| the sum | degrees | `factor:zx` | van Hoeij |
|---|---:|---:|---:|
| `(√2+√3) + (√5+√7)` → `SD_4` | 4 + 4 | 3.34 s | 3.34 s |
| `(√2+√3+√5+√7) + √11` → `SD_5` | 16 + 2 | 281.9 s | 90.4 s |

**Degree-4 arithmetic spends 0.3 s of its 3.34 s on the factorization.**
The rest is the bivariate resultant — `deg p · deg q + 1` univariate
resultants and an interpolation — which van Hoeij does not touch. The
argument below correctly identifies degree 16 as where `SD_4` sits and
incorrectly concludes that factoring is therefore what degree-4
arithmetic costs. The cliff is one rung further out, at degree 32, where
Zassenhaus was 202.5 s of the 281.9 s and van Hoeij does that part in
9.4 s.

Kept rather than patched, for the reason §V0 gives: this changes what a
reader should conclude, and it is the same lesson twice — **a bottleneck
named from theory is a claim, not a fact.** Theory names the exponential
step because that is the step theory notices.

The concluding paragraph held up: the factorization *was* built as a
single call, and swapping it took one arm. `/lib/racoon-alg` factors
through `+facz`, whose recombination step is **the library's door
sample** rather than an import — defaulting to `firr:zx`, and bound to
`factor:vh` by `/lib/baloon-alg`. §A1's dependency list therefore still
holds exactly as written. See `racoon/SPEC-QUESTIONS.md` R4.

---

`deg(α+β)` and `deg(α·β)` are at most `deg α · deg β`. Two degree-4
numbers therefore give a resultant of **degree 16**, and extracting the
minimal polynomial means factoring it over ℤ.

§9 records that `factor:zx` uses Zassenhaus recombination, exponential in
the worst case, and that **Swinnerton–Dyer `SD_4` and beyond are
explicitly out of scope until a van Hoeij milestone.** `SD_4` has degree
16. So arithmetic on degree-4 algebraic numbers lands precisely on the
cliff §9 already fenced off.

This is not a reason to defer phase A — degrees 2 and 3 are the common
case, cover every quadratic and cubic irrational, and are unaffected. It
is a reason to state plainly that **van Hoeij is a dependency of phase A
at higher degrees, not an optional optimization**, and to build A2 so the
factorization step is a single call that a better algorithm can replace.

Two mitigations belong in the implementation: take the squarefree part
before factoring, and try `+firr:zx` first, since a resultant that is
already irreducible needs no factorization at all.

## A9. Out of scope — hard fence

No complex algebraic numbers; this is the *real* line, as the backronym
says. No general number fields, primitive-element computation, or field
towers — a ℚ(α) representation with polynomial arithmetic mod the minimal
polynomial is a legitimate companion to this one and is *not* specified
here; `/lib/racoon-fp3` already shows the shape over 𝔽p. No Galois
theory, no splitting fields. No real closure, no quantifier elimination,
no Thom encodings, no cylindrical algebraic decomposition. No symbolic
radical *expressions*: this computes with `sqrt 2` as a number, and never
produces the string "√2" — that is a printing concern and belongs in a
`-fmt` consumer.

---

# Milestone C — van Hoeij recombination

**Engineering Specification v0.2 — Milestone C, phase V: lattice reduction and van Hoeij**

§9 records the cost cliff: `factor:zx` recombines Hensel-lifted modular
factors by **Zassenhaus**, enumerating subsets, which is exponential in
the number of modular factors. `SD_4` and beyond are out of scope because
of it, and §A8 showed the same wall stops algebraic arithmetic at degree
4. This replaces that step.

## V0. The benchmark was wrong, and it was measured

§9 said `SD_4` and beyond were out of scope pending van Hoeij, and §A8
built on that. **Measured before building anything, `factor:zx` factors
`SD_4` correctly in 302 ms.** The premise was false.

The reason is that Zassenhaus's cost depends on the number of *modular*
factors `r`, not the degree, and it enumerates subsets only up to
`⌊r/2⌋` because the complement rule covers the rest:

| | degree | `r` mod a good prime | subsets tried | `factor:zx` |
|---|---:|---:|---:|---|
| `SD_3` | 8 | 4 | 10 | fast |
| `SD_4` | 16 | **8** | **162** | **302 ms** |
| `SD_5` | 32 | **16** | **39,202** | **204 s** — 676× |
| `SD_6` | 64 | 32 | ~2.1 × 10⁹ | out of reach |

Both were run to completion and both answers are correct: `SD_4` and
`SD_5` are irreducible, and `factor:zx` says so.

`SD_4` has degree 16 but only eight modular factors, because every
Swinnerton–Dyer polynomial splits into pieces of degree at most 2 — its
Galois group is elementary abelian of exponent 2, so no Frobenius element
has order above 2. Degree 16 over degree-2 pieces is `r = 8`, not 16. The
original line conflated the two.

**The retargeted claim: `SD_5` at 204 s is what van Hoeij has to beat, and
`SD_6` is what it has to make possible at all.** 242× the subsets and
eighteen-digit coefficients gave 676× the wall time, which is the
exponential showing itself; one more step multiplies the subset count by
another 53,000 and ends the line entirely. That is the benchmark §V7 now
names.

This correction is recorded rather than quietly patched because it
changes what phase V is *for*, and because the general lesson is the
project's own §11.3 in a new place: **a fence stated from theory and
never measured is a claim, not a fact.**

## V1. Where it lives

**`baloon/desk/lib/vanhoeij.hoon`, a consumer importing BOTH libraries.**
Escalation R4, decided: LLL operates on integer lattice bases, which is
exactly `$zmat`, and Baloon Milestone C already supplies `det`, `mul`,
`rank`, and the Hermite form over ℤ. Racoon cannot import Baloon — the
dependency runs the other way — so putting LLL in Racoon would mean
duplicating all of it. It goes on the Baloon side instead, where both
libraries are in scope, and Racoon stays the lower layer.

**Both §13 fences are lifted** (`raccoon-spec.md` and `baloon-spec.md`),
recorded there and in `racoon/SPEC-QUESTIONS.md` R4. They were Milestone A
fences; this section supersedes them.

## V2. LLL — and the one `pinned` arm outside Racoon

| Item | Convention |
|---|---|
| `+lll` | `zmat -> zmat`. An LLL-reduced basis of the **same lattice**. Requires full row rank, asserted |
| **`pinned`, not `free`** | A lattice has *many* LLL-reduced bases, so the output is underdetermined by the specification and a jet cannot be allowed to pick a different one. This is the first `pinned` arm outside Racoon's five, and it is pinned for the same reason `egcd:nz` is: the answer is not unique, so the *procedure* is the contract |
| **What is pinned, exactly** | δ = 3/4; classic Lenstra–Lenstra–Lovász; size-reduce row `k` against rows `k−1 … 0` in **descending** index order; rounding to the nearest integer with **ties away from zero**; start at `k = 1` (zero-indexed); on a swap set `k = max(k−1, 1)`. The *method of computing the Gram–Schmidt data is NOT pinned* — exact rational GSO and an incrementally updated one are mathematically equal, so they yield the same reductions and the same output |
| **Exact rationals throughout** | No floating point. The classic LLL failure mode is a GSO computed in floating point drifting until the Lovász test flips wrongly; here it cannot happen |

**`+lll` being `pinned` does not make `factor` pinned.** Every candidate
factor van Hoeij proposes is verified by trial division, so the
factorization is canonical no matter which reduced basis LLL returned.
The pinning stops at the lattice arm.

## V3. Van Hoeij recombination

For `f ∈ ℤ[x]` squarefree with modular factors `g_1 … g_r` lifted to
`p^a`, a true factor `F` satisfies `F = lc_F · ∏_{i∈S} g_i mod p^a` for
some `S ⊆ {1..r}`. Write `S` as a 0-1 vector `v ∈ {0,1}^r`.

**The linear condition.** For monic `g`, the power sums `s_j` of its
roots are computable from its coefficients by Newton's identities, and
they are additive over products: `s_j(∏_{i∈S} g_i) = Σ_{i∈S} s_j(g_i)`.
Since `F` has integer coefficients, its power sums are **integers of
bounded size** — bounded by `n · B^j` for a root bound `B`. So

```
Σ_i v_i · s_j(g_i)  ≡  (a small integer)   mod p^a
```

which is a knapsack condition, and the 0-1 solutions are **short vectors**
in the lattice generated by

```
[  I_r        C   ]        C the r×m matrix of scaled power sums
[  0     p^a · I_m ]
```

LLL-reduce, read the 0-1 patterns off the short vectors, and verify.

## V4. Correctness does not depend on the lattice

**This is the load-bearing design decision.** Every candidate subset,
however it was proposed, is confirmed by **trial division into `f`**, and
if the lattice pass fails to produce a complete factorization the
algorithm **falls back to Zassenhaus enumeration** over whatever factors
remain.

So the lattice step is an *accelerator*, never an oracle. A bug in the
bound, the scaling, the choice of `j`'s, or the LLL itself can make this
slower; it cannot make it wrong. That is what makes a heuristic-shaped
algorithm safe to pin as `free`, and it is the only reason phase V is
approachable at all.

## V5. Crash table (normative)

| Arm | Condition | Behavior |
|---|---|---|
| `lll` | empty basis, or rows of differing length | crash |
| `lll` | rows not linearly independent | crash — asserted through `rank:zm` |
| `factor` | `f = ~` | crash |
| `factor` | `f` not squarefree | crash — recombination is defined on distinct factors |

No `~|` anywhere.

## V6. Phases

- **V0 — LLL.** Self-contained, independently useful, and verifiable
  without van Hoeij existing.
- **V1 — recombination.** Power sums, the lattice, extraction, trial
  division, and the Zassenhaus fallback.

**Both are built.** `SD_5` factors in 9.42 s against Zassenhaus's
202.5 s, which is the §V0 target beaten by 21.5×; the §V7.5 table is in
`baloon/README.md` and `/gen/baloon-vh-bench` reproduces it. The first
consumer is `/lib/racoon-alg`, whose one factorization call takes
`+factor:vh` as a door sample — bound by `/lib/baloon-alg`, so that
Racoon's desk keeps building alone. See §A8, which the same measurement
corrected.

## V7. Testing

1. **LLL is verified STRUCTURALLY, not against another program.** SymPy
   has `DomainMatrix.lll()`, but an LLL-reduced basis is **not unique** —
   two correct implementations at the same δ can return different bases —
   so matching its output is neither necessary nor sufficient. §11.3 says
   confirm a convention before pinning it against a tool; here the
   conclusion is that the tool is the wrong oracle. Instead check the
   definition, which is exact and complete:
   - **size-reduced**: `|μ_ij| ≤ 1/2` for all `j < i`
   - **Lovász**: `‖b*_k‖² ≥ (3/4 − μ²_{k,k−1})·‖b*_{k−1}‖²`
   - **same lattice**: `hnf:zm` of the input equals `hnf:zm` of the
     output. This needs no oracle at all, and is exactly the check
     Baloon's Milestone C made possible
   Any basis satisfying all three *is* an LLL-reduced basis of that
   lattice. That is the whole specification.
2. **Determinant invariance.** For a square basis, `|det:zm|` is
   unchanged — the transform is unimodular.
3. **Van Hoeij against Zassenhaus.** The two must agree on every input,
   which makes `factor:zx` itself the oracle: it is already verified
   against SymPy over the Milestone A corpus.
4. **The point of the exercise.** `SD_5`, not `SD_4` — see §V0 for why the
   original target was wrong.
5. **Benchmarks.** `SD_3` and `SD_4` both ways, recorded in the README.
   This is the one place in the project where a speed difference is the
   deliverable rather than a footnote.

## V8. Out of scope — hard fence

No floating-point or heuristic LLL variants; exact rationals only. No
BKZ, no deep insertion, no block reduction. No lattice cryptography, no
CVP or SVP solvers beyond what recombination needs. No multivariate or
algebraic-function-field factorization.

---

# Milestone C — the rational function field

**Engineering Specification v0.2 — Milestone C, phase F: rational
functions, their integration, and the Laplace transform**

§13 fences out "integration/Risch" as a Milestone A boundary. This
section supersedes the *rational* half of it, exactly as §V superseded
the LLL line: everything below is closed-form, decidable, and reachable
from arms that already exist. The transcendental half — `exp`, `log`,
`sin` as symbols, and a general simplifier — stays fenced and is
addressed in §F9.

## F0. Why this is reachable now, and what it is worth

Integration of rational functions needs exactly four things: polynomial
GCD, squarefree decomposition, resultants, and factorization over ℚ. All
four are in the frozen library, and phase A added the fifth thing the
logarithmic part needs — **real algebraic numbers to name the roots of
the Rothstein–Trager resultant.** Nothing here requires a primitive that
does not exist.

The reach is larger than "integrate a rational function" suggests. For
linear systems with constant coefficients — which is most of what a
Mathcad-style tool is asked — the Laplace transform of the answer *is* a
rational function, partial fractions *is* the inverse transform, and the
characteristic polynomial is `charpoly:qm` followed by `factor:zx`.
Transfer functions, poles and zeros, step responses, and constant-
coefficient ODEs are all one field's arithmetic.

**Every arm is `free`.** `$rfun` in lowest terms with a monic
denominator is a unique mathematical object, and so is the exponential
polynomial of §F5. This is worth stating early because it is exactly
what phase (B) — symbolic expressions — will *not* be able to promise;
see §F9.

## F1. Where it lives

**Two consumer libraries, both importing `/lib/racoon` and nothing from
Baloon:**

| | |
|---|---|
| `/lib/racoon-rf` | the field, decomposition, and integration — phases F0–F2 |
| `/lib/racoon-lt` | the Laplace transform and the exponential-polynomial class — phase F3 |

Seventh and eighth applications of the consumer rule after `racoon-fmt`,
`racoon-rs`, `racoon-fp3`, `racoon-zfac`, `racoon-roots`, and
`racoon-alg`. `%zx` and `%qx` stay frozen; nothing inside them needs
this.

**Both are doors over their factorization step**, per the pattern R4
settled for `/lib/racoon-alg`: the sample is `fir=$-(zol (list zol))`,
"primitive squarefree polynomial to its irreducible factors", defaulting
to `firr:zx`. A Baloon-side `/lib/baloon-rf` binds `factor:vh`. This is
not decoration — partial fractions factors the denominator, which is the
same cost cliff §V0 measured, and a denominator with sixteen modular
factors is not exotic.

**The binding must be threaded, and this is the trap.** `/lib/racoon-rf`
calls `/lib/racoon-alg` for root selection, and `racoon-alg` is a door
over the *same* sample. Passing `~(. al fir)` rather than `al` is
normative: a caller who binds the fast factorizer at the top and gets the
slow one three layers down has been silently given the wrong performance
and no error.

## F2. Representation

```hoon
::    $rfun: a rational function over Q.
::
::  .num and .den are coprime, .den is MONIC and nonzero.  Zero is
::  [~ ~[[--1 1]]], that is 0/1.
+$  rfun  [num=qol den=qol]
```

**This form is canonical**, which buys the same two things §A2 bought:
`=(a b)` decides equality with no normalization pass, and every arm is
`free` so a jet may use any algorithm. Monic-denominator plus coprime is
the unique representative of an element of ℚ(x); nothing else is.

## F3. Canonical conventions (normative)

| Item | Convention |
|---|---|
| **Reduction** | Every arm produces lowest terms with a monic denominator. `+new` is the only arm accepting an unreduced pair, mirroring `+canon` in `%zx` and `+make` in `/lib/racoon-alg` |
| **Zero and one** | `0/1` and `1/1`. A zero numerator forces `den = ~[1]`, so zero has one representative |
| **Degree** | `+deg` produces `@s`, `deg num - deg den`, which is negative for a proper fraction. The degree of zero crashes, as `deg:zx` does |
| `+deriv` | Quotient rule, then reduce. Note the denominator of `(u/v)'` is `v²`, which is **not** in lowest terms in general — the reduction is not optional |
| `+eval` | `[rfun frac] -> frac`. Crashes at a pole; see §F4 |
| **Squarefree partial fractions** | `+pfrac` decomposes against the *squarefree* factorization of the denominator, which needs no irreducible factorization and is therefore cheap and always available. This is the form Hermite reduction consumes |
| **Full partial fractions** | `+pfrac-full` decomposes against the irreducible factorization over ℚ. Ordering is pinned: ascending by `pcmp:zx` on the denominator base, then ascending by power. Without a pinned order the output is not canonical and the arm could not be `free` |
| **Bezout, not undetermined coefficients** | Splitting `a/(b·c)` with `gcd(b,c) = 1` uses the extended Euclidean algorithm on polynomials, derived in the consumer from `divmod:qx`. Solving a linear system for the coefficients would work and would drag Baloon in for nothing |
| **Hermite reduction** | The rational part of the integral. Produces `[rat=rfun log=rfun]` where `log` has a squarefree denominator, so what remains is purely logarithmic |
| **Rothstein–Trager, by residue rather than by resultant** | The logarithmic part. For squarefree `d` with irreducible factor `g`, every root `α` of `g` has residue `a(α)/d'(α)`, and those residues are all one **rational** `c` exactly when `a·(d')⁻¹ mod g` is the constant `c`. Testing each factor directly avoids forming `Res_x(a - t·d', d)` at all — no bivariate resultant, no interpolation, no second factorization. Irrational residues are out of range; see §F6 |
| **The constant of integration is 0** | `+integrate` produces the antiderivative vanishing at no particular point; the constant is pinned to zero so the product is a function of the input alone |

## F4. Public API

`/lib/racoon-rf`:

| Arm | Signature | Notes |
|---|---|---|
| `new` | `[qol qol] -> rfun` | Reduce. The only arm accepting an unreduced pair |
| `of-q` `of-p` | `frac -> rfun` / `qol -> rfun` | Embed a constant, embed a polynomial |
| `zero` `one` | `rfun` | |
| `is-zero` `deg` | `rfun -> ?` / `rfun -> @s` | |
| `add` `sub` `mul` `div` | `[rfun rfun] -> rfun` | `div` crashes on a zero divisor |
| `neg` `inv` | `rfun -> rfun` | `inv` crashes on zero |
| `pow` | `[rfun @s] -> rfun` | Negative exponents via `inv` |
| `deriv` | `rfun -> rfun` | |
| `eval` | `[rfun frac] -> frac` | Crashes at a pole |
| `pderiv` | `qol -> qol` | The formal derivative in ℚ[x]. Exposed because `%qx` has no `+deriv` — §R1 promoted one to `%zx` only — and every caller of `+integrate` needs it to check the answer |
| `sqf-den` `fac-den` | `qol -> (list [p=qol m=@ud])` | The squarefree and irreducible factorizations of a denominator. `sqf-den` needs no factorization at all and is what Hermite consumes |
| `poles` | `rfun -> (list [p=qol m=@ud])` | `fac-den` of the denominator — the factorization made visible, since a caller who wants it should not have to redo it |
| `recombine` | `pfd -> rfun` | Sum a decomposition back up. Public because it is the property test worth having and a caller should not write it twice |
| `pfrac` | `rfun -> [p=qol ts=(list [n=qol d=qol e=@ud])]` | Polynomial part plus squarefree terms `n/d^e` |
| `pfrac-full` | `rfun -> [p=qol ts=(list [n=qol d=qol e=@ud])]` | Same, against irreducible `d` |
| `hermite` | `rfun -> [rat=rfun log=rfun]` | The rational part, and what is left |
| `integrate` | `rfun -> (unit [rat=rfun ls=(list [c=frac a=qol])])` | `rat` plus a sum of `c · log(a)`. Coefficients are **rational**, not `$anum` — §F6 says why. `~` when a residue is not |

`/lib/racoon-lt`: see §F5.

Every arm is **`free`**.

**Delegated helpers, not API.** `qone`, `pone`, `monic`, `exact`,
`ppow`, `to-z`, `of-z`, `pegcd`, `psort`, `split`, `expand`, `pf`,
`terms`, `pint`, and `residue` exist in the same door and are reachable
— a door has no private chapter, only a `+|` convention — but they are
delegated in §14's sense and may change without escalation. The library
header lists both sets so the boundary is stated rather than inferred.

## F5. The exponential polynomial, and why the transform closes

Inverse Laplace of a rational function is not a rational function, so
phase F3 needs one more type. It does not need a general expression
tree, because the class that is closed under differentiation,
integration, and the Laplace transform is small and nameable:

**The obvious representation is wrong, and this section records why
before anyone writes it.** The first form of this table was

```hoon
+$  eterm  [c=anum k=@ud s=anum w=anum tr=?(%cos %sin)]
```

with `$anum` coefficients, on the reasoning that σ and ω are real
algebraic and `/lib/racoon-alg` names them. It does. The problem is the
**coefficient field of the transform**: `L{e^{σt}} = 1/(s - σ)`, which is
not a rational function over ℚ when σ is irrational. So `+laplace` would
not land in `$rfun` at all, and the two arms would not compose.

The fix is to notice what the inverse transform of a rational function
over ℚ actually produces. With linear and quadratic factors only,
completing the square gives **σ and ω² both rational** — only ω itself is
irrational. And the sine term always arrives carrying a compensating
`1/ω`, because that is what differentiating the quadratic contributes. So
normalize the basis to absorb it:

```hoon
::    $eterm: c · t^k · e^(sig·t) · cos(sqrt(wsq)·t)          when %cos
::            c · t^k · e^(sig·t) · sin(sqrt(wsq)·t)/sqrt(wsq) when %sin
+$  eterm  [c=frac k=@ud sig=frac wsq=frac tr=?(%cos %sin)]
::    $expo: a finite sum of them, sorted, no zero coefficients
+$  expo  (list eterm)
```

**Every coefficient is now rational**, both transforms land where they
should, and the class is still closed under differentiation and
integration. `wsq = 0` with `tr = %cos` is the pure exponential case,
since `cos 0 = 1`; the `%sin` convention degenerates continuously there
too, since `sin(ωt)/ω → t` as `ω → 0`, which is the same `t^k` ladder the
repeated-root case walks.

`/lib/racoon-lt` therefore needs **no algebraic numbers at all** and does
not import `/lib/racoon-alg`. Sorting and zero-stripping are pinned, so
`$expo` is canonical and the arms stay `free`.

**Nothing here is complex.** A rational denominator's non-real roots come
in conjugate pairs, and each pair contributes one real term. Complex
algebraic numbers stay fenced by §A9 and are not needed — and after this
correction, neither are real ones.

| Arm | Signature | Notes |
|---|---|---|
| `canon` | `expo -> expo` | Sort, combine like terms, drop zero coefficients. The only arm accepting an unsorted or redundant list |
| `laplace` | `expo -> rfun` | **Total.** Each term transforms to a rational function and they sum. `L{t^k f} = (-1)^k F^(k)`, so the `t^k` ladder is `k` applications of `deriv:rf` rather than a closed formula |
| `inverse` | `rfun -> (unit expo)` | `~` exactly when §F6's condition fails. Repeated poles included, at any multiplicity |
| `ederiv` | `expo -> expo` | The class is closed under `d/dt`, so this cannot fail |
| `eadd` `escale` | `[expo expo] -> expo` / `[expo frac] -> expo` | |
| `solve-ode` | `[qol (list frac)] -> (unit expo)` | Constant-coefficient homogeneous, given the characteristic polynomial and initial conditions |

`integrate` on `$expo` is **not built**: it is the inverse of `ederiv`
and wants solving rather than substituting, which is the same shape as
the repeated-pole expansion and belongs with it.

## F6. What is out of range, and how a caller finds out

`+inverse` and `+integrate` produce `~` rather than crashing, because
being out of range is a property of the *input* that the caller could not
reasonably have checked in advance. The two arms have **different**
conditions and they are not the same fence.

### `+integrate`: the residues must be rational

**This section was wrong when it was written, and is corrected rather
than quietly narrowed.** It said real algebraic residues were in range,
on the grounds that `/lib/racoon-alg` can name them. Naming them was
never the problem. The log *argument* is `gcd(a - c·d', d)` computed over
**ℚ(c)[x]**, and polynomial arithmetic over an algebraic extension of ℚ
does not exist in this project — `/lib/racoon-fp3` has that shape for
𝔽p and nothing has it for ℚ. So the reachable class is the **rational**
residues.

The condition is decidable per irreducible factor `g` of the squarefree
denominator, and needs only the extended Euclidean algorithm: `a·(d')⁻¹
mod g` is either a constant, and then that constant is the residue, or it
is not, and then the residues genuinely differ between conjugate roots.

That class is larger than "the denominator splits into linear factors":
`∫ 2x/(x² + 1)` has residue 1 at both roots and comes back as
`log(x² + 1)`. What it excludes is `∫ 1/(x² + 1)` — the arctangent, whose
residues are `∓i/2` — and every case like it.

Lifting this wants either Lazard–Rioboo–Trager or a RootSum
representation of the answer, and both are **new specification, not new
code**. Neither is in scope here.

### `+inverse`: the poles must be nameable in ℝ

Unaffected by the above, because it needs no arithmetic in an extension —
only σ and ω, which come from a rational quadratic by completing the
square. Factor the denominator over ℚ; each irreducible factor `g` is in
range when

- `deg g = 1` — a real root, trivially; or
- `deg g = 2` — the real quadratic *is* the factor, so a negative
  discriminant is fine; or
- `(count:roots g lo hi) = deg g` over a bound containing every root —
  all roots real, and `/lib/racoon-alg` names them.

An irreducible factor of degree ≥ 3 with non-real roots is the whole of
what is excluded. Naming its roots needs **complex** root isolation,
which §A9 fences and this section does not lift. It excludes the inverse
transform of `1/(s⁵ + s + 1)`; it excludes nothing that factors into
linears and quadratics over ℚ, which is every transfer function anyone
writes by hand.

## F7. Crash table (normative — every row gets a test)

| Arm | Condition | Behavior |
|---|---|---|
| `new` | `den = ~` | crash |
| `inv` `div` | the argument is zero | crash |
| `pow` | negative exponent of zero | crash |
| `deg` | the argument is zero | crash |
| `eval` | the point is a pole | crash |
| `integrate` | a residue is not rational | **no crash**: product is `~` |
| `inverse` | §F6's condition fails | **no crash**: product is `~` |
| `solve-ode` | wrong number of initial conditions | crash |
| `solve-ode` | the characteristic polynomial is out of §F6's range | **no crash**: `~` |

No `~|` anywhere (R3).

## F8. Phases

- **F0 — the field.** `$rfun`, `new`, arithmetic, `deriv`, `eval`, `deg`.
  No factorization anywhere, so this phase is verifiable on its own and
  the door's sample is never read.
- **F1 — decomposition.** `poles`, `pfrac`, `pfrac-full`. The first
  phase that factors, and therefore the first that can be slow.
- **F2 — integration.** `hermite`, then Rothstein–Trager and
  `integrate`. Depends on `/lib/racoon-alg`.
- **F3 — transforms.** `$expo`, `laplace`, `inverse`, `solve-ode`, in
  `/lib/racoon-lt`. **Built.** `+laplace` is total; `+inverse` handles
  linear and quadratic irreducible factors at **any multiplicity**. The
  repeated-quadratic expansion is the recurrence

  ```
  P_1 = cos(ωt)          Q_1 = sin(ωt)/ω
  P_(j+1) = t·Q_j / 2j
  Q_(j+1) = [(2j-1)·Q_j - t·P_j] / 2jw
  ```

  where `P_j = L⁻¹{s/(s²+w)^j}` and `Q_j = L⁻¹{1/(s²+w)^j}`. The second
  falls out of `d/ds[s/q^j]` once `s²` is rewritten as `q - w`, which is
  what leaves a `w` in the denominator rather than an `s` — and is why
  §F5's normalized sine keeps every coefficient rational here too.

  Only `integrate` on `$expo` remains: it is the inverse of `ederiv` and
  wants solving rather than substituting.

## F9. Testing

1. **Integration is verified by differentiating the answer.** An
   antiderivative is not unique — the constant, and every `log(a)` term
   up to the sign and scale of `a` — so SymPy's form is neither
   necessary nor sufficient, exactly as §V7.1 concluded for LLL. The
   definition is exact and complete instead: `deriv(integrate(f))` must
   equal `f`, over `$rfun` for the rational part and by re-deriving the
   logarithmic part symbolically. **This needs no oracle at all.**
2. **Partial fractions IS canonical once §F3 pins the order**, so it can
   be checked against SymPy's `apart` — after confirming the convention
   agrees, per §11.3, and recording what was confirmed.
3. **The transform round-trips.** `inverse(laplace(e))` is `e` on the
   whole exponential-polynomial class, and `laplace(inverse(f))` is `f`
   whenever `inverse` produced a value. Both are oracle-free.
4. **Cross-checks needing no oracle.** `deriv` obeys the product and
   quotient rules on random pairs; `pfrac` recombines to its input;
   `eval` commutes with the field operations away from poles;
   `integrate` of a proper fraction with a squarefree denominator has an
   empty rational part.
5. **Adversarial.** A denominator that is a perfect power; a numerator
   whose degree exceeds the denominator's; `1/(x² + 1)`, whose residues
   are not real but whose *integral* is — the arctangent case, which is
   the one a naive Rothstein–Trager gets wrong by returning `~`;
   repeated roots in `solve-ode`, which give the `t^k` factors; a
   degree-5 irreducible with one real root, which must produce `~` from
   `+inverse` and not a wrong answer.
6. **Benchmarks.** `integrate` at denominator degrees 4, 8, and 16, both
   factorizer bindings, through `scripts/bench.sh`. Recorded, no gates.

## F10. Out of scope — hard fence

No `exp`, `log`, `sin`, or `cos` as **symbols**: they appear only as the
structured `$expo` of §F5 and as the `log(a)` terms of `+integrate`,
both of which are closed classes rather than an expression language. No
symbolic expression tree, no simplifier, no pattern matching or
rewriting — that is phase (B), it is a different contract (see below),
and it does not live in Racoon.

No Risch algorithm and no transcendental integration. No definite
integration, no improper integrals, no contour methods. No Fourier
transform: it needs either complex algebraic numbers or a distribution
theory, and both are out. No complex algebraic numbers — §A9 stands, and
§F6 states precisely what that costs.

No multivariate rational functions. No differential equations beyond
constant coefficients — variable coefficients need power series or
differential Galois theory, and neither is specified here.

No polynomial arithmetic over an algebraic extension of ℚ. That is the
one absence §F6 turned into a visible limit, and it is named here so
that lifting it is recognised as its own piece of work rather than a
patch to `+integrate`.

**The reason phase (B) cannot be a section of this document.** Racoon's
whole design rests on canonical outputs: unique objects, structural
equality, every arm `free`. A symbolic expression language cannot have
that property. By Richardson's theorem, deciding whether an elementary
expression is identically zero is **undecidable**, so there is no
canonical form to name and no `=(a b)` that decides equality. Every
simplifier arm would have to be `pinned` — the procedure becoming the
contract, as it is for `egcd:nz` and `lll` — which inverts this
project's disposition rather than extending it. That belongs in a
sibling with its own spec, standing on this one the way Baloon does.

**That sibling is named Calhoon.** It is not specified here and no arm
of this document depends on it; the name is recorded so that §F10's
fence has something to point at.
