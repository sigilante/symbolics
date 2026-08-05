# nockapp — Tip5 as an independent witness

An **example**, not a core deliverable. Racoon and Baloon are the
libraries; this is a thing built on top of them to see whether they hold
up against someone else's arithmetic.

`/lib/tip5` is [Tip5][tip5], the algebraic sponge hash Nockchain uses for
commitments, Merkle trees, and transaction IDs. It already has an
authoritative Hoon implementation in
[nockchain-official][nc] (`hoon/common/ztd/three.hoon`) and a Rust jet.
**This is a second one, and second is the point.**

## Why a second implementation

Nockchain's Hoon and its Rust jet share a lineage: the same reading of the
same paper produced both, so their agreeing mostly confirms that the
transcription was consistent with itself. An implementation built from
different primitives agrees for a different reason — or disagrees, which
is the more useful outcome.

That makes this a witness for **in-Hoon determinism on the mathematics**:
the same field, the same permutation, arrived at from exact algebra rather
than from hand-tuned 64-bit arithmetic.

```
    field scalars     +cadd +csub +cmul +cpow +cinv on ~(. mx:racoon p)
    the MDS layer     +mul on ~(. mm:baloon p), a 16x16 by 16x1 product
    the lookup table  +cpow and +csub at modulus 257
```

The witness is two-sided. A digest matching Nockchain's is evidence about
Tip5 **and** about Racoon's modular arithmetic and Baloon's matrices: a
fault in either would have to conspire with a fault in the transcription
to stay hidden.

## What it found

**"Tip5 with 5 rounds" names two different functions in
nockchain-official.** `ztd/three.hoon`'s `+round-constants` selects an
80-constant block when `num-rounds` is 5; the `ai-pow-zk` golden KAT's
5-round permutation uses the **first 80 of the canonical 112**. They are
not the same numbers and not the same hash.

```
+tip5 ~[1 2 3]                 rounds 5  %canon
   out  ~[11.296.766.565.621.581.192 ...]
+tip5 ~[1 2 3], =sched %alt5   rounds 5  %alt5
   out  ~[1.037.267.703.022.364.995 ...]
```

Both are carried, both are verified against their own published vectors,
and the round schedule is a door **sample** rather than a constant —
which is the honest shape given that a round count alone does not name
the function. Nockchain's door takes only the count and picks the block
internally, which is what hides the collision.

This is what a witness is for. Nothing here says either function is
wrong; what it says is that "Tip5, 5 rounds" is not a complete
specification of which one you get.

## What is derived and what is not

A witness that copies its inputs is not a witness, so everything
derivable is derived:

| | |
|---|---|
| `lookup-table` | 256 entries, from `x -> (x+1)³ - 1 mod 257` |
| `mds` | 256 entries, circulant from a column of 16 |
| `r`, `r-inv` | from `p` |
| init states | from the domain |

What cannot be derived is Tip5's **design constants** — the MDS matrix's
first column and the round-constant schedules. Those are in
`/lib/tip5-constants`, mechanically extracted rather than typed. That is
the exact boundary of this library's independence, and it is stated in the
file header rather than left to be discovered.

The published lookup table is checked in as a *vector*, not a constant:
the suite asserts the derived table equals it, entry for entry, and
`/lib/tip5` still builds its own from the cube map.

## Montgomery form is specification, not optimization

`+split-and-lookup` reads the **bytes** of a state element, so it sees the
representative rather than the field element. A Tip5 that skipped the
transform would compute a different function.

Here it is derived from its definition — `montify` is multiplication by
`r = 2^64 mod p = 2^32 - 1`, `demontify` by its inverse — where
Nockchain's `+mont-reduction` is hand-derived bit manipulation over
32-bit limbs. Those two agreeing is among the more interesting things the
vectors check, and the golden KAT makes it direct: it publishes its round
constants in **both** forms, and this library's `montify` carries one to
the other.

The x⁷ S-box rests on `r³ = 1` in this field, which is why four *plain*
multiplications of Montgomery representatives land back in Montgomery
space. That identity is asserted rather than assumed — it is specific to
Goldilocks and would silently compute the wrong thing elsewhere.

## Coverage, stated plainly

Every published vector is at **5 rounds**, so that is what is verified.

| suite arm | vectors | source |
|---|---:|---|
| `test-w-hash-10` | 100 | `hoon/tests/crypto/mod/tip5.hoon` |
| `test-w-hash-varlen` | 100 | same |
| `test-w-permute` | 100 | `tip5_5round_golden_kat.txt` |

The canonical **7-round** path is the same code with 32 more constants
and is **unverified** — no vectors for it are published. A green suite
says nothing about it, `/gen/tip5` prints `UNVERIFIED` on every line that
uses it, and this table is the reason.

`test-w-permute` was confirmed to discriminate by pointing it at the other
schedule and watching the suite go red, since a `levy` over vectors is
the kind of arm that passes vacuously if the list is ever empty.

## It is slow, deliberately

Racoon's `+cmul` canonicalizes on every operation and has no Montgomery
multiplication; Nockchain's runs on raw `@` arithmetic with a
hand-derived reduction and a Rust jet under it. 100 `hash-varlen` vectors
take 51 s here.

**Do not call this to hash anything whose latency matters.** Call it to
find out whether the fast one is right.

## Every arm is `pinned`

Tip5's output is defined by its procedure; there is no canonical
mathematical object to name, the way there is for `det` or `gcd`. This
inverts Racoon's usual disposition, where `pinned` is the rare exception
— five arms in the whole library, plus `lll` — and it is the clearest
sign that this desk is an example rather than algebra.

## Layout

```
nockapp/
  desk/
    lib/tip5.hoon             the witness
    lib/tip5-constants.hoon   design constants -- GENERATED
    lib/tip5-vectors.hoon     known answers -- GENERATED
    tests/lib/tip5.hoon       test suite
    gen/tip5.hoon             hash from the dojo
  tools/genkat.py             extracts both generated files
  scripts/sync.sh             copy desk/ into the pier
  README.md                   this file
```

## Edit–test loop

This desk needs **both** others; run their sync scripts first on a fresh
pier.

```
racoon/scripts/sync.sh && baloon/scripts/sync.sh && nockapp/scripts/sync.sh
|commit %base                          # dojo
-test /=base=/tests/lib/tip5 ~         # dojo
```

To regenerate the two generated files after a nockchain-official update:

```
python3 tools/genkat.py [path-to-nockchain-official]
```

It defaults to `~/zorp/nockchain-official`. Neither generated file is
hand-edited — 208 sixty-four-bit constants is exactly the shape of
mistake this project has made before, when four Swinnerton–Dyer
coefficients were wrong the first time they were written out by hand.

[tip5]: https://eprint.iacr.org/2023/107
[nc]: https://github.com/zorp-corp/nockchain
