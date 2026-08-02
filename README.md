#   Symbolic Libraries for Urbit

**Status ~2026.8.1:  Embarquemos.**

![An evocative scene of a mysterious futuristic castle in the style of Flash Gordon](./img/hero.jpeg)

The Urbit symbolics stack covers the mathematics of:

* $ℤ$ represents the set of integers (e.g., $\{-2, -1, 0, 1, 2, ...\}$).
* $ℚ$ denotes the set of rational numbers, which are quotients of integers (fractions like $\frac{1}{2}$ or $-\frac{7}{3}$), including all integers as a subset.
* $𝔽p$ (also written as $Z/pZ$ or $GF(p)$) is a finite field consisting of integers modulo a prime number $p$; it is used in modular arithmetic where addition and multiplication wrap around after reaching $p$. 
* $ℤ/n$ (standardly written as $ℤ/nℤ$ or $ℤ/(n)$) represents the ring of integers modulo $n$, containing $n$ residue classes ${0, 1, ..., n-1}$ where operations are performed by taking the remainder of division by $n$.

This repository organizes the core symbolic computing apparatus for Urbit:

- Racoon (Real AlgebraiCs in hOON) offers basic symbolic operations.
  - [`README.md`](./lagoon/README.md)
  - `racoon/desk` contains the Hoon-specific code for Racoon.
    - `/lib/racoon` is the main library for Racoon operations.
    - `/lib/racoon-fmt` contains the Hoon-specific code for formatting Racoon types (input and output)
    - `/sur/racoon` supplies type headers for Racoon.
  - `racoon/vere` will contain the C jets for the Vere runtime.
- Baloon (Basic linear ALgebra in hOON) offers exact linear algebra over the Racoon types.
  - [`README.md`](./baloon/README.md)
  - `baloon/desk` contains the Hoon-specific code for Baloon.
    - `/lib/baloon` is the main library for Baloon operations.
    - `/lib/baloon-fmt` contains the Hoon-specific code for formatting Baloon types (input and output)
    - `/sur/baloon` supplies type headers for Baloon.
  - `baloon/vere` contains the C jets for the Vere runtime.
