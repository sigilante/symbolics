#   Symbolic Libraries for Urbit

**Status ~2026.8.1:  Embarquemos.**

![An evocative scene of a mysterious futuristic castle in the style of Flash Gordon](./img/hero.jpeg)

This repository organizes the core symbolic computing apparatus for Urbit:

- Racoon (Real AlgebraiCs in hOON) offers basic symbolic operations.
- Baloon (Basic linear ALgebra in hOON) offers exact linear algebra over ℚ.

ℤ represents the set of integers (e.g., ${-2, -1, 0, 1, 2, ...}$), with the name derived from the German word Zahlen meaning "numbers". 

ℚ denotes the set of rational numbers, which are quotients of integers (fractions like $1/2$ or $-7/3$), including all integers as a subset. 

𝔽p (also written as Z/pZ or GF(p)) is a finite field consisting of integers modulo a prime number $p$; it is used in modular arithmetic where addition and multiplication wrap around after reaching $p$. 

ℤ/n (standardly written as ℤ/nℤ or ℤ/(n)) represents the ring of integers modulo $n$, containing $n$ residue classes ${0, 1, ..., n-1}$ where operations are performed by taking the remainder of division by $n$.  Note that while some introductory texts use the notation $\mathbb{Z}_n$, this is often avoided in advanced mathematics because $\mathbb{Z}_p$ typically denotes the ring of $p$-adic integers.
