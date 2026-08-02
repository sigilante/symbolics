#!/usr/bin/env python3
"""Generate desk/lib/baloon-vectors.hoon from an independent oracle.

SPEC deliverable 3.  The output file is NEVER hand-edited: regenerate it with

    python3 tools/genvec.py > desk/lib/baloon-vectors.hoon

Determinism is required (SPEC S11.2): the PRNG seed is pinned below and no
value is drawn from the clock, the environment, or set iteration order.

Oracle policy (SPEC S11.3).  VERIFY SymPy's conventions, do not assume them.
Racoon lost time to sympy.resultant silently normalizing its argument order,
which produced a wrong sign whenever deg a < deg b and would have been baked
into the vectors as the reference answer.  Every convention relied on here is
asserted against its definition in +selfcheck below, which runs on every
generation, so a SymPy upgrade that changes a convention breaks generation
rather than silently corrupting the corpus.
"""

import random

from sympy import Matrix, Rational, eye, symbols, zeros as spzeros

X = symbols("x")

SEED = 20260802

# --------------------------------------------------------------------------
# Hoon literal formatting
# --------------------------------------------------------------------------


def ud(n):
    """Format a natural as a Hoon @ud, dot-grouped every three digits."""
    if n < 0:
        raise ValueError("ud() requires a natural, got %r" % (n,))
    s = str(n)
    parts = []
    while len(s) > 3:
        parts.append(s[-3:])
        s = s[:-3]
    parts.append(s)
    return ".".join(reversed(parts))


def sd(n):
    """Format an integer as a Hoon @s.  Zero is always --0."""
    return ("--" if n >= 0 else "-") + ud(abs(n))


def frac(r):
    """Format a Rational as a canonical $frac literal."""
    r = Rational(r)
    return "[%s %s]" % (sd(int(r.p)), ud(int(r.q)))


def qvec(v):
    """Format a list of Rationals as a $qvec literal."""
    if not v:
        return "~"
    return "~[%s]" % " ".join(frac(x) for x in v)


def qmat(m):
    """Format a list of rows as a $qmat literal."""
    if not m:
        return "~"
    return "~[%s]" % " ".join(qvec(r) for r in m)


def of_matrix(M):
    """sympy Matrix -> list of rows of Rational."""
    return [[Rational(M[i, j]) for j in range(M.cols)] for i in range(M.rows)]


def emit(name, hoon_type, rows, doc):
    """Emit one vector arm."""
    print("::    +%s:  %s" % (name, doc))
    print("::")
    print("::  %d cases." % len(rows))
    print("++  %s" % name)
    print("  ^-  %s" % hoon_type)
    if not rows:
        print("  ~")
        print("::")
        return
    print("  :~  %s" % rows[0])
    for r in rows[1:]:
        print("      %s" % r)
    print("  ==")
    print("::")


# --------------------------------------------------------------------------
# Convention self-check (SPEC S11.3)
# --------------------------------------------------------------------------


def selfcheck():
    """Assert every SymPy convention this script relies on.

    Runs on every generation.  A SymPy upgrade that changes a convention
    fails here loudly rather than corrupting the corpus quietly.
    """
    # .T is the transpose, not the conjugate transpose (identical over Q,
    # but the distinction matters if complex entries ever appear)
    A = Matrix([[1, 2, 3], [4, 5, 6]])
    assert A.T.tolist() == [[1, 4], [2, 5], [3, 6]]
    assert A.T.T.tolist() == A.tolist()

    # eye(n) is the identity; zeros(r, c) is row-major r x c
    assert eye(3).tolist() == [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
    assert spzeros(2, 3).tolist() == [[0, 0, 0], [0, 0, 0]]

    # indexing is M[row, col], zero-based
    assert A[0, 2] == 3 and A[1, 0] == 4

    # rational entries stay exact, never becoming floats
    Q = Matrix([[Rational(1, 3)]])
    assert Q[0, 0] == Rational(1, 3)
    assert (Q * 3)[0, 0] == 1


# --------------------------------------------------------------------------
# Matrix supply
# --------------------------------------------------------------------------


def rand_qmat(rng, r, c, denom=6, span=9):
    """A random r x c matrix of canonical rationals."""
    return [
        [Rational(rng.randrange(-span, span + 1), rng.randrange(1, denom + 1))
         for _ in range(c)]
        for _ in range(r)
    ]


def supply(rng, count, maxdim=5):
    """A deterministic supply of matrices, edge cases first."""
    out = [
        [[Rational(0)]],                       # 1x1 zero
        [[Rational(1)]],                       # 1x1 one
        [[Rational(-3, 4)]],                   # 1x1 fractional
        [[Rational(1), Rational(2)]],          # 1x2, wide
        [[Rational(1)], [Rational(2)]],        # 2x1, tall
        [[Rational(1), Rational(0)], [Rational(0), Rational(1)]],
        [[Rational(1), Rational(2)], [Rational(3), Rational(4)]],
        [[Rational(1, 2), Rational(1, 3)], [Rational(1, 4), Rational(1, 5)]],
        # singular
        [[Rational(1), Rational(2)], [Rational(2), Rational(4)]],
        # a rank-1 3x3
        [[Rational(1), Rational(2), Rational(3)],
         [Rational(2), Rational(4), Rational(6)],
         [Rational(3), Rational(6), Rational(9)]],
    ]
    while len(out) < count:
        r = rng.randrange(1, maxdim + 1)
        c = rng.randrange(1, maxdim + 1)
        out.append(rand_qmat(rng, r, c))
    return out


# --------------------------------------------------------------------------
# Phase 0 families
# --------------------------------------------------------------------------


def dims_rows(rng, count=48):
    rows = []
    for m in supply(rng, count):
        rows.append("[%s %s %s]" % (qmat(m), ud(len(m)), ud(len(m[0]))))
    return rows


def transpose_rows(rng, count=48):
    rows = []
    for m in supply(rng, count):
        t = of_matrix(Matrix(m).T)
        # involutive, checked here as well as in-ship
        assert of_matrix(Matrix(t).T) == m
        rows.append("[%s %s]" % (qmat(m), qmat(t)))
    return rows


def idn_rows(count=12):
    rows = []
    for n in range(1, count + 1):
        rows.append("[%s %s]" % (ud(n), qmat(of_matrix(eye(n)))))
    return rows


def zeros_rows(count=48):
    rows = []
    for r in range(1, 8):
        for c in range(1, 8):
            rows.append("[%s %s %s]"
                        % (ud(r), ud(c), qmat(of_matrix(spzeros(r, c)))))
            if len(rows) == count:
                return rows
    return rows


# --------------------------------------------------------------------------


def main():
    selfcheck()
    rng = random.Random(SEED)

    print("  ::  /lib/baloon-vectors")
    print("::::  GENERATED FILE -- DO NOT EDIT")
    print("::")
    print("::  Regenerate with:  python3 tools/genvec.py")
    print("::")
    print("::  Reference vectors for the Baloon test suite, produced by an")
    print("::  independent oracle (sympy.Matrix).  PRNG seed %d." % SEED)
    print("::")
    print("::  Every SymPy convention relied on is asserted against its")
    print("::  definition in the generator's +selfcheck, which runs on every")
    print("::  generation -- see SPEC S11.3 and Racoon's sympy.resultant")
    print("::  lesson.")
    print("::")
    print("/-  *baloon, *racoon")
    print("|%")
    print("::")

    emit("dims-vectors", "(list [a=qmat r=@ud c=@ud])", dims_rows(rng),
         "+dims:qm, dimensions derived from the structure")
    emit("transpose-vectors", "(list [a=qmat t=qmat])", transpose_rows(rng),
         "+transpose:qm, oracle sympy Matrix.T")
    emit("idn-vectors", "(list [n=@ud m=qmat])", idn_rows(),
         "+idn:qm, oracle sympy.eye")
    emit("zeros-vectors", "(list [r=@ud c=@ud m=qmat])", zeros_rows(),
         "+zeros:qm, oracle sympy.zeros")

    print("--")


if __name__ == "__main__":
    main()
