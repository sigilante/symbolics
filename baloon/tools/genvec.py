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

    # charpoly is det(xI - A), NOT det(A - xI).  The two differ by (-1)^n
    # and agree only in even dimension, so this must be checked at ODD n or
    # it proves nothing.
    C = Matrix([[1, 2, 0], [3, 4, 1], [0, 1, 2]])
    assert C.charpoly(X).as_expr().expand() == (X * eye(3) - C).det().expand()
    assert C.charpoly(X).as_expr().expand() != (C - X * eye(3)).det().expand()
    # and it is monic of degree n
    cc = list(reversed(C.charpoly(X).all_coeffs()))
    assert cc[-1] == 1 and len(cc) == 4

    # eigenvals returns a value -> multiplicity map, and .is_rational
    # distinguishes the eigenvalues this library can actually represent
    assert Matrix([[2, 0], [0, 3]]).eigenvals() == {2: 1, 3: 1}
    assert Matrix([[5, 1], [0, 5]]).eigenvals() == {5: 2}
    rot = Matrix([[0, -1], [1, 0]]).eigenvals()
    assert all(not v.is_rational for v in rot)


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
# Phase 1 families
# --------------------------------------------------------------------------


def conformable_pairs(rng, count, same=True):
    """Pairs of matrices: same shape when .same, else cols(a) == rows(b)."""
    out = []
    if same:
        edges = [
            ([[0]], [[0]]),
            ([[1]], [[-1]]),
            ([[1, 2], [3, 4]], [[5, 6], [7, 8]]),
            ([[Rational(1, 2)]], [[Rational(1, 3)]]),
        ]
    else:
        edges = [
            ([[1]], [[1]]),
            ([[1, 2], [3, 4]], [[5, 6], [7, 8]]),
            ([[1, 2, 3], [4, 5, 6]], [[1, 2], [3, 4], [5, 6]]),
            ([[1, 2], [3, 4], [5, 6]], [[1, 2, 3], [4, 5, 6]]),
        ]
    out.extend([([[Rational(x) for x in r] for r in a],
                 [[Rational(x) for x in r] for r in b]) for a, b in edges])
    while len(out) < count:
        r = rng.randrange(1, 5)
        k = rng.randrange(1, 5)
        c = k if same else rng.randrange(1, 5)
        a = rand_qmat(rng, r, k)
        b = rand_qmat(rng, r, k) if same else rand_qmat(rng, k, c)
        out.append((a, b))
    return out


def binop_rows(rng, op, same=True, count=48):
    rows = []
    for a, b in conformable_pairs(rng, count, same):
        c = of_matrix(op(Matrix(a), Matrix(b)))
        rows.append("[%s %s %s]" % (qmat(a), qmat(b), qmat(c)))
    return rows


def neg_rows(rng, count=48):
    rows = []
    for m in supply(rng, count):
        rows.append("[%s %s]" % (qmat(m), qmat(of_matrix(-Matrix(m)))))
    return rows


def scale_rows(rng, count=48):
    rows = []
    scalars = [Rational(0), Rational(1), Rational(-1), Rational(1, 2),
               Rational(-3, 4), Rational(5)]
    for i, m in enumerate(supply(rng, count)):
        x = scalars[i % len(scalars)]
        rows.append("[%s %s %s]"
                    % (qmat(m), frac(x), qmat(of_matrix(Matrix(m) * x))))
    return rows


def pow_rows(rng, count=48):
    """+pow:qm -- [m e c].  Square inputs only; non-square crashes."""
    rows = []
    mats = [
        [[Rational(1)]],
        [[Rational(0)]],
        [[Rational(1), Rational(2)], [Rational(3), Rational(4)]],
        [[Rational(1), Rational(0)], [Rational(0), Rational(1)]],
        [[Rational(1, 2), Rational(1, 3)], [Rational(1, 4), Rational(1, 5)]],
        # nilpotent: powers vanish
        [[Rational(0), Rational(1)], [Rational(0), Rational(0)]],
    ]
    while len(mats) < 12:
        n = rng.randrange(1, 4)
        mats.append(rand_qmat(rng, n, n, denom=3, span=4))
    i = 0
    while len(rows) < count:
        m = mats[i % len(mats)]
        e = i % 6
        i += 1
        c = of_matrix(Matrix(m) ** e)
        rows.append("[%s %s %s]" % (qmat(m), ud(e), qmat(c)))
    return rows



# --------------------------------------------------------------------------
# Phase 2 families
# --------------------------------------------------------------------------


def squares(rng, count, maxdim=4):
    """A supply of square matrices, singular cases included."""
    out = [
        [[Rational(1)]],
        [[Rational(0)]],
        [[Rational(1), Rational(2)], [Rational(3), Rational(4)]],
        [[Rational(1), Rational(2)], [Rational(2), Rational(4)]],      # singular
        [[Rational(1), Rational(0)], [Rational(0), Rational(1)]],
        [[Rational(0), Rational(1)], [Rational(1), Rational(0)]],      # swap
        [[Rational(1, 2), Rational(1, 3)], [Rational(1, 4), Rational(1, 5)]],
        [[Rational(1), Rational(2), Rational(3)],
         [Rational(4), Rational(5), Rational(6)],
         [Rational(7), Rational(8), Rational(10)]],
        [[Rational(1), Rational(2), Rational(3)],
         [Rational(4), Rational(5), Rational(6)],
         [Rational(7), Rational(8), Rational(9)]],                     # singular
        # a zero first pivot, which forces the Bareiss row swap
        [[Rational(0), Rational(1)], [Rational(1), Rational(1)]],
        [[Rational(0), Rational(0), Rational(1)],
         [Rational(0), Rational(1), Rational(0)],
         [Rational(1), Rational(0), Rational(0)]],
    ]
    while len(out) < count:
        n = rng.randrange(1, maxdim + 1)
        out.append(rand_qmat(rng, n, n, denom=4, span=6))
    return out


def det_rows(rng, count=48):
    rows = []
    for m in squares(rng, count):
        rows.append("[%s %s]" % (qmat(m), frac(Matrix(m).det())))
    return rows


def rref_rows(rng, count=48):
    rows = []
    for m in supply(rng, count):
        R, piv = Matrix(m).rref()
        pl = "~" if not piv else "~[%s]" % " ".join(ud(int(p)) for p in piv)
        rows.append("[%s %s %s]" % (qmat(m), qmat(of_matrix(R)), pl))
    return rows


def rank_rows(rng, count=48):
    rows = []
    for m in supply(rng, count):
        rows.append("[%s %s]" % (qmat(m), ud(Matrix(m).rank())))
    return rows


def inv_rows(rng, count=48):
    """+inv:qm -- [m c].  Invertible inputs only; singular ones crash."""
    rows = []
    for m in squares(rng, count * 3):
        M = Matrix(m)
        if M.det() == 0:
            continue
        inverse = of_matrix(M.inv())
        # the defining identity, checked here as well as in-ship
        assert of_matrix(Matrix(inverse) * M) == of_matrix(eye(M.rows))
        rows.append("[%s %s]" % (qmat(m), qmat(inverse)))
        if len(rows) == count:
            break
    return rows


def solve_rows(rng, count=48):
    """+solve:qm -- [a b out].  Singular a gives ~, not a crash."""
    rows = []
    for m in squares(rng, count * 2):
        M = Matrix(m)
        n = M.rows
        b = rand_qmat(rng, n, 1, denom=3, span=5)
        if M.det() == 0:
            out = "~"
        else:
            x = of_matrix(M.solve(Matrix(b)))
            assert of_matrix(M * Matrix(x)) == b
            out = "[~ %s]" % qmat(x)
        rows.append("[%s %s %s]" % (qmat(m), qmat(b), out))
        if len(rows) == count:
            break
    return rows


def nullspace_rows(rng, count=48):
    """+nullspace:qm -- [m basis].

    SymPy's basis matches the SPEC S7 convention: for each free column j, a
    vector with 1 at j, 0 at the other free columns, and the negated RREF
    entry at each pivot.  Asserted below rather than assumed.
    """
    rows = []
    for m in supply(rng, count):
        M = Matrix(m)
        ns = [list(v) for v in M.nullspace()]
        # every basis vector really is in the kernel
        for v in ns:
            assert all(x == 0 for x in M * Matrix(len(v), 1, v))
        # rank-nullity
        assert M.rank() + len(ns) == M.cols
        body = "~" if not ns else "~[%s]" % " ".join(qvec(v) for v in ns)
        rows.append("[%s %s]" % (qmat(m), body))
    return rows



# --------------------------------------------------------------------------
# Phase 3 families
# --------------------------------------------------------------------------


def spectral_supply(rng, count):
    """Square matrices, weighted toward ones with rational spectra."""
    out = [
        [[Rational(1)]],
        [[Rational(0)]],
        [[Rational(-3, 4)]],
        [[Rational(2), Rational(0)], [Rational(0), Rational(3)]],   # diagonal
        [[Rational(5), Rational(1)], [Rational(0), Rational(5)]],   # repeated
        [[Rational(1), Rational(2)], [Rational(3), Rational(4)]],   # irrational
        [[Rational(0), Rational(-1)], [Rational(1), Rational(0)]],  # complex
        [[Rational(1), Rational(0)], [Rational(0), Rational(1)]],
        [[Rational(1), Rational(2), Rational(3)],
         [Rational(4), Rational(5), Rational(6)],
         [Rational(7), Rational(8), Rational(10)]],
        # upper triangular: the spectrum is the diagonal
        [[Rational(1), Rational(9)], [Rational(0), Rational(-2)]],
        [[Rational(2), Rational(1), Rational(3)],
         [Rational(0), Rational(-1), Rational(4)],
         [Rational(0), Rational(0), Rational(7)]],
        [[Rational(1, 2), Rational(0)], [Rational(0), Rational(-1, 3)]],
    ]
    while len(out) < count:
        n = rng.randrange(1, 4)
        out.append(rand_qmat(rng, n, n, denom=3, span=4))
    return out


def charpoly_rows(rng, count=48):
    rows = []
    for m in spectral_supply(rng, count):
        M = Matrix(m)
        cs = [Rational(c) for c in reversed(M.charpoly(X).all_coeffs())]
        assert cs[-1] == 1                       # monic
        assert len(cs) == M.rows + 1             # degree n
        rows.append("[%s %s]" % (qmat(m), qvec(cs)))
    return rows


def eigen_rows(rng, count=48):
    """+eigen:qm -- [m evs].  RATIONAL eigenvalues only, ascending."""
    rows = []
    for m in spectral_supply(rng, count):
        M = Matrix(m)
        ev = [(Rational(v), int(k)) for v, k in M.eigenvals().items()
              if v.is_rational]
        ev.sort(key=lambda t: t[0])
        # each really is a root of the characteristic polynomial
        for v, _ in ev:
            assert M.charpoly(X).as_expr().subs(X, v) == 0
        body = ("~" if not ev
                else "~[%s]" % " ".join("[%s %s]" % (frac(v), ud(k))
                                        for v, k in ev))
        rows.append("[%s %s]" % (qmat(m), body))
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

    # Phase 1
    bt = "(list [a=qmat b=qmat c=qmat])"
    emit("add-vectors", bt, binop_rows(rng, lambda p, q: p + q),
         "+add:qm, oracle sympy Matrix addition")
    emit("sub-vectors", bt, binop_rows(rng, lambda p, q: p - q),
         "+sub:qm, oracle sympy Matrix subtraction")
    emit("mul-vectors", bt,
         binop_rows(rng, lambda p, q: p * q, same=False),
         "+mul:qm, oracle sympy Matrix product; cols(a) = rows(b)")
    emit("neg-vectors", "(list [a=qmat c=qmat])", neg_rows(rng),
         "+neg:qm")
    emit("scale-vectors", "(list [a=qmat x=frac c=qmat])", scale_rows(rng),
         "+scale:qm; includes the zero scalar")
    emit("pow-vectors", "(list [a=qmat e=@ud c=qmat])", pow_rows(rng),
         "+pow:qm; square inputs, includes e = 0 and a nilpotent matrix")

    # Phase 2
    emit("det-vectors", "(list [a=qmat d=frac])", det_rows(rng),
         "+det:qm, oracle sympy Matrix.det; includes singular inputs")
    emit("rref-vectors", "(list [a=qmat m=qmat piv=(list @ud)])",
         rref_rows(rng), "+rref:qm, oracle sympy Matrix.rref")
    emit("rank-vectors", "(list [a=qmat r=@ud])", rank_rows(rng),
         "+rank:qm, oracle sympy Matrix.rank")
    emit("inv-vectors", "(list [a=qmat c=qmat])", inv_rows(rng),
         "+inv:qm, checked against inv(m) * m = I; singular inputs crash")
    emit("solve-vectors", "(list [a=qmat b=qmat out=(unit qmat)])",
         solve_rows(rng),
         "+solve:qm, checked against a * x = b; singular a gives ~")
    emit("nullspace-vectors", "(list [a=qmat ns=(list qvec)])",
         nullspace_rows(rng),
         "+nullspace:qm, the pinned SPEC S7 basis; rank-nullity asserted")

    # Phase 3
    emit("charpoly-vectors", "(list [a=qmat cp=qol])", charpoly_rows(rng),
         "+charpoly:qm, det(xI - A); monic of degree n, asserted")
    emit("eigen-vectors", "(list [a=qmat evs=(list [val=frac mult=@ud])])",
         eigen_rows(rng),
         "+eigen:qm, RATIONAL eigenvalues only, ascending; roots asserted")

    print("--")


if __name__ == "__main__":
    main()
