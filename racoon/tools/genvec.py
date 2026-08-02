#!/usr/bin/env python3
"""Generate desk/lib/racoon-vectors.hoon from an independent oracle.

SPEC deliverable 3.  The output file is NEVER hand-edited: regenerate it with

    python3 tools/genvec.py > desk/lib/racoon-vectors.hoon

Determinism is required (SPEC S11.2): the PRNG seed is pinned below and no
value is drawn from the clock, the environment, or set iteration order.

Oracles.  Where an arm's output is canonical, the oracle is an independent
implementation -- math.isqrt, sympy.isprime, sympy.ntheory.modular.crt,
fractions.Fraction.  Where SPEC S9 pins the *algorithm* rather than the value
(+egcd, +ratrec), the pinned algorithm is transcribed here and its output is
cross-checked against an independent invariant: the Bezout identity against
math.gcd for +egcd, and the congruence q*u = p (mod m) for +ratrec.  That
keeps this file a check on the Hoon transcription rather than a copy of it.
"""

import math
from fractions import Fraction

from sympy import Poly, ZZ, isprime, symbols
from sympy.ntheory.modular import crt as sympy_crt

import random

X = symbols("x")

SEED = 20260801
MERSENNE_61 = 2**61 - 1

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


def loob(b):
    """Format a bool as a Hoon ?."""
    return "%.y" if b else "%.n"


def frac(f):
    """Format a Fraction as a canonical $frac literal."""
    return "[%s %s]" % (sd(f.numerator), ud(f.denominator))


def unit_frac(f):
    """Format an optional Fraction as a (unit frac) literal."""
    return "~" if f is None else "[~ %s]" % (frac(f),)


def zol(c):
    """Format a little-endian coefficient list as a $zol literal."""
    if not c:
        return "~"
    return "~[%s]" % " ".join(sd(v) for v in c)


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
# Pinned algorithms, transcribed from SPEC S7 / S9
# --------------------------------------------------------------------------


def pinned_egcd(a, b):
    """Textbook EEA (vzGG Alg. 3.6); base case egcd(a, 0) = [a 1 0]."""
    r0, r1 = a, b
    s0, s1 = 1, 0
    t0, t1 = 0, 1
    while r1 != 0:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    # independent cross-check: the Bezout identity, and d against math.gcd
    assert r0 == math.gcd(a, b), (a, b, r0)
    assert r0 == s0 * a + t0 * b, (a, b)
    return r0, s0, t0


def pinned_ratrec(u, m, nb, db):
    """Wang rational reconstruction (vzGG S5.10), per SPEC S9."""
    r0, r1 = m, u
    t0, t1 = 0, 1
    while r1 > nb:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        t0, t1 = t1, t0 - q * t1
    if t1 == 0:
        return None
    aq = abs(t1)
    if aq > db:
        return None
    if math.gcd(r1, aq) != 1:
        return None
    p = r1 if t1 > 0 else -r1
    # independent cross-check: the defining congruence
    assert (aq * u - p) % m == 0, (u, m, p, aq)
    return Fraction(p, aq)


# --------------------------------------------------------------------------
# Vector families
# --------------------------------------------------------------------------


def gcd_rows(rng):
    """+gcd:nz -- [a b g]."""
    cases = [
        # SPEC S7: gcd(0, 0) = 0, and 0 is the identity
        (0, 0), (17, 0), (0, 17), (1, 0), (0, 1),
        # coprime, equal, and divisor pairs
        (1, 1), (12, 18), (18, 12), (35, 64), (17, 34),
        (1000000, 5), (2**32, 2**16), (6, 35),
        # consecutive Fibonacci: the EEA worst case
        (89, 55), (144, 89), (233, 144), (377, 233), (610, 377),
        # powers of two, and a prime against its multiples
        (1024, 768), (2**20, 2**13), (97, 97 * 5), (97, 98),
        # both large
        (MERSENNE_61, 2**61), (MERSENNE_61, MERSENNE_61),
        (2**64 - 1, 2**32 - 1),
    ]
    while len(cases) < 48:
        a = rng.randrange(0, 2**40)
        b = rng.randrange(0, 2**40)
        cases.append((a, b))
    return ["[%s %s %s]" % (ud(a), ud(b), ud(math.gcd(a, b))) for a, b in cases]


def egcd_rows(rng):
    """+egcd:nz -- [a b d u v]."""
    cases = [
        # SPEC S7 pinned base case
        (17, 0), (0, 0), (0, 17), (1, 0),
        (240, 46), (46, 240), (12, 18), (35, 64), (1, 1),
        # Fibonacci pairs maximise the EEA step count
        (89, 55), (144, 89), (233, 144), (377, 233), (610, 377),
        (987, 610), (1597, 987),
        # coprime pairs, where the cofactors are modular inverses
        (3, 97), (97, 3), (65537, 4294967291),
        (2**31 - 1, 2**61 - 1),
    ]
    while len(cases) < 44:
        a = rng.randrange(0, 2**40)
        b = rng.randrange(0, 2**40)
        cases.append((a, b))
    rows = []
    for a, b in cases:
        d, u, v = pinned_egcd(a, b)
        rows.append("[%s %s %s %s %s]" % (ud(a), ud(b), ud(d), sd(u), sd(v)))
    return rows


def isqrt_rows(rng):
    """+isqrt:nz -- [a r]."""
    cases = [0, 1, 2, 3, 4, 5, 8, 9, 10, 15, 16, 17, 24, 25, 26, 99, 100, 101]
    # perfect squares and their neighbours: the off-by-one boundary
    for k in (255, 256, 65535, 65536, 2**20, 2**31, 2**32):
        cases += [k * k - 1, k * k, k * k + 1]
    # exact powers of two, whose roots straddle the bit-length seed
    cases += [2**32, 2**33, 2**63, 2**64, 2**65]
    while len(cases) < 52:
        cases.append(rng.randrange(0, 2**64))
    return ["[%s %s]" % (ud(a), ud(math.isqrt(a))) for a in cases]


def is_prime_rows(rng):
    """+is-prime:nz -- [n ?]."""
    cases = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    # every witness in the pinned schedule, and 37^2 where trial division ends
    cases += [43, 97, 101, 1369, 1370]
    # Carmichael numbers: these defeat a Fermat test
    cases += [561, 1105, 1729, 2465, 2821, 6601, 8911, 62745, 162401]
    # strong pseudoprimes to the first k bases, which defeat a short schedule
    cases += [2047, 1373653, 25326001, 3215031751, 2152302898747,
              3474749660383, 341550071728321]
    # large primes and near-primes, including the 61-bit Mersenne prime
    cases += [1000000007, 1000000009, MERSENNE_61, MERSENNE_61 + 2,
              2**31 - 1, 2**61 + 1, 1000000009000000021]
    while len(cases) < 56:
        cases.append(rng.randrange(2, 2**50))
    return ["[%s %s]" % (ud(n), loob(bool(isprime(n)))) for n in cases]


def crt_rows(rng):
    """+crt:nz -- [in r m]."""
    cases = [
        [(2, 3), (3, 5), (2, 7)],
        [(1, 4), (1, 9)],
        [(3, 5)],
        [(13, 5)],
        [(0, 2), (0, 3)],
        [(1, 2), (2, 3), (3, 5), (4, 7)],
        [(2, 7), (4, 11), (9, 13), (1, 17)],
        [(0, 2), (1, 3), (2, 5), (3, 7), (4, 11), (5, 13)],
        [(1, 2**31 - 1), (2, 2**61 - 1)],
        [(12345, 65537), (54321, 4294967291)],
    ]
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
              59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]
    while len(cases) < 44:
        k = rng.randrange(2, 6)
        ms = rng.sample(primes, k)
        cases.append([(rng.randrange(0, m), m) for m in ms])
    rows = []
    for pairs in cases:
        rs = [r for r, _ in pairs]
        ms = [m for _, m in pairs]
        r, m = sympy_crt(ms, rs)
        r, m = int(r), int(m)
        assert m == math.prod(ms)
        for rr, mm in pairs:
            assert r % mm == rr % mm
        inner = " ".join("[%s %s]" % (ud(a), ud(b)) for a, b in pairs)
        rows.append("[~[%s] %s %s]" % (inner, ud(r), ud(m)))
    return rows


def ratrec_rows(rng):
    """+ratrec:nz -- [u m nb db out]."""
    m = 10007
    bd = math.isqrt((m - 1) // 2)
    cases = [
        (65, 97, 6, 6), (0, 97, 6, 6), (1, 97, 6, 6), (96, 97, 6, 6),
        # SPEC S8: failure is ~, not a crash
        (5, 97, 2, 2), (44, 97, 3, 3),
        (0, 2, 0, 0), (1, 2, 1, 1),
    ]
    # round-trips: build p/q, reduce it mod m, and require exact recovery
    seen = set()
    while len(cases) < 48:
        p = rng.randrange(-bd, bd + 1)
        q = rng.randrange(1, bd + 1)
        if math.gcd(abs(p), q) != 1 or (p, q) in seen:
            continue
        seen.add((p, q))
        u = (p * pow(q, -1, m)) % m
        cases.append((u, m, bd, bd))
    rows = []
    for u, mm, nb, db in cases:
        out = pinned_ratrec(u, mm, nb, db)
        rows.append("[%s %s %s %s %s]"
                    % (ud(u), ud(mm), ud(nb), ud(db), unit_frac(out)))
    return rows


def qq_pairs(rng, n):
    """A deterministic supply of Fraction pairs, with the edges up front."""
    out = [
        (Fraction(0), Fraction(1)),
        (Fraction(1), Fraction(1)),
        (Fraction(1, 2), Fraction(1, 3)),
        (Fraction(-1, 2), Fraction(1, 3)),
        (Fraction(2, 3), Fraction(3, 4)),
        (Fraction(-3, 4), Fraction(-4, 3)),
        (Fraction(1, 2), Fraction(-1, 2)),
        (Fraction(1, 2), Fraction(2, 4)),
        (Fraction(5), Fraction(-5)),
        (Fraction(0), Fraction(-7, 3)),
        (Fraction(10**9, 3), Fraction(3, 10**9)),
        (Fraction(MERSENNE_61, 2), Fraction(2, MERSENNE_61)),
    ]
    while len(out) < n:
        a = Fraction(rng.randrange(-500, 501), rng.randrange(1, 200))
        b = Fraction(rng.randrange(-500, 501), rng.randrange(1, 200))
        out.append((a, b))
    return out


def qq_binop_rows(rng, op, skip_zero_b=False):
    rows = []
    for a, b in qq_pairs(rng, 48):
        if skip_zero_b and b == 0:
            b = Fraction(1, 7)
        rows.append("[%s %s %s]" % (frac(a), frac(b), frac(op(a, b))))
    return rows


def qq_cmp_rows(rng):
    rows = []
    for a, b in qq_pairs(rng, 48):
        o = "%eq" if a == b else ("%lt" if a < b else "%gt")
        rows.append("[%s %s %s]" % (frac(a), frac(b), o))
    return rows


def qq_new_rows(rng):
    """+new:qq -- [p q out].  Inputs are deliberately non-canonical."""
    cases = [
        (-6, 4), (6, 4), (0, 7), (5, 5), (4, 2), (1, 1), (0, 1),
        (-1, 1), (7, 1), (-100, 10), (2**61, 2), (-(2**61), 2),
        (999999, 3), (1, 999999),
    ]
    while len(cases) < 44:
        p = rng.randrange(-10**6, 10**6)
        q = rng.randrange(1, 10**6)
        cases.append((p, q))
    return ["[%s %s %s]" % (sd(p), ud(q), frac(Fraction(p, q)))
            for p, q in cases]


def qq_unary_rows(rng, op, nonzero=False):
    rows = []
    for a, _ in qq_pairs(rng, 48):
        if nonzero and a == 0:
            a = Fraction(3, 5)
        rows.append("[%s %s]" % (frac(a), frac(op(a))))
    return rows


# --------------------------------------------------------------------------
# Z[x] -- Phase 1
#
# Coefficient lists are little-endian and canonical (no trailing zero).  The
# oracle is sympy.Poly over ZZ, which is big-endian, so +to_poly and +of_poly
# reverse on the way in and out.
# --------------------------------------------------------------------------


def to_poly(c):
    """Little-endian coefficient list -> sympy Poly over ZZ."""
    if not c:
        return Poly(0, X, domain=ZZ)
    return Poly(list(reversed(c)), X, domain=ZZ)


def of_poly(p):
    """sympy Poly -> canonical little-endian coefficient list."""
    c = [int(v) for v in reversed(p.all_coeffs())]
    while c and c[-1] == 0:
        c.pop()
    return c


def zx_polys(rng, n):
    """A deterministic supply of canonical Z[x] polynomials, edges first."""
    out = [
        [],                       # the zero polynomial
        [1], [-1], [5], [-5],     # degree 0, both signs
        [0, 1],                   # x
        [1, 1], [-1, 1],          # 1 + x, x - 1
        [0, 0, 1],                # x^2
        [1, 2, 1],                # (1 + x)^2
        [-1, 0, 1],               # x^2 - 1
        [1, -2, 1],               # (x - 1)^2
        [1, 0, 0, 0, 1],          # 1 + x^4, with interior zeros
        [2, 4, 6],                # non-primitive
        [-3, 0, 9],               # non-primitive, negative lc absent
        [1, 1, 1, 1, 1, 1],
        [0, 0, 0, 1],             # x^3, leading interior zeros
        [10 ** 9, -(10 ** 9)],    # large coefficients
        [2 ** 61, 1],             # coefficient past a word boundary
        [-(2 ** 61), -1],
    ]
    nonzero = [v for v in range(-20, 21) if v != 0]
    while len(out) < n:
        d = rng.randrange(0, 7)
        c = [rng.randrange(-50, 51) for _ in range(d)]
        c.append(rng.choice(nonzero))   # keeps the list canonical
        out.append(c)
    return out


def zx_pairs(rng, n):
    ps = zx_polys(rng, n + 1)
    return [(ps[i], ps[i + 1]) for i in range(n)]


def pinned_pcmp(a, b):
    """The SPEC S7 total order: shorter first, then high index down."""
    if len(a) != len(b):
        return "%lt" if len(a) < len(b) else "%gt"
    for u, v in zip(reversed(a), reversed(b)):
        if u != v:
            return "%lt" if u < v else "%gt"
    return "%eq"


def zx_canon_rows(rng):
    """+canon:zx -- [in out].  Inputs are deliberately non-canonical."""
    cases = [
        ([], []),
        ([0], []),
        ([0, 0], []),
        ([0, 0, 0, 0], []),
        ([1, 0], [1]),
        ([0, 1], [0, 1]),
        ([0, 0, 1, 0, 0], [0, 0, 1]),
        ([1, 2, 3, 0], [1, 2, 3]),
        ([-1, 0, 0], [-1]),
    ]
    for p in zx_polys(rng, 40):
        # append a deterministic run of zeros; canon must strip all of them
        k = (len(p) % 3) + 1
        cases.append((p + [0] * k, p))
    return ["[%s %s]" % (zol(i), zol(o)) for i, o in cases]


def zx_deg_rows(rng):
    """+deg:zx -- [a d].  The zero polynomial crashes, so it is excluded."""
    ps = [p for p in zx_polys(rng, 48) if p]
    return ["[%s %s]" % (zol(p), ud(len(p) - 1)) for p in ps]


def zx_lc_rows(rng):
    """+lc:zx -- [a c].  The zero polynomial crashes, so it is excluded."""
    ps = [p for p in zx_polys(rng, 48) if p]
    return ["[%s %s]" % (zol(p), sd(p[-1])) for p in ps]


def zx_pcmp_rows(rng):
    """+pcmp:zx -- [a b o]."""
    rows = []
    pairs = zx_pairs(rng, 44)
    # a total order must be reflexive, so compare a few polys with themselves
    pairs += [(p, list(p)) for p in zx_polys(rng, 6)]
    for a, b in pairs:
        o = pinned_pcmp(a, b)
        # cross-check antisymmetry against the reversed comparison
        rev = pinned_pcmp(b, a)
        assert (o == "%eq") == (rev == "%eq")
        assert o != rev or o == "%eq"
        rows.append("[%s %s %s]" % (zol(a), zol(b), o))
    return rows


def zx_binop_rows(rng, op):
    rows = []
    for a, b in zx_pairs(rng, 48):
        c = of_poly(op(to_poly(a), to_poly(b)))
        rows.append("[%s %s %s]" % (zol(a), zol(b), zol(c)))
    return rows


def zx_neg_rows(rng):
    rows = []
    for p in zx_polys(rng, 48):
        rows.append("[%s %s]" % (zol(p), zol(of_poly(-to_poly(p)))))
    return rows


def zx_shift_rows(rng):
    """+shift:zx -- [a k c].  Multiplication by x^k."""
    rows = []
    ps = zx_polys(rng, 48)
    for i, p in enumerate(ps):
        k = i % 6
        c = of_poly(to_poly(p) * to_poly([0] * k + [1]))
        rows.append("[%s %s %s]" % (zol(p), ud(k), zol(c)))
    return rows


def zx_scale_rows(rng):
    """+scale:zx -- [a c out].  Scalar 0 must produce the zero polynomial."""
    rows = []
    scalars = [0, 1, -1, 2, -3, 7, -100, 2 ** 40]
    ps = zx_polys(rng, 48)
    for i, p in enumerate(ps):
        s = scalars[i % len(scalars)]
        c = of_poly(to_poly(p) * Poly(s, X, domain=ZZ))
        rows.append("[%s %s %s]" % (zol(p), sd(s), zol(c)))
    return rows


def zx_eval_rows(rng):
    """+eval:zx -- [a x y].  Horner against sympy evaluation."""
    rows = []
    points = [0, 1, -1, 2, -2, 3, -10, 1000, -(2 ** 20)]
    ps = zx_polys(rng, 48)
    for i, p in enumerate(ps):
        xv = points[i % len(points)]
        y = 0 if not p else int(to_poly(p).eval(xv))
        rows.append("[%s %s %s]" % (zol(p), sd(xv), sd(y)))
    return rows


# --------------------------------------------------------------------------


def main():
    rng = random.Random(SEED)

    print("  ::  /lib/racoon-vectors")
    print("::::  GENERATED FILE -- DO NOT EDIT")
    print("::")
    print("::  Regenerate with:  python3 tools/genvec.py")
    print("::")
    print("::  Reference vectors for the Racoon test suite, produced by an")
    print("::  independent oracle (SymPy, math.isqrt, fractions.Fraction).")
    print("::  PRNG seed %d; see tools/genvec.py for the oracle used per arm."
          % SEED)
    print("::")
    print("/-  *racoon")
    print("|%")
    print("::")

    emit("gcd-vectors", "(list [a=@ud b=@ud g=@ud])", gcd_rows(rng),
         "+gcd:nz, oracle math.gcd")
    emit("egcd-vectors", "(list [a=@ud b=@ud d=@ud u=@s v=@s])",
         egcd_rows(rng),
         "+egcd:nz, pinned EEA, checked against math.gcd and Bezout")
    emit("isqrt-vectors", "(list [a=@ud r=@ud])", isqrt_rows(rng),
         "+isqrt:nz, oracle math.isqrt")
    emit("is-prime-vectors", "(list [n=@ud p=?])", is_prime_rows(rng),
         "+is-prime:nz, oracle sympy.isprime")
    emit("crt-vectors",
         "(list [in=(list [r=@ud m=@ud]) r=@ud m=@ud])", crt_rows(rng),
         "+crt:nz, oracle sympy.ntheory.modular.crt")
    emit("ratrec-vectors",
         "(list [u=@ud m=@ud nb=@ud db=@ud out=(unit frac)])",
         ratrec_rows(rng),
         "+ratrec:nz, pinned Wang EEA, checked against the congruence")

    ft = "(list [a=frac b=frac c=frac])"
    emit("qq-add-vectors", ft,
         qq_binop_rows(rng, lambda a, b: a + b), "+add:qq, oracle Fraction")
    emit("qq-sub-vectors", ft,
         qq_binop_rows(rng, lambda a, b: a - b), "+sub:qq, oracle Fraction")
    emit("qq-mul-vectors", ft,
         qq_binop_rows(rng, lambda a, b: a * b), "+mul:qq, oracle Fraction")
    emit("qq-div-vectors", ft,
         qq_binop_rows(rng, lambda a, b: a / b, skip_zero_b=True),
         "+div:qq, oracle Fraction; divisors are nonzero")
    emit("qq-cmp-vectors", "(list [a=frac b=frac o=ord])", qq_cmp_rows(rng),
         "+cmp:qq, oracle Fraction ordering")
    emit("qq-new-vectors", "(list [p=@s q=@ud c=frac])", qq_new_rows(rng),
         "+new:qq, oracle Fraction; inputs are non-canonical")
    emit("qq-neg-vectors", "(list [a=frac c=frac])",
         qq_unary_rows(rng, lambda a: -a), "+neg:qq, oracle Fraction")
    emit("qq-inv-vectors", "(list [a=frac c=frac])",
         qq_unary_rows(rng, lambda a: 1 / a, nonzero=True),
         "+inv:qq, oracle Fraction; operands are nonzero")

    zt = "(list [a=zol b=zol c=zol])"
    emit("zx-canon-vectors", "(list [in=zol out=zol])", zx_canon_rows(rng),
         "+canon:zx; inputs carry trailing zeros")
    emit("zx-deg-vectors", "(list [a=zol d=@ud])", zx_deg_rows(rng),
         "+deg:zx; the zero polynomial crashes, so it is excluded")
    emit("zx-lc-vectors", "(list [a=zol c=@s])", zx_lc_rows(rng),
         "+lc:zx; the zero polynomial crashes, so it is excluded")
    emit("zx-pcmp-vectors", "(list [a=zol b=zol o=ord])", zx_pcmp_rows(rng),
         "+pcmp:zx, the pinned SPEC S7 order")
    emit("zx-add-vectors", zt,
         zx_binop_rows(rng, lambda p, q: p + q),
         "+add:zx, oracle sympy.Poly over ZZ")
    emit("zx-sub-vectors", zt,
         zx_binop_rows(rng, lambda p, q: p - q),
         "+sub:zx, oracle sympy.Poly over ZZ")
    emit("zx-mul-vectors", zt,
         zx_binop_rows(rng, lambda p, q: p * q),
         "+mul:zx, oracle sympy.Poly over ZZ")
    emit("zx-neg-vectors", "(list [a=zol c=zol])", zx_neg_rows(rng),
         "+neg:zx, oracle sympy.Poly over ZZ")
    emit("zx-shift-vectors", "(list [a=zol k=@ud c=zol])", zx_shift_rows(rng),
         "+shift:zx, oracle multiplication by x^k")
    emit("zx-scale-vectors", "(list [a=zol c=@s out=zol])",
         zx_scale_rows(rng),
         "+scale:zx, oracle sympy.Poly over ZZ")
    emit("zx-eval-vectors", "(list [a=zol x=@s y=@s])", zx_eval_rows(rng),
         "+eval:zx, oracle sympy Poly.eval")

    print("--")


if __name__ == "__main__":
    main()
