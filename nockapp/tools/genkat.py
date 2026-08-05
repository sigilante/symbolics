#!/usr/bin/env python3
"""genkat.py -- generate desk/lib/tip5-vectors.hoon from Nockchain's own KATs.

The witness is only worth something if the vectors come from the OTHER
implementation, so this reads them out of nockchain-official rather than
producing them here:

  hoon/tests/crypto/mod/tip5.hoon
      tip5-fixlen-kats   input 10 belts  -> output 5 belts   (+hash-10)
      tip5-varlen-kats   input n belts   -> output 5 belts   (+hash-varlen)
      both at num-rounds = 5, which is what that file exercises

  crates/ai-pow-zk/tests/fixtures/tip5_5round_golden_kat.txt
      IN/OUT pairs of 16 belts, the raw permutation, also 5 rounds

Nothing here interprets the numbers.  Constants -- the MDS column, the
round constants, the lookup table -- are deliberately NOT extracted: the
lookup table and the full MDS matrix are derived in /lib/tip5 from their
definitions, and the two irreducible constant blocks are transcribed by
hand so that a reviewer can diff them against the source.

Usage:  python3 tools/genkat.py [path-to-nockchain-official]
"""
import os
import re
import sys

NOCK = sys.argv[1] if len(sys.argv) > 1 else os.path.expanduser(
    "~/zorp/nockchain-official")
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                   "..", "desk", "lib", "tip5-vectors.hoon")

PERM_CAP = 100          # of 315 available; the rest add cost, not coverage


def dot(n):
    """Hoon's dotted decimal: 1234567 -> 1.234.567"""
    s, out = str(n), []
    while len(s) > 3:
        out.append(s[-3:])
        s = s[:-3]
    out.append(s)
    return ".".join(reversed(out))


def hoon_list(xs, indent):
    """A list literal, wrapped to stay under 80 columns.

    TALL form, `:~ ... ==`, not the irregular `~[...]`: the wide form has
    to fit on one line, and none of these do.  The empty list is `~`,
    since `:~  ==` is not a thing.
    """
    pad = " " * indent
    if not xs:
        return pad + "~"
    line, lines = pad + ":~  ", []
    for x in xs:
        tok = dot(x) + "  "
        if len(line) + len(tok) > 78:
            lines.append(line.rstrip())
            line = pad + "    "
        line += tok
    lines.append(line.rstrip())
    lines.append(pad + "==")
    return "\n".join(lines)


def read_hoon_kats(path):
    """Both KAT lists out of the Nockchain test file, as (name, [(in, out)])."""
    text = open(path).read()
    out = {}
    for name in ("tip5-fixlen-kats", "tip5-varlen-kats"):
        start = text.index("++  " + name)
        end = len(text)
        for other in ("++  tip5-fixlen-kats", "++  tip5-varlen-kats"):
            k = text.find(other, start + 4)
            if k != -1:
                end = min(end, k)
        body = text[start:end]
        # one block per vector; inside it the operands are `~` or `~[...]`,
        # input then output.  The bare `~` is real -- the first varlen
        # vector hashes the empty list -- so this cannot just scan for
        # bracket pairs.
        pairs = []
        for block in body.split("^-  tip5-tv")[1:]:
            ops = []
            for raw in block.splitlines():
                ln = raw.strip()
                if ln == "~":
                    ops.append([])
                elif ln.startswith("~[") and ln.endswith("]"):
                    ops.append([int(t.replace(".", ""))
                                for t in ln[2:-1].split()])
            assert len(ops) == 2, (name, len(ops))
            pairs.append((ops[0], ops[1]))
        out[name] = pairs
    return out


def read_golden(path):
    """IN/OUT pairs from the Rust golden KAT."""
    pairs, cur = [], None
    for line in open(path):
        f = line.split()
        if not f:
            continue
        if f[0] == "IN":
            cur = [int(x) for x in f[1:]]
        elif f[0] == "OUT" and cur is not None:
            pairs.append((cur, [int(x) for x in f[1:]]))
            cur = None
    return pairs


def emit(fh, name, pairs, note):
    fh.write("::    +%s:  %s\n" % (name, note))
    fh.write("++  %s\n  ^-  (list kat)\n  :~\n" % name)
    for i, (a, b) in enumerate(pairs):
        fh.write("    :-\n")
        fh.write(hoon_list(a, 6) + "\n")
        fh.write(hoon_list(b, 6) + "\n")
    fh.write("  ==\n")


def read_constants(path):
    """The two round-constant blocks and the MDS column, out of three.hoon.

    Every constant is written dotted and every one is >= 10^8, so a token
    with at least one dot group is a constant and the bare 5 and 7 in the
    `?>  ?|(=(num-rounds 5) ...)` guard are not.  Order is load-bearing:
    the file lists the 80-constant block first.
    """
    text = open(path).read()
    a = text.index("++  round-constants")
    b = text.index("++  mds-matrix-first-column")
    c = text.index("++  mds-first-column-fft")
    nums = [int(t.replace(".", ""))
            for t in re.findall(r"\d+(?:\.\d{3})+", text[a:b])]
    assert len(nums) == 192, len(nums)
    col = [int(t.replace(".", ""))
           for t in re.findall(r"\d+(?:\.\d{3})+", text[b:c])]
    assert len(col) == 16, len(col)
    return {"rc-alt5": nums[:80], "rc-canon": nums[80:], "mds-column": col}


def emit_flat(fh, name, xs, note):
    fh.write("::    +%s:  %s\n" % (name, note))
    fh.write("++  %s\n  ^-  (list @ud)\n%s\n" % (name, hoon_list(xs, 2)))


def write_constants(consts):
    out = os.path.join(os.path.dirname(OUT), "tip5-constants.hoon")
    with open(out, "w") as fh:
        fh.write("""  ::  /lib/tip5-constants
::::  Tip5's design constants -- GENERATED, never hand-edited
::
::  Extracted by tools/genkat.py from nockchain-official's
::  hoon/common/ztd/three.hoon.  These are the two blocks /lib/tip5
::  cannot derive: nothing generates them, they are choices made when
::  Tip5 was designed.
::
::  MECHANICALLY EXTRACTED RATHER THAN TYPED.  This project has been
::  bitten before -- four Swinnerton-Dyer coefficients were wrong the
::  first time they were written out by hand -- and 208 sixty-four-bit
::  constants is exactly the shape of that mistake.
::
::  ALL IN PLAIN FORM, in [0, p).  Nockchain stores the round constants
::  montified because it adds them to Montgomery representatives;
::  /lib/tip5 montifies them itself, so what appears here is what the
::  specification says.
::
::  THERE ARE TWO ROUND-CONSTANT BLOCKS AND THEY ARE NOT THE SAME.
::  See /lib/tip5's header: `Tip5 with 5 rounds` names two different
::  functions in nockchain-official, and both are carried here so that
::  both published sets of vectors can be checked.
::
|%
""")
        emit_flat(fh, "rc-canon", consts["rc-canon"],
                  "112 constants, the canonical Tip5 schedule")
        emit_flat(fh, "rc-alt5", consts["rc-alt5"],
                  "80 constants, ztd/three.hoon's num-rounds=5 branch")
        emit_flat(fh, "mds-column", consts["mds-column"],
                  "the MDS matrix's first column; the rest is circulant")
        fh.write("--\n")
    print("constants -> %s" % os.path.normpath(out))


def main():
    write_constants(read_constants(
        os.path.join(NOCK, "hoon/common/ztd/three.hoon")))
    kats = read_hoon_kats(
        os.path.join(NOCK, "hoon/tests/crypto/mod/tip5.hoon"))
    golden = os.path.join(
        NOCK, "crates/ai-pow-zk/tests/fixtures/tip5_5round_golden_kat.txt")
    perm = read_golden(golden)
    # the published lookup table, as a VECTOR: /lib/tip5 derives its own
    # from the cube map, and the suite checks the two against each other
    lookup = [int(x) for x in
              open(golden).read().split("LOOKUP")[1].split("\n")[0].split()]
    assert len(lookup) == 256, len(lookup)
    fix, var = kats["tip5-fixlen-kats"], kats["tip5-varlen-kats"]
    perm = perm[:PERM_CAP]

    with open(OUT, "w") as fh:
        fh.write("""  ::  /lib/tip5-vectors
::::  Known-answer vectors for /lib/tip5 -- GENERATED, never hand-edited
::
::  Produced by tools/genkat.py from nockchain-official.  These are the
::  OTHER implementation's answers, which is the entire point: agreeing
::  with vectors this repository produced itself would demonstrate
::  nothing.
::
::  Sources, both at num-rounds = 5:
::    +fixlen, +varlen   hoon/tests/crypto/mod/tip5.hoon
::    +permute           crates/ai-pow-zk/tests/fixtures/
::                         tip5_5round_golden_kat.txt
::
::  .i and .o are plain field elements in [0, p).  Montgomery form is
::  internal to the permutation and never appears here.
::
|%
+$  kat  [i=(list @) o=(list @)]
""")
        emit(fh, "fixlen", fix,
             "input 10 belts, output 5 -- +hash-10")
        emit(fh, "varlen", var,
             "input n belts, output 5 -- +hash-varlen")
        emit(fh, "permute", perm,
             "input 16 belts, output 16 -- the bare permutation")
        emit_flat(fh, "lookup", lookup,
                  "the published S-box table, to check the derived one")
        fh.write("--\n")

    print("fixlen %d, varlen %d, permute %d (of %d) -> %s"
          % (len(fix), len(var), len(perm), PERM_CAP, os.path.normpath(OUT)))


main()
