#!/usr/bin/env python3
"""Render pinned zcash-test-vectors data as a Lean module.

Usage: python3 -I scripts/test_vectors_to_lean.py <zcash-test-vectors checkout> <revision>

Reads `test-vectors/json/orchard_poseidon.json`, `test-vectors/json/orchard_poseidon_hash.json`
and the round constants, MDS matrix and capacity element of the generator
`zcash_test_vectors/orchard/poseidon.py`, and writes the Lean module to stdout.

Nothing from the checkout is imported or executed: the JSON is parsed with `json`, and the
generator's constants are read from its syntax tree with `ast`. Field elements in the JSON are
32-byte little-endian encodings; each is decoded to an integer and must be canonical (below the
Pallas base-field modulus), otherwise the script fails.
"""

import ast
import json
import os
import sys

PALLAS_P = 0x40000000000000000000000000000000224698FC094CF91B992D30ED00000001


def die(msg):
    sys.stderr.write("test_vectors_to_lean.py: " + msg + "\n")
    sys.exit(1)


def decode(hexstr, what):
    raw = bytes.fromhex(hexstr)
    if len(raw) != 32:
        die("%s: expected 32 bytes, got %d" % (what, len(raw)))
    n = int.from_bytes(raw, "little")
    if n >= PALLAS_P:
        die("%s: non-canonical encoding (>= p)" % what)
    return n


def load_rows(path, header):
    with open(path) as f:
        rows = json.load(f)
    if len(rows) < 2 or rows[1] != [header]:
        die("%s: unexpected header %r" % (path, rows[1] if len(rows) > 1 else None))
    return rows[2:]


def int_of(node, what):
    """Evaluate the integer literals the generator uses: `0x..`, `Fp(..)`, `1 << k`."""
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "Fp" \
            and len(node.args) == 1 and not node.keywords:
        return int_of(node.args[0], what)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.LShift):
        return int_of(node.left, what) << int_of(node.right, what)
    die("%s: unsupported expression %s" % (what, ast.dump(node)))


def generator_constants(path):
    with open(path) as f:
        tree = ast.parse(f.read(), filename=path)
    assigns = {}
    for stmt in tree.body:
        if isinstance(stmt, ast.Assign) and len(stmt.targets) == 1 \
                and isinstance(stmt.targets[0], ast.Name):
            assigns[stmt.targets[0].id] = stmt.value
    for name in ("R_F", "R_P", "t", "ROUND_CONSTANTS", "MDS_MATRIX", "CAPACITY_ELEMENT"):
        if name not in assigns:
            die("%s: no top-level assignment to %s" % (path, name))
    r_f, r_p, t = (int_of(assigns[n], n) for n in ("R_F", "R_P", "t"))
    # ROUND_CONSTANTS = [Fp(x) for x in chain.from_iterable([[..], [..], ...])]
    rc = assigns["ROUND_CONSTANTS"]
    if not (isinstance(rc, ast.ListComp) and isinstance(rc.generators[0].iter, ast.Call)
            and len(rc.generators[0].iter.args) == 1
            and isinstance(rc.generators[0].iter.args[0], ast.List)):
        die("ROUND_CONSTANTS: unexpected shape")
    rows = rc.generators[0].iter.args[0].elts
    round_constants = []
    for i, row in enumerate(rows):
        if not (isinstance(row, ast.List) and len(row.elts) == t):
            die("ROUND_CONSTANTS row %d: expected %d entries" % (i, t))
        round_constants.append([int_of(e, "ROUND_CONSTANTS[%d]" % i) for e in row.elts])
    if len(round_constants) != r_f + r_p:
        die("ROUND_CONSTANTS: %d rows, expected R_F + R_P = %d" % (len(round_constants), r_f + r_p))
    mds_node = assigns["MDS_MATRIX"]
    if not (isinstance(mds_node, ast.List) and len(mds_node.elts) == t):
        die("MDS_MATRIX: unexpected shape")
    mds = []
    for i, row in enumerate(mds_node.elts):
        if not (isinstance(row, ast.List) and len(row.elts) == t):
            die("MDS_MATRIX row %d: unexpected shape" % i)
        mds.append([int_of(e, "MDS_MATRIX[%d]" % i) for e in row.elts])
    capacity = int_of(assigns["CAPACITY_ELEMENT"], "CAPACITY_ELEMENT")
    flat = [x for row in round_constants + mds for x in row] + [capacity]
    for v in flat:
        if v >= PALLAS_P:
            die("generator constant not reduced mod p")
    return r_f, r_p, t, round_constants, mds, capacity


def h(n):
    return "0x%064x" % n


def main():
    if len(sys.argv) != 3:
        die("usage: test_vectors_to_lean.py <zcash-test-vectors checkout> <revision>")
    root, rev = sys.argv[1], sys.argv[2]
    perm_rows = load_rows(os.path.join(root, "test-vectors/json/orchard_poseidon.json"),
                          "initial_state, final_state")
    hash_rows = load_rows(os.path.join(root, "test-vectors/json/orchard_poseidon_hash.json"),
                          "input, output")
    r_f, r_p, t, rc, mds, capacity = generator_constants(
        os.path.join(root, "zcash_test_vectors/orchard/poseidon.py"))

    perm = []
    for i, (inp, out) in enumerate(perm_rows):
        if len(inp) != 3 or len(out) != 3:
            die("orchard_poseidon vector %d: expected width-3 states" % i)
        perm.append(([decode(x, "orchard_poseidon[%d].initial_state" % i) for x in inp],
                     [decode(x, "orchard_poseidon[%d].final_state" % i) for x in out]))
    hashes = []
    for i, (inp, out) in enumerate(hash_rows):
        if len(inp) != 2:
            die("orchard_poseidon_hash vector %d: expected two inputs" % i)
        hashes.append(([decode(x, "orchard_poseidon_hash[%d].input" % i) for x in inp],
                       decode(out, "orchard_poseidon_hash[%d].output" % i)))

    out = []
    w = out.append
    w("-- Auto-generated by `scripts/regenerate-test-vectors.sh` from zcash/zcash-test-vectors@%s."
      " Do not edit by hand." % rev)
    w("")
    w("import Zcash.Circuits.Poseidon.Constants")
    w("")
    w("/-!")
    w("# zcash-test-vectors: Orchard Poseidon")
    w("")
    w("The `orchard_poseidon` and `orchard_poseidon_hash` vectors of")
    w("[zcash-test-vectors](https://github.com/zcash/zcash-test-vectors) at revision")
    w("`%s`, and the round constants, MDS matrix and capacity" % rev)
    w("element of their generator `zcash_test_vectors/orchard/poseidon.py`.")
    w("")
    w("Each field element is the integer its canonical 32-byte little-endian encoding denotes; the")
    w("converter rejects a non-canonical encoding, so every value here is below the Pallas")
    w("base-field modulus. `scripts/regenerate-test-vectors.sh` regenerates this file")
    w("byte-for-byte.")
    w("-/")
    w("")
    w("namespace Zcash.Circuits.Tests.TestVectors.OrchardPoseidon")
    w("")
    w("open Zcash.Circuits.Poseidon.Permute (State)")
    w("")
    w("/-- One `orchard_poseidon` vector: the permutation maps `input` to `output`. -/")
    w("structure PermutationVector where")
    w("  input : State Nat")
    w("  output : State Nat")
    w("")
    w("/-- One `orchard_poseidon_hash` vector: the two-input hash maps `(x, y)` to `output`. -/")
    w("structure HashVector where")
    w("  x : Nat")
    w("  y : Nat")
    w("  output : Nat")
    w("")
    w("/-- The generator's full-round count `R_F`. -/")
    w("def fullRounds : Nat := %d" % r_f)
    w("")
    w("/-- The generator's partial-round count `R_P`. -/")
    w("def partialRounds : Nat := %d" % r_p)
    w("")
    w("/-- The generator's state width `t`. -/")
    w("def width : Nat := %d" % t)
    w("")

    def state(row):
        return "{ x0 := %s, x1 := %s, x2 := %s }" % (h(row[0]), h(row[1]), h(row[2]))

    def items(name, typ, rows):
        w("def %s : List %s := [" % (name, typ))
        for i, row in enumerate(rows):
            w("  %s%s" % (row, "," if i + 1 < len(rows) else ""))
        w("]")
        w("")

    w("/-- The generator's `ROUND_CONSTANTS`, one row per round (%d rows). -/" % len(rc))
    items("roundConstants", "(State Nat)", [state(r) for r in rc])
    w("/-- The generator's `MDS_MATRIX`, row by row. -/")
    items("mds", "(List Nat)", ["[%s]" % ", ".join(h(x) for x in r) for r in mds])
    w("/-- The generator's `CAPACITY_ELEMENT`, the capacity word of the two-input hash. -/")
    w("def capacityElement : Nat := %s" % h(capacity))
    w("")
    w("/-- `orchard_poseidon.json` (%d vectors). -/" % len(perm))
    items("permutation", "PermutationVector",
          ["{ input := %s,\n    output := %s }" % (state(a), state(b)) for a, b in perm])
    w("/-- `orchard_poseidon_hash.json` (%d vectors). -/" % len(hashes))
    items("hash", "HashVector",
          ["{ x := %s, y := %s,\n    output := %s }" % (h(a[0]), h(a[1]), h(b)) for a, b in hashes])
    w("end Zcash.Circuits.Tests.TestVectors.OrchardPoseidon")
    sys.stdout.write("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
