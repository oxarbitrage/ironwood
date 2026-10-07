# zcash-test-vectors fixtures

The Lean models of the deployed primitives mirror the Rust sources they port. These
fixtures check them against [zcash-test-vectors](https://github.com/zcash/zcash-test-vectors),
the cross-implementation anchor, so that a transcription faithfully mirroring a wrong or
drifted source still fails (ironwood#204).

| File | What it is |
|---|---|
| `OrchardPoseidonData.lean` | Generated: the `orchard_poseidon` and `orchard_poseidon_hash` vectors, and the round constants, MDS matrix and capacity element of their generator `zcash_test_vectors/orchard/poseidon.py`. |
| `OrchardPoseidon.lean` | Hand-written: the ported constants equal the generator's; `Permute.value` and the two-input `Hash.ConstantLength.value` reproduce every vector. |
| `MANIFEST.tsv` | Per-artifact provenance: path, sha256, generator, source revision, invocation. |

Generated files open with the converter's header and must not be edited by hand.
`scripts/regenerate-test-vectors.sh` checks them against `MANIFEST.tsv`, then regenerates
them from the pinned commit and diffs them byte-for-byte; `--check-manifest` checks the
digests without a clone, and `--write` rewrites the fixtures and the manifest.

The comparison is at the field-element level: each vector entry is the integer its
canonical 32-byte little-endian encoding denotes, and a non-canonical encoding fails the
converter. Byte-level encodings are out of scope here.
