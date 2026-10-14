import Zcash.Circuits.Action.RealBases
import Zcash.Circuits.Tests.TestVectors.OrchardGeneratorsData
import Zcash.Circuits.Tests.TestVectors.PointEncoding
import Zcash.Meta.AxiomCheck

/-!
# The Orchard generators against zcash-test-vectors

The six fixed bases and the three Sinsemilla domain points of the model are the points whose
compressed encodings are the `orchard_generators` vector of zcash-test-vectors.

## What is checked

Each `*_encoding` theorem states that the model's point compresses (`PointEncoding.encode`) to the
vector's bytes. Compression is injective on curve points (`PointEncoding.eq_of_encode_eq`), so the
model's point is the only curve point with that encoding: the comparison is at the decoded point
level.

## Method

The encodings are evaluated by `decide +kernel`.

The six fixed bases are certified definitions (`Ecc.MulFixed.Certs`) that depend on
`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt`, a `native_decide` owner named in
`Zcash.TrustBoundary`; the theorems that mention them are pinned with that owner. The theorems
about the three domain points use standard axioms only.
-/

namespace Zcash.Circuits.Tests.TestVectors.OrchardGenerators

open Zcash.Circuits
open Zcash.Circuits.Ecc.MulFixed.Certs
open Zcash.Circuits.Action (noteQ ivkQ merkleQ)
open Zcash.Circuits.Tests.TestVectors.PointEncoding

/-! ## The encodings -/

theorem spendAuthG_encoding : encode spendAuthG.point = generators.skb := by decide +kernel
theorem nullifierK_encoding : encode nullifierK.point = generators.nkb := by decide +kernel
theorem valueCommitV_encoding : encode valueCommitV.point = generators.vcvb := by decide +kernel
theorem valueCommitR_encoding : encode valueCommitR.point = generators.vcrb := by decide +kernel
theorem noteCommitR_encoding : encode noteCommitR.point = generators.cmb := by decide +kernel
theorem noteQ_encoding : encode noteQ = generators.cmq := by decide +kernel
theorem commitIvkR_encoding : encode commitIvkR.point = generators.ivkb := by decide +kernel
theorem ivkQ_encoding : encode ivkQ = generators.ivkq := by decide +kernel
theorem merkleQ_encoding : encode merkleQ = generators.mcq := by decide +kernel

/-! ## Census -/

assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.spendAuthG_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.nullifierK_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.valueCommitV_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.valueCommitR_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.noteCommitR_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.noteQ_encoding
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.commitIvkR_encoding
  +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.ivkQ_encoding
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardGenerators.merkleQ_encoding

end Zcash.Circuits.Tests.TestVectors.OrchardGenerators
