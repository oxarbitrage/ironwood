import Zcash.Circuits.Specs.Pallas
import Zcash.Meta.AxiomCheck

/-!
# Pallas point encodings for the zcash-test-vectors checks

zcash-test-vectors gives points as 32-byte compressed encodings. A check compresses the model's
point and compares bytes, then uses injectivity to conclude that the model's point is the only
curve point with that encoding. The comparison is at the decoded point level, and no square root
is computed.

## What is checked

`encode` is the protocol's Pallas point compression `repr_P`: the x-coordinate in the low 255 bits
and the parity of the y-coordinate in bit 255, read as a little-endian integer. `eq_of_encode_eq`
shows it is injective on curve points.
-/

namespace Zcash.Circuits.Tests.TestVectors.PointEncoding

open Zcash.Circuits

/-- Pallas point compression: `x` in the low 255 bits, the parity of `y` in bit 255. -/
def encode (pt : Point Fp) : Nat := pt.x.val + 2 ^ 255 * (pt.y.val % 2)

/-- Compression is injective on curve points. -/
theorem eq_of_encode_eq {P Q : Point Fp} (hP : P.OnCurve) (hQ : Q.OnCurve)
    (h : encode P = encode Q) : P = Q := by
  have hp : CompElliptic.Fields.Pasta.PALLAS_BASE_CARD < 2 ^ 255 := by decide
  have hPx := ZMod.val_lt P.x
  have hQx := ZMod.val_lt Q.x
  have hPy := Nat.mod_lt P.y.val (by norm_num : 0 < 2)
  have hQy := Nat.mod_lt Q.y.val (by norm_num : 0 < 2)
  unfold encode at h
  have hx : P.x.val = Q.x.val := by omega
  have hpar : P.y.val % 2 = Q.y.val % 2 := by omega
  have hx' : Q.x = P.x := (ZMod.val_injective _ hx).symm
  have hPx0 : P.x ≠ 0 := by
    intro h0
    obtain ⟨x, y⟩ := P
    subst h0
    exact Point.no_onCurve_of_x_zero y hP
  rcases Point.y_eq_or_neg_of_same_x (Or.inl hP) (Or.inl hQ) hPx0 (hx' ▸ hPx0) hx' with hy | hy
  · cases P; cases Q; simp_all
  · by_cases hy0 : P.y = 0
    · cases P; cases Q; simp_all
    · exfalso
      haveI : NeZero P.y := ⟨hy0⟩
      have hneg := ZMod.val_neg_of_ne_zero P.y
      rw [← hy] at hneg
      have hodd : CompElliptic.Fields.Pasta.PALLAS_BASE_CARD % 2 = 1 := by decide
      have hlt := ZMod.val_lt P.y
      have hpos : 0 < P.y.val := (ZMod.val_pos).mpr hy0
      omega

/-! ## Census -/

assert_axioms Zcash.Circuits.Tests.TestVectors.PointEncoding.eq_of_encode_eq

end Zcash.Circuits.Tests.TestVectors.PointEncoding
