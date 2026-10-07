import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Zcash.Circuits.Poseidon.HashTheorems
import Zcash.Circuits.Tests.TestVectors.OrchardPoseidonData
import Zcash.Meta.AxiomCheck

/-!
# Orchard Poseidon against zcash-test-vectors

The Lean model of Orchard's `P128Pow5T3` mirrors `halo2_poseidon/src/fp.rs` (constants) and
`halo2_gadgets/src/poseidon/pow5.rs` (schedule). This module checks it against the shared
[zcash-test-vectors](https://github.com/zcash/zcash-test-vectors), at the revision pinned in
`OrchardPoseidonData.lean`, so that a transcription faithfully mirroring a wrong source fails.

## What is checked

* `roundConstants_eq_generator`, `mds_eq_generator`: the ported round constants and MDS matrix
  equal those of the vectors' generator, `zcash_test_vectors/orchard/poseidon.py`, transcribed
  separately from the same Grain parameter script;
* `permute_value_eq_vector`: `Permute.value` maps every `orchard_poseidon` input state to its
  output state;
* `constantLength_value_eq_vector`: the two-input `Hash.ConstantLength.value`, which the
  nullifier derivation applies to `(nk, ρ)`, maps every `orchard_poseidon_hash` input to its
  output.

The comparison is at the field-element level: each vector entry is the integer its 32-byte
little-endian encoding denotes. Byte-level encoding is out of scope.

## Method

Evaluating the field-level model in the kernel is impractically slow, because of the `ZMod`
instance layer (see `Zcash/Circuits/Tests/BenchFixedBase.lean`). So the vectors are evaluated on
`permN`, a `Nat` mirror of the same schedule that reduces modulo `p` after every operation, and
`toState_permN` transfers the result to `Fp` once, for every input.
-/

namespace Zcash.Circuits.Tests.TestVectors.OrchardPoseidon

open Zcash.Circuits.Poseidon
open Zcash.Circuits.Poseidon.Permute (State)

/-- The Pallas base-field modulus. -/
abbrev p : Nat := CompElliptic.Fields.Pasta.PALLAS_BASE_CARD

/-- The field state an integer state denotes. -/
def toState (s : State Nat) : State Fp := { x0 := s.x0, x1 := s.x1, x2 := s.x2 }

/-- Field-wise equality of integer states, as a `Bool` the kernel can evaluate. -/
def beqN (a b : State Nat) : Bool := a.x0 == b.x0 && a.x1 == b.x1 && a.x2 == b.x2

/-- `beqN` decides equality: it turns the kernel's `Bool` checks into equations. -/
theorem eq_of_beqN {a b : State Nat} (h : beqN a b = true) : a = b := by
  cases a; cases b; simp_all [beqN]

/-! ## The generator's constants, by index -/

/-- Round `r` of the generator's round constants. -/
def rcN (r : Nat) : State Nat := roundConstants.getD r { x0 := 0, x1 := 0, x2 := 0 }

/-- Entry `(i, j)` of the generator's MDS matrix. -/
def mdsN (i j : Nat) : Nat := (mds.getD i []).getD j 0

/-! ## A `Nat`-level mirror of the schedule -/

/-- `x ↦ x⁵ mod p`, in the shape of `pow5`. -/
def pow5N (x : Nat) : Nat :=
  let x2 := x * x % p
  x2 * x2 % p * x % p

/-- The MDS matrix applied to a state, modulo `p`. -/
def mixN (s : State Nat) : State Nat :=
  { x0 := (s.x0 * mdsN 0 0 + s.x1 * mdsN 0 1 + s.x2 * mdsN 0 2) % p
    x1 := (s.x0 * mdsN 1 0 + s.x1 * mdsN 1 1 + s.x2 * mdsN 1 2) % p
    x2 := (s.x0 * mdsN 2 0 + s.x1 * mdsN 2 1 + s.x2 * mdsN 2 2) % p }

/-- One full round at source round `r`, mirroring `FullRound.value`. -/
def fullN (r : Nat) (s : State Nat) : State Nat :=
  mixN
    { x0 := pow5N ((s.x0 + (rcN r).x0) % p)
      x1 := pow5N ((s.x1 + (rcN r).x1) % p)
      x2 := pow5N ((s.x2 + (rcN r).x2) % p) }

/-- One partial-round row (source rounds `r` and `r + 1`), mirroring `PartialRounds.value`. -/
def partialN (r : Nat) (s : State Nat) : State Nat :=
  let mid := mixN
    { x0 := pow5N ((s.x0 + (rcN r).x0) % p)
      x1 := (s.x1 + (rcN r).x1) % p
      x2 := (s.x2 + (rcN r).x2) % p }
  mixN
    { x0 := pow5N ((mid.x0 + (rcN (r + 1)).x0) % p)
      x1 := (mid.x1 + (rcN (r + 1)).x1) % p
      x2 := (mid.x2 + (rcN (r + 1)).x2) % p }

/-- Apply `f k`, `f (k + 1)`, …, `f (k + n - 1)` in order. Structural recursion, so the kernel
evaluates it directly (`Fin.foldl` is well-founded recursion). -/
def iterN (f : Nat → State Nat → State Nat) : Nat → Nat → State Nat → State Nat
  | _, 0, s => s
  | k, n + 1, s => iterN f (k + 1) n (f k s)

/-- The `Nat`-level permutation: 4 full rounds, 28 partial-round rows, 4 full rounds. -/
def permN (s : State Nat) : State Nat :=
  iterN (fun i => fullN (4 + 56 + i)) 0 4 <|
    iterN (fun i => partialN (4 + 2 * i)) 0 28 <|
      iterN (fun i => fullN i) 0 4 s

/-! ## Kernel checks over `Nat` -/

/-- The generator's shape is the `P128Pow5T3` schedule: width 3, `R_F = 8` (4 + 4) and
`R_P = 56` (28 two-round rows), one constant row per round, a 3×3 MDS matrix, and capacity
`2·2⁶⁴`. -/
theorem generator_shape :
    width = 3 ∧ fullRounds = 8 ∧ partialRounds = 56 ∧ roundConstants.length = 64 ∧
    mds.length = 3 ∧ (mds.all fun row => row.length == 3) = true ∧
    capacityElement = 2 * 2 ^ 64 := by
  decide +kernel

/-- The `Nat` mirror maps every `orchard_poseidon` input state to its output state. -/
theorem permN_vectors : (permutation.all fun v => beqN (permN v.input) v.output) = true := by
  decide +kernel

/-- The `Nat` mirror's first output word, on `(x, y, capacity)`, is every
`orchard_poseidon_hash` output. -/
theorem permN_hash_vectors :
    (hash.all fun v =>
      (permN { x0 := v.x, x1 := v.y, x2 := capacityElement }).x0 == v.output) = true := by
  decide +kernel

/-! ## The ported constants equal the generator's -/

/-- The ported round constants equal the generator's, round by round. -/
theorem roundConstants_eq_generator (r : Nat) (hr : r < 64) :
    Permute.P128Pow5T3.roundConstants r = toState (rcN r) := by
  interval_cases r <;>
    simp only [Permute.P128Pow5T3.roundConstants, Permute.P128Pow5T3.fromRaw, toState, rcN,
      roundConstants, List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num

/-- The ported MDS matrix equals the generator's, entry by entry. -/
theorem mds_eq_generator (i j : Nat) (hi : i < 3) (hj : j < 3) :
    Permute.P128Pow5T3.mds i j = (mdsN i j : Fp) := by
  interval_cases i <;> interval_cases j <;>
    simp only [Permute.P128Pow5T3.mds, Permute.P128Pow5T3.fromRaw, mdsN, mds,
      List.getD_cons_succ, List.getD_cons_zero] <;>
    norm_num

/-! ## Transport from `Nat` to `Fp` -/

/-- `pow5N` denotes `pow5`. -/
theorem cast_pow5N (x : Nat) : ((pow5N x : Nat) : Fp) = pow5 (x : Fp) := by
  simp only [pow5N, pow5, Nat.cast_mul, ZMod.natCast_mod]

/-- `mixN` denotes the ported MDS matrix applied to the state. -/
theorem toState_mixN (a b c : Nat) :
    toState (mixN { x0 := a, x1 := b, x2 := c }) =
      { x0 := a * Permute.P128Pow5T3.mds 0 0 + b * Permute.P128Pow5T3.mds 0 1 +
          c * Permute.P128Pow5T3.mds 0 2
        x1 := a * Permute.P128Pow5T3.mds 1 0 + b * Permute.P128Pow5T3.mds 1 1 +
          c * Permute.P128Pow5T3.mds 1 2
        x2 := a * Permute.P128Pow5T3.mds 2 0 + b * Permute.P128Pow5T3.mds 2 1 +
          c * Permute.P128Pow5T3.mds 2 2 } := by
  simp (disch := decide) only [toState, mixN, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    mds_eq_generator]

/-- One `Nat` full round denotes `FullRound.value` at the ported constants. -/
theorem toState_fullN (r : Nat) (hr : r < 64) (s : State Nat) :
    toState (fullN r s) =
      FullRound.value (FullRound.params Permute.P128Pow5T3.roundConstants
        Permute.P128Pow5T3.mds r) (toState s) := by
  have hrc := roundConstants_eq_generator r hr
  rw [fullN, toState_mixN]
  simp only [FullRound.value, FullRound.params, hrc, toState, cast_pow5N, ZMod.natCast_mod,
    Nat.cast_add]

/-- One `Nat` partial-round row denotes `PartialRounds.value` at the ported constants. -/
theorem toState_partialN (r : Nat) (hr : r + 1 < 64) (s : State Nat) :
    toState (partialN r s) =
      PartialRounds.value (PartialRounds.paramsP128 Permute.P128Pow5T3.roundConstants r)
        (toState s) := by
  have hrc := roundConstants_eq_generator r (by omega)
  have hrc' := roundConstants_eq_generator (r + 1) hr
  simp only [partialN, PartialRounds.value, PartialRounds.mid0SboxValue,
    PartialRounds.paramsP128, PartialRounds.params, hrc, hrc']
  rw [toState_mixN]
  simp (disch := decide) only [toState, mixN, cast_pow5N, ZMod.natCast_mod, Nat.cast_add,
    Nat.cast_mul, mds_eq_generator]

/-- `iterN` denotes the matching `Fin.foldl`, given that each step denotes its counterpart. -/
theorem toState_iterN (f : Nat → State Nat → State Nat) (F : Nat → State Fp → State Fp) :
    ∀ (n k : Nat) (s : State Nat),
      (∀ i t, k ≤ i → i < k + n → toState (f i t) = F i (toState t)) →
      toState (iterN f k n s) = Fin.foldl n (fun st i => F (k + i.val) st) (toState s)
  | 0, _, _, _ => by simp [iterN]
  | n + 1, k, s, h => by
    rw [iterN, toState_iterN f F n (k + 1) (f k s) (fun i t h1 h2 => h i t (by omega) (by omega)),
      Fin.foldl_succ, h k s (by omega) (by omega)]
    simp only [Fin.val_succ, Fin.val_zero, Nat.add_zero]
    congr 1
    funext st i
    congr 1
    omega

/-- The `Nat` mirror denotes `Permute.value` at the ported constants, on every input. -/
theorem toState_permN (s : State Nat) :
    toState (permN s) = Permute.value Permute.P128Pow5T3.roundConstants (toState s) := by
  have h1 := toState_iterN (fun i => fullN i)
    (fun i => FullRound.value (FullRound.params Permute.P128Pow5T3.roundConstants
      Permute.P128Pow5T3.mds i)) 4 0 s
    (fun i t _ hi => toState_fullN i (by omega) t)
  have h2 := toState_iterN (fun i => partialN (4 + 2 * i))
    (fun i => PartialRounds.value
      (PartialRounds.paramsP128 Permute.P128Pow5T3.roundConstants (4 + 2 * i))) 28 0
    (iterN (fun i => fullN i) 0 4 s)
    (fun i t _ hi => toState_partialN (4 + 2 * i) (by omega) t)
  have h3 := toState_iterN (fun i => fullN (4 + 56 + i))
    (fun i => FullRound.value (FullRound.params Permute.P128Pow5T3.roundConstants
      Permute.P128Pow5T3.mds (4 + 56 + i))) 4 0
    (iterN (fun i => partialN (4 + 2 * i)) 0 28 (iterN (fun i => fullN i) 0 4 s))
    (fun i t _ hi => toState_fullN (4 + 56 + i) (by omega) t)
  simp only [Nat.zero_add] at h1 h2 h3
  rw [permN, h3, h2, h1, Permute.value]

/-! ## The model against the vectors -/

/-- `Permute.value` at the ported constants maps every `orchard_poseidon` input state to its
output state. -/
theorem permute_value_eq_vector :
    ∀ v ∈ permutation,
      Permute.value Permute.P128Pow5T3.roundConstants (toState v.input) = toState v.output := by
  intro v hv
  rw [← toState_permN, eq_of_beqN (List.all_eq_true.mp permN_vectors v hv)]

/-- The two-input `Hash.ConstantLength.value` maps every `orchard_poseidon_hash` input to its
output. -/
theorem constantLength_value_eq_vector :
    ∀ v ∈ hash, Hash.ConstantLength.value #v[(v.x : Fp), (v.y : Fp)] = (v.output : Fp) := by
  intro v hv
  have hcap : Hash.ConstantLength.capacity 2 = (capacityElement : Fp) := by
    rw [generator_shape.2.2.2.2.2.2]
    simp [Hash.ConstantLength.capacity]
  have hperm := toState_permN { x0 := v.x, x1 := v.y, x2 := capacityElement }
  have hout := eq_of_beq (List.all_eq_true.mp permN_hash_vectors v hv)
  calc Hash.ConstantLength.value #v[(v.x : Fp), (v.y : Fp)]
      = (Permute.value Permute.P128Pow5T3.roundConstants
          (toState { x0 := v.x, x1 := v.y, x2 := capacityElement })).x0 := by
        simp [Hash.ConstantLength.value, Hash.ConstantLength.blockCount,
          Hash.ConstantLength.stepValueAt, Hash.ConstantLength.absorbPermuteValue,
          Permute.concreteValue, Hash.ConstantLength.blockValue, Hash.ConstantLength.paddedWord,
          Sponge.AddInput.value, Sponge.GetOutput.value, toState, hcap, Fin.foldl_succ,
          Fin.foldl_zero]
    _ = (v.output : Fp) := by rw [← hperm, ← hout]; rfl

/-! ## Census -/

assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.eq_of_beqN
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.generator_shape
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.permN_vectors
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.permN_hash_vectors
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.roundConstants_eq_generator
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.mds_eq_generator
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.cast_pow5N
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.toState_mixN
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.toState_fullN
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.toState_partialN
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.toState_iterN
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.toState_permN
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.permute_value_eq_vector
assert_axioms Zcash.Circuits.Tests.TestVectors.OrchardPoseidon.constantLength_value_eq_vector

end Zcash.Circuits.Tests.TestVectors.OrchardPoseidon
