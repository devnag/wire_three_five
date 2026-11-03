import Proof.Wire_3_5.Primitive.SeedFix.W6M
import Proof.Wire_3_5.Filters.GF2Primitive

/-! # W6, part 14: the modulus search's entry words

P3:2121-2157 (filt:majorant: the field `GF(2^{ℓ₀})` of the fixed hash, its modulus `p` the first primitive
polynomial of degree `ℓ₀`, `Majorant.refMod = GF.firstPrimitive ℓ₀`): the numbers machine runs C1's verified
search `GF2.searchM` (`search_run`) on fifteen of its streams; this part writes the search's entry words
(the frames of `binary ℓ₀ 0`, `binary ℓ₀ 1`, `binary ℓ₀ (2^{ℓ₀}-1)`, the scratch `0^{2ℓ₀+2}`):
* the words: `binary_zero`, `binary_max`, `binary_one`, `frame_rep`, `frame_one`, `zeros_rep`;
* **`wPRT_exec`**: `pre ++ (A copies of u) ++ tail` written on a blank stream, head back at `0`, registers kept.

Paper quantity of the main types: the search's entry words (the degree `ℓ₀` in binary frames). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (cap : ℕ)

/-! ## The words -/

theorem binary_zero : ∀ ℓ : ℕ, binary ℓ 0 = List.replicate ℓ false
  | 0 => rfl
  | ℓ + 1 => by
    show (0 % 2 == 1) :: binary ℓ (0 / 2) = false :: List.replicate ℓ false
    rw [Nat.zero_div, binary_zero ℓ]
    rfl

theorem binary_max : ∀ ℓ : ℕ, binary ℓ (2 ^ ℓ - 1) = List.replicate ℓ true
  | 0 => rfl
  | ℓ + 1 => by
    have hp : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
    have h3 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
    have h1 : (2 ^ (ℓ + 1) - 1) % 2 = 1 := by omega
    have h2 : (2 ^ (ℓ + 1) - 1) / 2 = 2 ^ ℓ - 1 := by omega
    show ((2 ^ (ℓ + 1) - 1) % 2 == 1) :: binary ℓ ((2 ^ (ℓ + 1) - 1) / 2) = true :: List.replicate ℓ true
    rw [h1, h2, binary_max ℓ]
    rfl

theorem binary_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : binary ℓ 1 = true :: List.replicate (ℓ - 1) false := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  show (1 % 2 == 1) :: binary k (1 / 2) = true :: List.replicate (k + 1 - 1) false
  rw [show (1 : ℕ) / 2 = 0 from rfl, binary_zero, Nat.add_sub_cancel]
  rfl

theorem reps_succ' (n : ℕ) (u : List Bool) : FiltRec.reps (n + 1) u = u ++ FiltRec.reps n u := by
  unfold FiltRec.reps
  rw [List.replicate_succ, List.flatten_cons]

theorem frame_rep (b : Bool) : ∀ ℓ : ℕ, frame (List.replicate ℓ b) = FiltRec.reps ℓ [true, b] ++ [false]
  | 0 => rfl
  | ℓ + 1 => by
    rw [List.replicate_succ, reps_succ', frame, frame_rep b ℓ]
    rfl

theorem frame_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    frame (binary ℓ 1) = [true, true] ++ FiltRec.reps (ℓ - 1) [true, false] ++ [false] := by
  rw [binary_one ℓ hℓ, frame, frame_rep]
  rfl

theorem zeros_rep : ∀ ℓ : ℕ, List.replicate (2 * ℓ + 2) false = FiltRec.reps ℓ [false, false] ++ [false, false]
  | 0 => rfl
  | ℓ + 1 => by
    rw [FiltRec.reps_succ, show 2 * (ℓ + 1) + 2 = (2 * ℓ + 2) + 2 by ring, List.replicate_add, zeros_rep ℓ]
    rfl

/-! ## A word on a blank stream -/

/-- `pre`, then `A` copies of `u`, then `tail`, on stream `O`; the head back at `0`. -/
def wPRT (O : Fin 192) (A : Fin 80) (pre u tail : List Bool) : WP :=
  .seq (.seq (Emit.emitW O qOP pre) (.seq (Emit.repRegW O qOP A 77 78 u) (Emit.emitW O qOP tail))) (WM.rewind O qOP)

theorem wPRT_exec (O : Fin 192) (A : Fin 80) (hA77 : A ≠ 77) (hA78 : A ≠ 78) (hAq : A ≠ qOP) (pre u tail : List Bool)
    (σ : WL) (a : ℕ) (ha : σ.val A = a) (hst : σ.st O = []) (hsh : σ.sh O = 0) (hop : σ.val qOP = 0)
    (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (hpre : pre.length ≤ 2) (hu : u.length ≤ 2) (htl : tail.length ≤ 2)
    (hb : 2 * a + 4 ≤ cap) :
    WExec cap (wPRT O A pre u tail) σ (σ.sets O (pre ++ FiltRec.reps a u ++ tail)) (4 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have hlen : (FiltRec.reps a u).length = a * u.length := by unfold FiltRec.reps; simp
  have hlr : a * u.length ≤ 2 * a := by nlinarith
  have hmul : a * (8 * u.length + 4) ≤ 20 * a := by nlinarith
  have q77 : (77 : Fin 80) ≠ qOP := by decide
  have q78 : (78 : Fin 80) ≠ qOP := by decide
  have e1 := Emit.emitW_spec cap O qOP pre σ (by rw [hsh, hst]; rfl) (by rw [hop]; omega)
  have hA1 : (WriteNat.appendO σ O qOP pre).val A = a := by
    rw [WriteNat.appendO_val, Function.update_of_ne hAq, ha]
  have e2 := Emit.repRegW_spec cap O qOP A 77 78 hA77 hA78 (by decide) q77 u (WriteNat.appendO σ O qOP pre)
    (by rw [WriteNat.appendO_val, Function.update_of_ne q77, z77])
    (by rw [WriteNat.appendO_val, Function.update_of_ne q78, z78])
    (by rw [WriteNat.appendO_sh, WriteNat.appendO_st, Function.update_self, Function.update_self, hsh, hst]; simp)
    (by rw [hA1]; omega)
    (by rw [hA1, WriteNat.appendO_val, Function.update_self, hop]; omega)
  rw [hA1] at e2
  have e3 := Emit.emitW_spec cap O qOP tail (WriteNat.appendO (WriteNat.appendO σ O qOP pre) O qOP (FiltRec.reps a u))
    (by simp only [WriteNat.appendO_sh, WriteNat.appendO_st, Function.update_self, hsh, hst, List.length_append,
      List.nil_append]; omega)
    (by simp only [WriteNat.appendO_val, Function.update_self, hop, hlen]; omega)
  rw [WriteNat.appendO_append, WriteNat.appendO_append] at e3
  have e4 := wrewind_spec cap O qOP (pre ++ FiltRec.reps a u ++ tail).length
    (WriteNat.appendO σ O qOP (pre ++ FiltRec.reps a u ++ tail)) (by simp [hop]) (by simp [hop, hlen]; omega)
  rw [WriteNat.appendO_append] at e2
  refine WExec.cast cap (WExec.seq (WExec.seq e1 (WExec.seq e2 e3)) e4) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases hj : j = O
      · subst hj
        simp [hsh]
      · simp [Function.update_of_ne hj]
    · funext j
      by_cases hj : j = O
      · subst hj
        simp [hst]
      · simp [Function.update_of_ne hj]
    · funext r
      by_cases hr : r = qOP
      · subst hr
        simp [hop]
      · simp [Function.update_of_ne hr]
    · simp
  · simp only [List.length_append, hlen]
    omega

end NearCubicWires.WireExponent3_5.PrimT.W6
