import Setup.Sizes

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Joins
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu)
open NearCubicGates.Close.Worker.Format (readCount readField)

theorem two_pow_size (v : ℕ) : 2 ^ v.size ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp
  · have h1 : 1 ≤ v.size := by
      rw [Nat.one_le_iff_ne_zero]; intro h; rw [Nat.size_eq_zero] at h; omega
    have h2 : ¬ v.size ≤ v.size - 1 := by omega
    rw [Nat.size_le] at h2
    have h3 : 2 ^ v.size = 2 * 2 ^ (v.size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-! ## The evaluator's cost -/

theorem evalCost_le (dl lb lp : ℕ) :
    Succinct.evalCost dl lb lp ≤ 100000 * (dl + 2 ^ (lb + lp) + lb + lp + 2) ^ 3 := by
  have hlb : 2 ^ lb ≤ 2 ^ (lb + lp) := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold Succinct.evalCost Succinct.nodeCost Succinct.fieldCost
  generalize 2 ^ (lb + lp) = T at hlb ⊢
  generalize 2 ^ lb = U at hlb ⊢
  obtain ⟨X, hX⟩ : ∃ X, X = dl + T + lb + lp + 2 := ⟨_, rfl⟩
  rw [← hX]
  have hX2 : 2 ≤ X := by omega
  have f1 : 400 * (dl + lb + 2) * (U + 1) ≤ 400 * (X * X) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have f2 : 400 * (dl + (lb + lp) + 2) * (T + 1) ≤ 400 * (X * X) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
  have hXX : X ≤ X * X := Nat.le_mul_self X
  have h400 : 4 ≤ X * X := Nat.mul_le_mul hX2 hX2
  obtain ⟨P1, hP1⟩ : ∃ P, P = 400 * (dl + (lb + lp) + 2) * (T + 1) := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, P = 400 * (dl + lb + 2) * (U + 1) := ⟨_, rfl⟩
  rw [← hP1] at f2 ⊢
  rw [← hP2] at f1 ⊢
  have e3 : X * X ≤ X * X * X := Nat.le_mul_of_pos_right _ (by omega)
  have e4 : X ^ 3 = X * X * X := by ring
  have e2 : (X + 4) * (2000 * (X * X) + 100) ≤ 30000 * (X * X * X) := by nlinarith
  have e1 : (U + 4) * (4 * P1 + 100 * T + 40 * U + 40 * (lb + lp) + 400 + 100) ≤
      (X + 4) * (2000 * (X * X) + 100) := Nat.mul_le_mul (by omega) (by omega)
  rw [e4]
  obtain ⟨X3, hX3⟩ : ∃ Y, Y = X * X * X := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Y, Y = (U + 4) * (4 * P1 + 100 * T + 40 * U + 40 * (lb + lp) + 400 + 100) := ⟨_, rfl⟩
  obtain ⟨Q', hQ'⟩ : ∃ Y, Y = (X + 4) * (2000 * (X * X) + 100) := ⟨_, rfl⟩
  rw [← hX3] at e2 e3 ⊢
  rw [← hQ] at e1 ⊢
  rw [← hQ'] at e1 e2
  omega

/-! ## Phase K -/

/-! ## Phase R -/

/-! ## The guessed fields -/

/-! ## Phase B -/

/-! ## The pad-free sizes of an accepting run -/

section Core

end Core

end NearCubicGates.Close.Setup
