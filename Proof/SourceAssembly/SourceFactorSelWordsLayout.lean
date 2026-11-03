import Proof.Packets.SourceResidentCopies
import Proof.Packets.SourceResidentOccCount
import Proof.SourceAssembly.SLoadCore
import Proof.SourceAssembly.SourceFactorSelItem4Bank
import Proof.SourceAssembly.SourceFactorSelItem4Stages
import Proof.SourceAssembly.SourceFactorSelRunBound

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.Words
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section

/-! ## Sizes -/

/-- The local universe size. -/
def nW (w C k : Nat) : Nat := 754 + 2 * w + 2 * C + 2 * k
/-- W's region size in the host (everything from local `29` on). -/
def gwW (w C k : Nat) : Nat := 725 + 2 * w + 2 * C + 2 * k

theorem nW_eq (w C k : Nat) : nW w C k = 29 + gwW w C k := by unfold nW gwW; omega

def o4 (w : Nat) : Nat := 61 + w
def o5 (w C k : Nat) : Nat := 199 + w + C + k
def o6 (w C k : Nat) : Nat := 221 + 2 * w + C + k
def o7 (w C k : Nat) : Nat := 226 + 2 * w + C + k
def o8 (w C k : Nat) : Nat := 731 + 2 * w + 2 * C + 2 * k
def o9 (w C k : Nat) : Nat := 748 + 2 * w + 2 * C + 2 * k
def o10 (w C k : Nat) : Nat := 751 + 2 * w + 2 * C + 2 * k

/-- Unfold every size and close a linear goal. -/
macro "wz" : tactic => `(tactic| (simp only [nW, gwW, o4, o5, o6, o7, o8, o9, o10] at *; omega))

/-! ## The ten stage docks, by value -/

/-- Copies: sources `0..4` ↦ `0 2 5 6 7`; targets `5..11` ↦ `11 12 15 14 19 16 17`; the log `12` ↦ its block. -/
def t1 (j : Nat) : Nat :=
  match j with
  | 0 => 0 | 1 => 2 | 2 => 5 | 3 => 6 | 4 => 7 | 5 => 11 | 6 => 12 | 7 => 15 | 8 => 14 | 9 => 19 | 10 => 16 | _ => 17
def v1 (j : Nat) : Nat := if j < 12 then t1 j else 30 + j
/-- Occ: `0 1 2` ↦ `3 4 18`. -/
def t2 (j : Nat) : Nat := match j with | 0 => 3 | 1 => 4 | _ => 18
def v2 (j : Nat) : Nat := if j < 3 then t2 j else 43 + j
/-- LM: `0 2 3 4 5 7` ↦ `19 15 16 17 18 29`. -/
def t3 (j : Nat) : Nat := match j with | 0 => 19 | 1 => 48 | 2 => 15 | 3 => 16 | 4 => 17 | 5 => 18 | 6 => 53 | _ => 29
def v3 (j : Nat) : Nat := if j < 8 then t3 j else 47 + j
/-- Index block: `ixOut = 132+C+4` ↦ `13`; `ixIn j = 132+C+6+j` ↦ `0 2 6 1 29`. -/
def t4 (w C : Nat) (i : Nat) : Nat :=
  match i with | 0 => 13 | 1 => o4 w + (132 + C + 5) | 2 => 0 | 3 => 2 | 4 => 6 | 5 => 1 | _ => 29
def v4 (w C : Nat) (x : Nat) : Nat :=
  if 132 + C + 4 ≤ x ∧ x < 132 + C + 11 then t4 w C (x - (132 + C + 4)) else o4 w + x
/-- Input pass: `0 3 4 5 6 7 9 11 12 13 14 15` ↦ `28 11 12 13 14 20 21 15 16 17 18 19`. -/
def t5 (w C k : Nat) (j : Nat) : Nat :=
  match j with
  | 0 => 28 | 1 => o5 w C k + 1 | 2 => o5 w C k + 2 | 3 => 11 | 4 => 12 | 5 => 13 | 6 => 14 | 7 => 20
  | 8 => o5 w C k + 8 | 9 => 21 | 10 => o5 w C k + 10 | 11 => 15 | 12 => 16 | 13 => 17 | 14 => 18 | _ => 19
def v5 (w C k : Nat) (j : Nat) : Nat := if j < 16 then t5 w C k j else o5 w C k + j
/-- TK: `0 3` ↦ `8 27`. -/
def v6 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 8 else if j = 3 then 27 else o6 w C k + j
/-- Pool block: `plOut 98, 224` ↦ `25 26`; `plX 225, 226` ↦ `27 28`; `plIn j = 132+C+373+j` ↦ `0 2 6 1 29`. -/
def t7 (i : Nat) : Nat := match i with | 0 => 0 | 1 => 2 | 2 => 6 | 3 => 1 | _ => 29
def v7 (w C k p98 p224 : Nat) (x : Nat) : Nat :=
  if x = p98 then 25 else if x = p224 then 26
  else if 132 + C + 225 ≤ x ∧ x < 132 + C + 227 then x - (132 + C + 225) + 27
  else if 132 + C + 373 ≤ x ∧ x < 132 + C + 378 then t7 (x - (132 + C + 373)) else o7 w C k + x
/-- MS: `0 12 15` ↦ `25 26 24`. -/
def v8 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 25 else if j = 12 then 26 else if j = 15 then 24 else o8 w C k + j
/-- The two unframers: `0 1` ↦ `9 22` and `10 23`. -/
def v9 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 9 else if j = 1 then 22 else o9 w C k + j
def v10 (w C k : Nat) (j : Nat) : Nat := if j = 0 then 10 else if j = 1 then 23 else o10 w C k + j

section vals
variable (w C k : Nat)

theorem v1_cases (j : Nat) (hj : j < 13) : v1 j < 30 ∨ v1 j = 30 + j := by
  unfold v1; split_ifs with h
  · left; interval_cases j <;> decide
  · right; rfl
theorem v2_cases (j : Nat) (hj : j < 4) : v2 j < 30 ∨ v2 j = 43 + j := by
  unfold v2; split_ifs with h
  · left; interval_cases j <;> decide
  · right; rfl
theorem v3_cases (j : Nat) : v3 j < 30 ∨ v3 j = 47 + j := by
  unfold v3; split_ifs with h
  · interval_cases j <;> first | (left; decide) | (right; rfl)
  · right; rfl
theorem v4_cases (x : Nat) : v4 w C x < 30 ∨ v4 w C x = o4 w + x := by
  unfold v4; split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    generalize hi : x - (132 + C + 4) = i
    have hi' : i < 7 := by omega
    by_cases h1 : i = 1
    · right
      subst h1
      show o4 w + (132 + C + 5) = o4 w + x
      omega
    · left
      interval_cases i <;> first | (exact absurd rfl h1) | (simp [t4])
  · right; rfl
theorem v5_cases (j : Nat) : v5 w C k j < 30 ∨ v5 w C k j = o5 w C k + j := by
  unfold v5; split_ifs with h
  · interval_cases j <;> first | (left; simp [t5]; done) | (right; simp [t5])
  · right; rfl
theorem v6_cases (j : Nat) : v6 w C k j < 30 ∨ v6 w C k j = o6 w C k + j := by
  unfold v6; split_ifs <;> first | (left; decide) | (right; rfl)
theorem v7_cases (p98 p224 x : Nat) : v7 w C k p98 p224 x < 30 ∨ v7 w C k p98 p224 x = o7 w C k + x := by
  unfold v7; split_ifs with h1 h2 h3 h4
  · left; decide
  · left; decide
  · left; omega
  · left
    have hi : x - (132 + C + 373) < 5 := by omega
    generalize x - (132 + C + 373) = i at hi
    interval_cases i <;> decide
  · right; rfl
theorem v8_cases (j : Nat) : v8 w C k j < 30 ∨ v8 w C k j = o8 w C k + j := by
  unfold v8; split_ifs <;> first | (left; decide) | (right; rfl)
theorem v9_cases (j : Nat) : v9 w C k j < 30 ∨ v9 w C k j = o9 w C k + j := by
  unfold v9; split_ifs <;> first | (left; decide) | (right; rfl)
theorem v10_cases (j : Nat) : v10 w C k j < 30 ∨ v10 w C k j = o10 w C k + j := by
  unfold v10; split_ifs <;> first | (left; decide) | (right; rfl)

end vals

section maps
variable (w C k : Nat)

def m1 : Fin 13 → Fin (nW w C k) := fun j => ⟨v1 j.val, by have := j.isLt; have := v1_cases j.val this; wz⟩
def m2 : Fin 4 → Fin (nW w C k) := fun j => ⟨v2 j.val, by have := j.isLt; have := v2_cases j.val this; wz⟩
def m3 : Fin (9 + (5 + w)) → Fin (nW w C k) := fun j => ⟨v3 j.val, by have := j.isLt; have := v3_cases j.val; wz⟩
def m4 : Fin ((132 + C) + (6 + k)) → Fin (nW w C k) :=
  fun j => ⟨v4 w C j.val, by have := j.isLt; have := v4_cases w C j.val; wz⟩
def m5 : Fin (22 + w) → Fin (nW w C k) := fun j => ⟨v5 w C k j.val, by have := j.isLt; have := v5_cases w C k j.val; wz⟩
def m6 : Fin 5 → Fin (nW w C k) := fun j => ⟨v6 w C k j.val, by have := j.isLt; have := v6_cases w C k j.val; wz⟩
def m7 (p98 p224 : Nat) : Fin ((132 + C) + (373 + k)) → Fin (nW w C k) :=
  fun j => ⟨v7 w C k p98 p224 j.val, by have := j.isLt; have := v7_cases w C k p98 p224 j.val; wz⟩
def m8 : Fin 17 → Fin (nW w C k) := fun j => ⟨v8 w C k j.val, by have := j.isLt; have := v8_cases w C k j.val; wz⟩
def m9 : Fin 3 → Fin (nW w C k) := fun j => ⟨v9 w C k j.val, by have := j.isLt; have := v9_cases w C k j.val; wz⟩
def m10 : Fin 3 → Fin (nW w C k) := fun j => ⟨v10 w C k j.val, by have := j.isLt; have := v10_cases w C k j.val; wz⟩

/-! Injectivity through a left inverse on the shared ports. -/

/-! Left inverses on the shared ports (`< 30`). -/



end maps

/-! ## The target words, the producing stage, the bank invariant -/


end
end NearCubicWires.SourceFactorSel.Words

