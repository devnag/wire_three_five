import Proof.Wire_3_5.Primitive.SeedFix.W6G

/-! # W6, part 8: the prime cutoff and the radix length

P3:2552-2553 (the tuned prime surrogate's cutoff, "a polynomial-size set of polynomially bounded primes":
`canonicalPrimeCutoff E K = (max 24 (6(E+1)(K+1)))²` with `E` the family's magnitude exponent and `K` the
denominator) and P3:2596-2597 ("`b_0 = 2` and `τ_0 = ⌈log₂ cutoff⌉`"), as register runs (`W6G`):
* **`cutW`** / **`cutW_rr`**: `rCut := canonicalPrimeCutoff E K` from `rE = E`, `rK = K` (`max 24 s = s + (24 - s)`),
  scratch `0 … 14` at `0` and restored, cost `20·(opU+1)`; built from `cutA` (`P = (E+1)(K+1)`, `6P`), `cutB`
  (`m = max 24 (6P)`, `m²`) and `cutC` (the scratch cleared);
* **`tauW`** / **`tauW_rr`**: `rTau := ⌈log₂ cut⌉` (`SymQM.clogW`), scratch `0 … 7`, cost `opU`.

Paper quantities of the main types: the prime cutoff and `τ₀`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

/-! ## The prime cutoff -/

def Rc1 : Fin 5 ↪ Fin 80 := ⟨![0, 1, 2, 7, 8], by decide⟩
def Rc2 : Fin 5 ↪ Fin 80 := ⟨![3, 2, 4, 7, 8], by decide⟩
def Rs : Fin 4 ↪ Fin 80 := ⟨![9, 4, 11, 12], by decide⟩
def Rc3 : Fin 5 ↪ Fin 80 := ⟨![4, 14, 56, 7, 8], by decide⟩

/-- `r0 := E+1`, `r1 := K+1`, `r2 := P = (E+1)(K+1)`, `r3 := 6`, `r4 := 6P`. -/
def cutA : WP :=
  .seq (wcopyR rE 0 5) (.seq (.inc 0) (.seq (wcopyR rK 1 5) (.seq (.inc 1) (.seq (UnaryArith.mulAddW Rc1) (.seq (StarNums.incN 3 6) (UnaryArith.mulAddW Rc2))))))

/-- `r9 := 24 - s`, `r4 := s + (24 - s) = max 24 s`, `r14 := r4`, `r56 := r4²`. -/
def cutB : WP :=
  .seq (StarNums.incN 9 24) (.seq (UnaryArith.subW Rs) (.seq (ParseNat.addTo 9 4 12) (.seq (wcopyR 4 14 5) (UnaryArith.mulAddW Rc3))))

/-- The scratch cleared. -/
def cutC : WP :=
  .seq (WM.clear 0) (.seq (WM.clear 1) (.seq (WM.clear 2) (.seq (WM.clear 3) (.seq (WM.clear 4) (.seq (WM.clear 9) (WM.clear 14))))))

/-- `rCut := (max 24 (6(E+1)(K+1)))²`. -/
def cutW : WP := .seq cutA (.seq cutB cutC)

theorem cutA_rr (f : Fin 80 → ℕ) (E K P : ℕ) (hP : (E + 1) * (K + 1) = P) (hE : f 54 = E) (hK : f 55 = K)
    (z0 : f 0 = 0) (z1 : f 1 = 0) (z2 : f 2 = 0) (z3 : f 3 = 0) (z4 : f 4 = 0) (z5 : f 5 = 0) (z7 : f 7 = 0)
    (z8 : f 8 = 0) (hcap : 6 * P ≤ cap) :
    RegRun cap cutA f (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (E)) 0 (E + 1)) 1 (K)) 1 (K + 1)) 2 (P)) 3 (6)) 4 (6 * P)) (7 * (opU cap + 1)) := by
  have hEP : E + 1 ≤ P := hP ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hKP : K + 1 ≤ P := hP ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hU := lin_le_opU cap
  refine RegRun.mono cap ((wcopy_rr cap 54 0 5 (by decide) (by decide) (by decide) f E hE z0 z5 (by rw [hE]; omega)).seq cap
    ((inc_rr cap 0 _ (E + 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)).seq cap
    ((wcopy_rr cap 55 1 5 (by decide) (by decide) (by decide) _ K (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, hK]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z1])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, hK]; omega)).seq cap
    ((inc_rr cap 1 _ (K + 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)).seq cap
    ((mulAdd_rr cap Rc1 0 1 2 7 8 rfl rfl rfl rfl rfl _ P (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z2, Nat.zero_add, hP])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z7]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z8]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z2, Nat.zero_add, hP]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)).seq cap
    ((incN_rr cap 3 6 _ 6 (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z3, Nat.zero_add]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z3]; omega)).seq cap
    ((mulAdd_rr cap Rc2 3 2 4 7 8 rfl rfl rfl rfl rfl _ (6 * P) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z4, Nat.zero_add])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z7]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z8]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z4, Nat.zero_add]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega))))))))) (by omega)

theorem cutB_rr (f : Fin 80 → ℕ) (s m : ℕ) (hm : s + (24 - s) = m) (h4 : f 4 = s) (z5 : f 5 = 0) (z7 : f 7 = 0)
    (z8 : f 8 = 0) (z9 : f 9 = 0) (z11 : f 11 = 0) (z12 : f 12 = 0) (z14 : f 14 = 0) (h56 : f 56 = 0)
    (hmc : m * m ≤ cap) :
    RegRun cap cutB f (Function.update (Function.update (Function.update (Function.update (Function.update f 9 (24)) 9 (24 - s)) 4 (m)) 14 (m)) 56 (m * m)) (5 * (opU cap + 1)) := by
  have hsm : s ≤ m := by omega
  have h24 : 24 ≤ m := by omega
  have hmm : m ≤ m * m := Nat.le_mul_self m
  have hU := lin_le_opU cap
  refine RegRun.mono cap ((incN_rr cap 9 24 f 24 (by simp only [z9, Nat.zero_add]) (by rw [z9]; omega)).seq cap
    ((sub_rr cap Rs 9 4 11 12 rfl rfl rfl rfl _ (24 - s) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, h4]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z11])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z12]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, h4]; omega)).seq cap
    ((addTo_rr cap 9 4 12 (by decide) (by decide) (by decide) _ m (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, h4]; exact hm)
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z12]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, h4]; omega)).seq cap
    ((wcopy_rr cap 4 14 5 (by decide) (by decide) (by decide) _ m (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z14])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z5]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)).seq cap
    ((mulAdd_rr cap Rc3 4 14 56 7 8 rfl rfl rfl rfl rfl _ (m * m) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, h56, Nat.zero_add])
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z7]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z8]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)
      (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, h56, Nat.zero_add]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega))))))) (by omega)

theorem cutC_rr (f : Fin 80 → ℕ) (b0 : f 0 ≤ cap) (b1 : f 1 ≤ cap) (b2 : f 2 ≤ cap) (b3 : f 3 ≤ cap) (b4 : f 4 ≤ cap)
    (b9 : f 9 ≤ cap) (b14 : f 14 ≤ cap) :
    RegRun cap cutC f (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 9 (0)) 14 (0)) (7 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  refine RegRun.mono cap ((clear_rr cap 0 f b0).seq cap
    ((clear_rr cap 1 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact b1)).seq cap
    ((clear_rr cap 2 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact b2)).seq cap
    ((clear_rr cap 3 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact b3)).seq cap
    ((clear_rr cap 4 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact b4)).seq cap
    ((clear_rr cap 9 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact b9)).seq cap
    ((clear_rr cap 14 _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; exact b14))))))))) (by omega)

theorem cut_regs (f : Fin 80 → ℕ) (E K P m : ℕ) (z0 : f 0 = 0) (z1 : f 1 = 0) (z2 : f 2 = 0) (z3 : f 3 = 0)
    (z4 : f 4 = 0) (z9 : f 9 = 0) (z14 : f 14 = 0) :
    Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update ((Function.update (Function.update (Function.update (Function.update (Function.update ((Function.update (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update f 0 (E)) 0 (E + 1)) 1 (K)) 1 (K + 1)) 2 (P)) 3 (6)) 4 (6 * P))) 9 (24)) 9 (24 - (6 * P))) 4 (m)) 14 (m)) 56 (m * m))) 0 (0)) 1 (0)) 2 (0)) 3 (0)) 4 (0)) 9 (0)) 14 (0) = Function.update f 56 (m * m) := by
  funext r
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]
  split_ifs <;> subst_vars <;> simp_all

theorem cutW_rr (f : Fin 80 → ℕ) (E K : ℕ) (hE : f rE = E) (hK : f rK = K)
    (hz : ∀ r : Fin 80, r.val < 15 → f r = 0) (hc0 : f rCut = 0)
    (hcap : SupplierPrime.canonicalPrimeCutoff E K ≤ cap) :
    RegRun cap cutW f (Function.update f rCut (SupplierPrime.canonicalPrimeCutoff E K)) (20 * (opU cap + 1)) := by
  have hE' : f 54 = E := hE
  have hK' : f 55 = K := hK
  have hc' : f 56 = 0 := hc0
  have z0 : f 0 = 0 := hz 0 (by decide)
  have z1 : f 1 = 0 := hz 1 (by decide)
  have z2 : f 2 = 0 := hz 2 (by decide)
  have z3 : f 3 = 0 := hz 3 (by decide)
  have z4 : f 4 = 0 := hz 4 (by decide)
  have z5 : f 5 = 0 := hz 5 (by decide)
  have z7 : f 7 = 0 := hz 7 (by decide)
  have z8 : f 8 = 0 := hz 8 (by decide)
  have z9 : f 9 = 0 := hz 9 (by decide)
  have z11 : f 11 = 0 := hz 11 (by decide)
  have z12 : f 12 = 0 := hz 12 (by decide)
  have z14 : f 14 = 0 := hz 14 (by decide)
  obtain ⟨P, hP⟩ : ∃ P, (E + 1) * (K + 1) = P := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, max 24 (6 * P) = m := ⟨_, rfl⟩
  have hcut : SupplierPrime.canonicalPrimeCutoff E K = m * m := by
    unfold SupplierPrime.canonicalPrimeCutoff SupplierPrime.canonicalPrimeScale
    rw [mul_assoc, hP, hm, pow_two]
  have hEP : E + 1 ≤ P := hP ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hKP : K + 1 ≤ P := hP ▸ Nat.le_mul_of_pos_left _ (by omega)
  have h24 : 24 ≤ m := hm ▸ le_max_left _ _
  have h6P : 6 * P ≤ m := hm ▸ le_max_right _ _
  have hmm : m ≤ m * m := Nat.le_mul_self m
  have hmc : m * m ≤ cap := hcut ▸ hcap
  have hm' : 6 * P + (24 - 6 * P) = m := by
    rw [← hm, max_def]; split_ifs <;> omega
  have hU := lin_le_opU cap
  have c := (cutA_rr cap f E K P hP hE' hK' z0 z1 z2 z3 z4 z5 z7 z8 (by omega)).seq cap
    ((cutB_rr cap _ (6 * P) m hm' (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z5])
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z7]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z8]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z9]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z11])
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z12]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, z14]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, hc']) hmc).seq cap
    (cutC_rr cap _ (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)
    (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false]; omega)))
  refine (c.congr cap ?_).mono cap (by omega)
  rw [hcut]
  exact cut_regs f E K P m z0 z1 z2 z3 z4 z9 z14

/-! ## The radix length -/

def Sq : Fin 10 ↪ Fin 80 := ⟨![56, 57, 0, 1, 2, 3, 4, 5, 6, 7], by decide⟩

/-- `rTau := ⌈log₂ cut⌉`. -/
def tauW : WP := SymQM.clogW Sq

theorem tauW_rr (f : Fin 80 → ℕ) (c : ℕ) (hc : f rCut = c) (ht : f rTau = 0) (hz : ∀ r : Fin 80, r.val < 8 → f r = 0)
    (hcap : c + 2 ≤ cap) :
    RegRun cap tauW f (Function.update f rTau (Nat.clog 2 c)) (opU cap) := by
  have hc' : f 56 = c := hc
  have ht' : f 57 = 0 := ht
  have z0 : f 0 = 0 := hz 0 (by decide)
  have z1 : f 1 = 0 := hz 1 (by decide)
  have z2 : f 2 = 0 := hz 2 (by decide)
  have z3 : f 3 = 0 := hz 3 (by decide)
  have z4 : f 4 = 0 := hz 4 (by decide)
  have z5 : f 5 = 0 := hz 5 (by decide)
  have z6 : f 6 = 0 := hz 6 (by decide)
  have z7 : f 7 = 0 := hz 7 (by decide)
  exact clog_rr cap Sq 56 57 rfl rfl f (Nat.clog 2 c) (by rw [hc']) (fun i hi => by
      fin_cases i
      · exact absurd hi (by decide)
      all_goals simp [Sq, ht', z0, z1, z2, z3, z4, z5, z6, z7]) (by rw [hc']; exact hcap)

end NearCubicWires.WireExponent3_5.PrimT.W6
