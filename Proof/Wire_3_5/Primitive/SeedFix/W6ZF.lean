import Proof.Wire_3_5.Primitive.SeedFix.W6ZE

/-! # W6, part 32: the fourteen THR numbers of a call at the call's base

P3:2552-2557 (`K = 8(|𝒢|+1)n^D`), P3:2552-2553 (the cutoff), P3:2573-2580 (`|primes|`, `Σp`, `τ₀`), P3:2121-2157 and
P3:2220-2231 (`A`, `B_*`, `J`, `t`, `e`, `ℓ₀`, the modulus): at a THR call (`a' ≤ 4`, `descriptionBits ≤ (n+1)^{26}`,
`|carriers| ≤ 2`), with `N = thrN alg P cap_T` (the call's base, `thr_basic`), every one of the fourteen numbers
`thrNumVals` is at most `N^{10D+137}` (P3:3114-3115: "All powers of `n` are fixed before a fixed `r`"):
* the field equations `v_nG … v_pMod` (definitional);
* `vb_nG`, `vb_den`, `vb_cut`, `vb_nPr`, `vb_pSum`, `vb_dig`, `vb_M`, `vb_A`, `vb_Bs`, `vb_KAB`, `vb_J`, `vb_2J`,
  `vb_KAJ`, `vb_tt`, `vb_ee`, `vb_ell0`, `vb_2ell`, `vb_pMod`;
* **`vb_get`**: `thrNumVals.get k ≤ N^{10D+137}` for every `k`.

Paper quantities of the main type: the fourteen THR numbers, each `≤ N^{10D+137}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

variable (alg : DecompositionAlgorithm)

theorem thrN16 (P : StarParams) (capT : ℕ) : 16 ≤ thrN alg P capT := by unfold thrN; omega

variable (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (ncar capT : ℕ)

theorem v_nG : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG = Fintype.card (Primitive.ThrEq P Cs alg) := rfl
theorem v_den : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den = 8 * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG + 1) * P.n ^ Dexp := rfl
theorem v_cut : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut = canonicalPrimeCutoff (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den := rfl
theorem v_nPr : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr = (primesUpTo (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut).card := rfl
theorem v_pSum : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).pSum = PrimAsm.ThrQ.primeSum (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut := rfl
theorem v_dig : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig = Nat.clog 2 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut := rfl
theorem v_A : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A = (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig * 2)) := rfl
theorem v_Bs : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs = a' * (4096 * ((ncar + 1) * (4096 * capT))) := rfl
theorem v_J : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J = Nat.clog 2 (8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + 1) := rfl
theorem v_tt : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).tt = Nat.clog 2 (8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J + 1) + 1 := rfl
theorem v_ee : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ee = Primitive.listE (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den := rfl
theorem v_ell0 : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 = max ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J + 1) (Nat.clog 2 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M) := rfl
theorem v_pMod : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).pMod = GF.firstPrimitive (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 := rfl

variable (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
include ha hd

theorem vb_nG : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG ≤ (thrN alg P capT) ^ 4 := (thr_basic alg P Cs capT ha hd).1

theorem vb_den : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den ≤ (thrN alg P capT) ^ (Dexp + 6) := by
  rw [v_den]; exact bK (thrN16 alg P capT) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG P.n Dexp (vb_nG alg Dexp P Cs ncar capT ha hd) (thr_basic alg P Cs capT ha hd).2.2.2.2.2.1

theorem vb_cut : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut ≤ (thrN alg P capT) ^ (2 * Dexp + 24) := by
  rw [v_cut]; exact bCut (thrN16 alg P capT) _ (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den Dexp (thr_basic alg P Cs capT ha hd).2.1 (vb_den alg Dexp P Cs ncar capT ha hd)

theorem vb_nPr : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr ≤ (thrN alg P capT) ^ (2 * Dexp + 25) := by
  have hN := thrN16 alg P capT
  rw [v_nPr]; exact pw_mono (by omega) (bPr hN (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut (2 * Dexp + 24) (vb_cut alg Dexp P Cs ncar capT ha hd)) (by omega)

theorem vb_pSum : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).pSum ≤ (thrN alg P capT) ^ (4 * Dexp + 49) := by
  have hN := thrN16 alg P capT
  rw [v_pSum]; exact pw_mono (by omega) (bPs hN (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut (2 * Dexp + 24) (vb_cut alg Dexp P Cs ncar capT ha hd)) (by omega)

theorem vb_dig : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig ≤ (thrN alg P capT) ^ (2 * Dexp + 24) := by
  rw [v_dig]; exact bDig (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut (2 * Dexp + 24) (vb_cut alg Dexp P Cs ncar capT ha hd)

theorem vb_M : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M ≤ (thrN alg P capT) ^ 2 := (thr_basic alg P Cs capT ha hd).2.2.1

theorem vb_A : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A ≤ (thrN alg P capT) ^ (4 * Dexp + 54) := by
  have hN := thrN16 alg P capT
  have hpr : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr ≤ (thrN alg P capT) ^ (2 * Dexp + 24 + 1) := vb_nPr alg Dexp P Cs ncar capT ha hd
  rw [v_A]
  exact pw_mono (by omega) (bA hN (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig (2 * Dexp + 24) (vb_nG alg Dexp P Cs ncar capT ha hd) hpr (vb_dig alg Dexp P Cs ncar capT ha hd)) (by omega)

variable (hnc : ncar ≤ 2)
include hnc

theorem vb_Bs : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs ≤ (thrN alg P capT) ^ 9 := by
  rw [v_Bs]; exact bB (thrN16 alg P capT) a' ncar capT ha hnc (thr_basic alg P Cs capT ha hd).2.2.2.2.2.2.1

theorem vb_KAB : 8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + 3 ≤ (thrN alg P capT) ^ (5 * Dexp + 71) := by
  have hN := thrN16 alg P capT
  exact pw_mono (by omega) (bKAB hN (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (Dexp + 6) (4 * Dexp + 54) 9 (vb_den alg Dexp P Cs ncar capT ha hd) (vb_A alg Dexp P Cs ncar capT ha hd) (vb_Bs alg Dexp P Cs ncar capT ha hd hnc)) (by omega)

theorem vb_J : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J ≤ (thrN alg P capT) ^ (5 * Dexp + 71) := by
  have h := vb_KAB alg Dexp P Cs ncar capT ha hd hnc
  rw [v_J]; exact bClog (8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs) (5 * Dexp + 71) (by omega)

theorem vb_2J : 2 ^ (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J ≤ (thrN alg P capT) ^ (5 * Dexp + 72) := by
  have hN := thrN16 alg P capT
  have h := vb_KAB alg Dexp P Cs ncar capT ha hd hnc
  rw [v_J]; exact b2Clog hN (8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs) (5 * Dexp + 71) (by omega)

theorem vb_KAJ : 8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J + 3 ≤ (thrN alg P capT) ^ (10 * Dexp + 133) := by
  have hN := thrN16 alg P capT
  exact pw_mono (by omega) (bKAB hN (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J (Dexp + 6) (4 * Dexp + 54) (5 * Dexp + 71) (vb_den alg Dexp P Cs ncar capT ha hd) (vb_A alg Dexp P Cs ncar capT ha hd) (vb_J alg Dexp P Cs ncar capT ha hd hnc)) (by omega)

theorem vb_tt : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).tt ≤ (thrN alg P capT) ^ (10 * Dexp + 134) := by
  have hN := thrN16 alg P capT
  have h0 := vb_KAJ alg Dexp P Cs ncar capT ha hd hnc
  have h := bClog (N := (thrN alg P capT)) (8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J) (10 * Dexp + 133) (by omega)
  rw [v_tt]
  exact pw_mono (by omega) (pw_succ hN h 1 (by omega)) (by omega)

theorem vb_ee : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ee ≤ (thrN alg P capT) ^ (10 * Dexp + 136 + 1) := by
  have hN := thrN16 alg P capT
  refine (Nat.le_of_eq (v_ee alg Dexp P Cs ncar capT)).trans ((listE_le _ _ _ _).trans ?_)
  have h8 : 8 ≤ (thrN alg P capT) ^ 1 := by rw [pow_one]; omega
  have hKA := pw_mul (pw_mul h8 (vb_den alg Dexp P Cs ncar capT ha hd)) (vb_A alg Dexp P Cs ncar capT ha hd)
  have htM := pw_mul (vb_tt alg Dexp P Cs ncar capT ha hd hnc) (vb_M alg Dexp P Cs ncar capT ha hd)
  have q1 : 8 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A ≤ (thrN alg P capT) ^ (10 * Dexp + 136) := pw_mono (by omega) hKA (by omega)
  have q2 : Primitive.listJ (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den ≤ (thrN alg P capT) ^ (10 * Dexp + 136) := pw_mono (by omega) (vb_J alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  have q3 : Primitive.listT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M ≤ (thrN alg P capT) ^ (10 * Dexp + 136) := pw_mono (by omega) htM (by omega)
  have q4 : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M ≤ (thrN alg P capT) ^ (10 * Dexp + 136) := pw_mono (by omega) (vb_M alg Dexp P Cs ncar capT ha hd) (by omega)
  have q5 : 1 ≤ (thrN alg P capT) ^ (10 * Dexp + 136) := Nat.one_le_pow _ _ (by omega)
  have hq1 := Nat.mul_le_mul_right ((thrN alg P capT) ^ (10 * Dexp + 136)) hN
  have hq2 := pow_succ' (thrN alg P capT) (10 * Dexp + 136)
  have e2 : 2 * Primitive.listT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M = 2 * (Primitive.listT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M) := by ring
  omega

theorem vb_ell0 : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 ≤ (thrN alg P capT) ^ (5 * Dexp + 72) := by
  have hN := thrN16 alg P capT
  rw [v_ell0]
  refine max_le (pw_mono (by omega) (pw_succ hN (vb_J alg Dexp P Cs ncar capT ha hd hnc) 1 (by omega)) (by omega)) ?_
  have hc : Nat.clog 2 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M ≤ (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  exact hc.trans (pw_mono (by omega) (vb_M alg Dexp P Cs ncar capT ha hd) (by omega))

theorem vb_2ell : 2 ^ ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1) ≤ (thrN alg P capT) ^ (5 * Dexp + 74) := by
  have hN := thrN16 alg P capT
  rw [v_ell0]
  exact pw_mono (by omega) (b2L0 hN (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M (5 * Dexp + 72) (vb_2J alg Dexp P Cs ncar capT ha hd hnc) (vb_M alg Dexp P Cs ncar capT ha hd) (by omega)) (by omega)

theorem vb_pMod : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).pMod ≤ (thrN alg P capT) ^ (5 * Dexp + 74) := by
  rw [v_pMod]; exact bMod (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (5 * Dexp + 74) (vb_2ell alg Dexp P Cs ncar capT ha hd hnc)

/-- **Every THR number of the call is at most `N^{10D+137}`.** -/
theorem vb_get (k : Fin 14) : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get k ≤ (thrN alg P capT) ^ (10 * Dexp + 137) := by
  have hN := thrN16 alg P capT
  have m : ∀ {x e : ℕ}, x ≤ (thrN alg P capT) ^ e → e ≤ 10 * Dexp + 137 → x ≤ (thrN alg P capT) ^ (10 * Dexp + 137) :=
    fun hx he => pw_mono (by omega) hx he
  fin_cases k
  · exact m (vb_nG alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_den alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_cut alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_nPr alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_pSum alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_dig alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_M alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_A alg Dexp P Cs ncar capT ha hd) (by omega)
  · exact m (vb_Bs alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  · exact m (vb_J alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  · exact m (vb_tt alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  · exact m (vb_ee alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  · exact m (vb_ell0 alg Dexp P Cs ncar capT ha hd hnc) (by omega)
  · exact m (vb_pMod alg Dexp P Cs ncar capT ha hd hnc) (by omega)

end NearCubicWires.WireExponent3_5.PrimT.W6
