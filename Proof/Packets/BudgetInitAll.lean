import Proof.SourceAssembly.SourceSkelInitAll
import Proof.Packets.BudgetInitCost

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SupplierEstimator
open NearCubicWires.RepairSource.ProjectionNormalization
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceConstruction NearCubicWires.RuntimeShape NearCubicWires.SourceSkeleton
noncomputable section

/-- Horner's partial values only grow (`1 ≤ p`). -/
theorem hVal_ge (p : ℕ) (hp : 1 ≤ p) : ∀ (cs : List ℕ) (v : ℕ), v ≤ InitS.hVal p cs v
  | [], v => le_rfl
  | a :: cs, v => by
    have h := hVal_ge p hp cs (v*p + a)
    have hv : v ≤ v*p + a := le_trans (Nat.le_mul_of_pos_right _ hp) (Nat.le_add_right _ _)
    exact hv.trans h

theorem hCost_le (p : ℕ) (hp : 1 ≤ p) : ∀ (cs : List ℕ) (v : ℕ),
    InitS.hCost p cs v ≤ cs.length * (6*(InitS.hVal p cs v*(p+1)) + 4*cs.sum + 17)
  | [], v => by simp [InitS.hCost]
  | a :: cs, v => by
    have ih := hCost_le p hp cs (v*p + a)
    have hH : InitS.hVal p (a :: cs) v = InitS.hVal p cs (v*p + a) := rfl
    have hge := hVal_ge p hp cs (v*p + a)
    set H := InitS.hVal p cs (v*p + a) with hHd
    have hvH : v ≤ H := le_trans (le_trans (Nat.le_mul_of_pos_right _ hp) (Nat.le_add_right _ _)) hge
    have haH : a ≤ H := le_trans (Nat.le_add_left _ _) hge
    have hvp : v*p ≤ H := le_trans (Nat.le_add_right _ _) hge
    have hstep : InitS.hStepCost p v a ≤ 6*(H*(p+1)) + 4*a + 16 := by
      unfold InitS.hStepCost
      simp only [List.length_replicate]
      have e1 : v*(2*p+3) = 2*(v*p) + 3*v := by ring
      have e2 : H*(p+1) = H*p + H := by ring
      have h1 : v*p ≤ H*p := Nat.mul_le_mul_right _ hvH
      omega
    have hmono : cs.length * (6*(H*(p+1)) + 4*cs.sum + 17) ≤ cs.length * (6*(H*(p+1)) + 4*(a + cs.sum) + 17) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [InitS.hCost, hH, List.length_cons, List.sum_cons]
    have e3 : (cs.length + 1) * (6*(H*(p+1)) + 4*(a + cs.sum) + 17) =
        cs.length * (6*(H*(p+1)) + 4*(a + cs.sum) + 17) + (6*(H*(p+1)) + 4*(a + cs.sum) + 17) := by ring
    rw [e3]
    omega

/-- **The `1^cwid` stage** (`hrT 8`): its cost is polynomial in `Ld ≥ 1` and the code width. -/
theorem cwCost_le (mode : Bool) (Ld : ℕ) (hL : 1 ≤ Ld) :
    InitS.cwCost mode Ld ≤ (InitS.cwCs mode).length * (6*(InitS.cwidOf mode Ld*(Ld+1)) + 4*(InitS.cwCs mode).sum + 17) +
      2*Ld + 2*InitS.cwidOf mode Ld + 8220 := by
  have h := hCost_le Ld hL (InitS.cwCs mode) 4096
  rw [InitS.cwid_eq] at h
  unfold InitS.cwCost
  simp only [List.length_replicate]
  omega

/-! ## 2. The whole init -/

theorem initAll_le {d : Dims} {eX pX gW eR eV X T : ℕ} (pl : InitRun.Place d eX pX gW eR eV X T)
    (h2 : 2 ≤ eR) (hVR : eV + 1 ≤ eR) (L C cVc cS cR DP CP DW CW DL CL : ℕ) (mode : Bool)
    (target q b DD CD Dcw Ccw : ℕ) :
    InitS.initAllCost pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw ≤
      (initT eR eV L C cVc cS cR + 98*C) * tableClass L (eR+1) q +
        initP L target cS cR DP CP DW CW DL CL * (q + b + 1)^(DP+DW+DL+3) +
        PCPSerializerCapacity.coefficient DD CD*(q+1)^(DD+1) + PCPSerializerCapacity.coefficient Dcw Ccw*(q+1)^(Dcw+1) +
        InitS.cwCost mode (CL*(q+1)^DL) + 26*q + 400 := by
  have hS := initS_le pl h2 hVR L C cVc cS cR DP CP DW CW DL CL mode target q b
  have hD := powerD_le DD CD q
  have hW := powerD_le Dcw Ccw q
  have hRc : Once.Rc eR L C q ≤ C * tableClass L (eR+1) q := Nat.mul_le_mul_left _ (tableClass_mono (by omega))
  have hK := normalizedLiveCount_le q L
  have e : (initT eR eV L C cVc cS cR + 98*C) * tableClass L (eR+1) q =
      initT eR eV L C cVc cS cR * tableClass L (eR+1) q + 98*(C * tableClass L (eR+1) q) := by ring
  unfold InitS.initAllCost InitS.initRCost InitS.initSCost InitS.rkCost InitS.Rk SourceRequest.CurComp.subCost InitPost.Ms
  rw [power1_eq, e]
  simp only [List.length_replicate]
  omega

end
end NearCubicWires.SourceBudget
end

