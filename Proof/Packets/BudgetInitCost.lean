import Proof.SourceAssembly.SourceInitHeader
import Proof.PCP.PCPSerializerCapacityBounds
import Proof.SourceAssembly.AdmissionInput

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SupplierEstimator
open NearCubicWires.RepairSource.ProjectionNormalization
namespace NearCubicWires.SourceBudget
open NearCubicWires.SourceConstruction NearCubicWires.RuntimeShape
noncomputable section

/-! ## 1. Unary scaling is linear; powers are polynomial -/

/-- **`c·(n+1)` in unary costs `(4c+2)·n + 12c + 18`** — linear in `n` (so `Power.budget 1 c V` is table class). -/
theorem power1_eq (c n : ℕ) :
    PCPSerializerCapacity.Power.budget 1 c n = (4*c+2)*n + 12*c + 18 := by
  unfold PCPSerializerCapacity.Power.budget DimensionPower.cost DimensionPower.cost WilliamsUnaryProduct.budget
  simp only [pow_zero, mul_one]
  ring

theorem powerD_le (D c n : ℕ) :
    PCPSerializerCapacity.Power.budget D c n ≤ PCPSerializerCapacity.coefficient D c*(n+1)^(D+1) := by
  have h := PCPSerializerCapacity.budget_bound D c n
  unfold PCPSerializerCapacity.budget at h
  omega

/-! ## 2. The pieces -/

theorem rewind_eq (V : ℕ) : RewindOnce.cost V = 6*V + 18 := by
  unfold RewindOnce.cost; omega

theorem xfer_eq (Rc : ℕ) : InitRun.xferCost Rc = 10*Rc + 26 := by
  unfold InitRun.xferCost; omega

theorem uniform_eq (cS cR V b Rc : ℕ) :
    Uniform.cost cS cR V b Rc = (6*cS+6*cR+6)*V + 14*cS + 14*cR + 2*b + 2*Rc + 80 := by
  unfold Uniform.cost
  rw [power1_eq, power1_eq]
  ring

theorem rowConst_le (L q : ℕ) : RowConst.cost L 2 q ≤ 700*(q+1)^2 + 20*(L*(q+1)^2) := by
  have hlc := Dimension.liveCount_poly q L
  have hK := normalizedLiveCount_le q L
  have h1 := power1_eq 2 (normalizedLiveCount q L)
  have h2 := power1_eq 3 (normalizedLiveCount q L + 2)
  have hq : q + 1 ≤ (q+1)^2 := Nat.le_self_pow (by decide) _
  have e : (400 + 20*L)*(q+1)^2 = 400*(q+1)^2 + 20*(L*(q+1)^2) := by ring
  unfold RowConst.cost
  simp only
  rw [h1, h2]
  omega

theorem slopes_le (L q : ℕ) :
    InitSlopes.cost L q (InitPost.Ms L q) ≤ 6200*(q+1)^2 + 20*(L*(q+1)^2) := by
  have hlc := Dimension.liveCount_poly q L
  have hK := normalizedLiveCount_le q L
  have h1 := power1_eq 200 (normalizedLiveCount q L + 1)
  have hq : q + 1 ≤ (q+1)^2 := Nat.le_self_pow (by decide) _
  have e : (400 + 20*L)*(q+1)^2 = 400*(q+1)^2 + 20*(L*(q+1)^2) := by ring
  unfold InitSlopes.cost InitSlopes.dv InitPost.Ms
  simp only
  rw [h1]
  set K := normalizedLiveCount q L with hKd
  have hdiv : q / (200*(K+1+1)) ≤ q := Nat.div_le_self _ _
  have hprod : q / (200*(K+1+1)) * (2*(2*(K+1))+3) ≤ 7*(q+1)^2 := by
    have := Nat.mul_le_mul hdiv (show 2*(2*(K+1))+3 ≤ 4*q+7 by omega)
    have e2 : 7*(q+1)^2 = 7*(q*q) + 14*q + 7 := by ring
    have e3 : q*(4*q+7) = 4*(q*q) + 7*q := by ring
    omega
  omega

theorem enc_le (b : ℕ) : InitEnc.cost b ≤ (PCPSerializerCapacity.coefficient 2 127 + 3000)*(b+1)^3 := by
  have hP := powerD_le 2 127 b
  have hb1 : b + 1 ≤ (b+1)^3 := Nat.le_self_pow (by decide) _
  have hb2 : (b+1)^2 ≤ (b+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have e : (PCPSerializerCapacity.coefficient 2 127 + 3000)*(b+1)^3 =
      PCPSerializerCapacity.coefficient 2 127*(b+1)^(2+1) + 3000*(b+1)^3 := by ring
  unfold InitEnc.cost InitEnc.rr CloseoutFinalC10AppendWorkspaceInit.budget CloseoutFinalC10AppendWorkspaceInit.capacity
  rw [power1_eq, power1_eq, power1_eq, power1_eq, power1_eq, e]
  omega

theorem costB_le (mode : Bool) (L target q Rc : ℕ) :
    InitRun.Place.costB mode L target q Rc ≤ 2*Rc + 200*(q+1)^2 + 8*L + 8*target + 60 := by
  have ht : (SourceFactorSel.Nat.tagWord mode).length ≤ 11 := by
    unfold SourceFactorSel.Nat.tagWord
    rw [RepairOrdinary.frame_length]
    have hx : (if mode then 0 else 1) ≤ 1 := by split <;> omega
    have := Admission.natWord_le (if mode then 0 else 1)
    omega
  have hL := Admission.natWord_le L
  have hT := Admission.natWord_le target
  have hq := Admission.natWord_le q
  have hbl : natBitLength q ≤ q + 1 := Admission.natBitLength_le_succ q
  have e2 : (q+1)^2 = q*q + 2*q + 1 := by ring
  have e3 : q^2 = q*q := by ring
  unfold InitRun.Place.costB SourceFactorSel.Nat.natCost CloseoutRowsEstimatorParity.Natural.budget
    EquationHeaderAppend.budget
  rw [RepairOrdinary.frame_length, RepairOrdinary.frame_length, e3]
  omega

theorem costA_le (DP CP DW CW DL CL q : ℕ) :
    InitRun.Place.costA DP CP DW CW DL CL q ≤ 2*q + 11 + PCPSerializerCapacity.coefficient DP CP*(q+1)^(DP+1) +
      PCPSerializerCapacity.coefficient DW CW*(q+1)^(DW+1) + PCPSerializerCapacity.coefficient DL CL*(q+1)^(DL+1) := by
  have h1 := powerD_le DP CP q
  have h2 := powerD_le DW CW q
  have h3 := powerD_le DL CL q
  unfold InitRun.Place.costA
  omega

/-! ## 3. The init, in the classes -/

/-- The init's table coefficient: `Once`'s, the `V`-linear stages, and fourteen `Rc`'s. -/
def initT (eR eV L C cVc cS cR : ℕ) : ℕ :=
  (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient eR C + BlockPlatform.UnaryCalc.polyCoefficient eV cVc + 300 +
    10*C + 6 + 10*cVc + 6 + 2 + 4*C + 12) + (6*cS+6*cR+12)*cVc + 14*C

/-- The init's polynomial coefficient. -/
def initP (L target cS cR DP CP DW CW DL CL : ℕ) : ℕ :=
  7200 + 40*L + (PCPSerializerCapacity.coefficient 2 127 + 3000) + PCPSerializerCapacity.coefficient DP CP +
    PCPSerializerCapacity.coefficient DW CW + PCPSerializerCapacity.coefficient DL CL + 14*cS + 14*cR + 8*L + 8*target + 500

theorem initS_le {d : Dims} {eX pX gW eR eV X T : ℕ} (pl : InitRun.Place d eX pX gW eR eV X T)
    (h2 : 2 ≤ eR) (hVR : eV + 1 ≤ eR) (L C cVc cS cR DP CP DW CW DL CL : ℕ) (mode : Bool) (target q b : ℕ) :
    pl.init2Cost L C cVc cS cR q b + 1 + InitRun.Place.headCost DP CP DW CW DL CL mode L target q (Once.Rc eR L C q) ≤
      initT eR eV L C cVc cS cR * tableClass L (eR+1) q +
        initP L target cS cR DP CP DW CW DL CL * (q + b + 1)^(DP+DW+DL+3) := by
  have hZ1 : 1 ≤ q + b + 1 := by omega
  have pw : ∀ k, k ≤ DP+DW+DL+3 → (q+b+1)^k ≤ (q + b + 1)^(DP+DW+DL+3) := fun k hk => Nat.pow_le_pow_right hZ1 hk
  have hY1 : 1 ≤ (q + b + 1)^(DP+DW+DL+3) := Nat.one_le_pow _ _ hZ1
  have hq2 : (q+1)^2 ≤ (q + b + 1)^(DP+DW+DL+3) := (Nat.pow_le_pow_left (by omega) 2).trans (pw 2 (by omega))
  have hb3 : (b+1)^3 ≤ (q + b + 1)^(DP+DW+DL+3) := (Nat.pow_le_pow_left (by omega) 3).trans (pw 3 (by omega))
  have hqP : (q+1)^(DP+1) ≤ (q + b + 1)^(DP+DW+DL+3) := (Nat.pow_le_pow_left (by omega) _).trans (pw _ (by omega))
  have hqW : (q+1)^(DW+1) ≤ (q + b + 1)^(DP+DW+DL+3) := (Nat.pow_le_pow_left (by omega) _).trans (pw _ (by omega))
  have hqL : (q+1)^(DL+1) ≤ (q + b + 1)^(DP+DW+DL+3) := (Nat.pow_le_pow_left (by omega) _).trans (pw _ (by omega))
  have hqY : q + 1 ≤ (q + b + 1)^(DP+DW+DL+3) := (show q + 1 ≤ (q+b+1)^1 by rw [pow_one]; omega).trans (pw 1 (by omega))
  have hbY : b + 1 ≤ (q + b + 1)^(DP+DW+DL+3) := (show b + 1 ≤ (q+b+1)^1 by rw [pow_one]; omega).trans (pw 1 (by omega))
  -- table atoms
  have hV : cVc * tableClass L eV q ≤ cVc * tableClass L (eR+1) q := Nat.mul_le_mul_left _ (tableClass_mono (by omega))
  have hRc : Once.Rc eR L C q ≤ C * tableClass L (eR+1) q := Nat.mul_le_mul_left _ (tableClass_mono (by omega))
  have honce := Once.onceCost_class eR eV L C cVc q h2 hVR
  have hrow := rowConst_le L q
  have hsl := slopes_le L q
  have henc := enc_le b
  have hA := costA_le DP CP DW CW DL CL q
  have hB := costB_le mode L target q (Once.Rc eR L C q)
  have hLq : L*(q+1)^2 ≤ L*(q + b + 1)^(DP+DW+DL+3) := Nat.mul_le_mul_left _ hq2
  have hVV : (6*cS+6*cR+6)*(cVc * tableClass L eV q) ≤ (6*cS+6*cR+6)*(cVc*tableClass L (eR+1) q) := Nat.mul_le_mul_left _ hV
  have eT : initT eR eV L C cVc cS cR * tableClass L (eR+1) q =
      (450 + 20*L + BlockPlatform.UnaryCalc.polyCoefficient eR C + BlockPlatform.UnaryCalc.polyCoefficient eV cVc + 300 +
        10*C + 6 + 10*cVc + 6 + 2 + 4*C + 12) * tableClass L (eR+1) q + (6*cS+6*cR+6)*(cVc*tableClass L (eR+1) q) + 6*(cVc*tableClass L (eR+1) q) + 14*(C*tableClass L (eR+1) q) := by
    unfold initT; ring
  have eP : initP L target cS cR DP CP DW CW DL CL * (q + b + 1)^(DP+DW+DL+3) =
      7200*(q + b + 1)^(DP+DW+DL+3) + 40*(L*(q + b + 1)^(DP+DW+DL+3)) + (PCPSerializerCapacity.coefficient 2 127 + 3000)*(q + b + 1)^(DP+DW+DL+3) + PCPSerializerCapacity.coefficient DP CP*(q + b + 1)^(DP+DW+DL+3) +
        PCPSerializerCapacity.coefficient DW CW*(q + b + 1)^(DP+DW+DL+3) + PCPSerializerCapacity.coefficient DL CL*(q + b + 1)^(DP+DW+DL+3) + 14*(cS*(q + b + 1)^(DP+DW+DL+3)) + 14*(cR*(q + b + 1)^(DP+DW+DL+3)) +
        8*(L*(q + b + 1)^(DP+DW+DL+3)) + 8*(target*(q + b + 1)^(DP+DW+DL+3)) + 500*(q + b + 1)^(DP+DW+DL+3) := by
    unfold initP; ring
  have hE : (PCPSerializerCapacity.coefficient 2 127 + 3000)*(b+1)^3 ≤ (PCPSerializerCapacity.coefficient 2 127 + 3000)*(q + b + 1)^(DP+DW+DL+3) :=
    Nat.mul_le_mul_left _ hb3
  have hcP : PCPSerializerCapacity.coefficient DP CP*(q+1)^(DP+1) ≤ PCPSerializerCapacity.coefficient DP CP*(q + b + 1)^(DP+DW+DL+3) :=
    Nat.mul_le_mul_left _ hqP
  have hcW : PCPSerializerCapacity.coefficient DW CW*(q+1)^(DW+1) ≤ PCPSerializerCapacity.coefficient DW CW*(q + b + 1)^(DP+DW+DL+3) :=
    Nat.mul_le_mul_left _ hqW
  have hcL : PCPSerializerCapacity.coefficient DL CL*(q+1)^(DL+1) ≤ PCPSerializerCapacity.coefficient DL CL*(q + b + 1)^(DP+DW+DL+3) :=
    Nat.mul_le_mul_left _ hqL
  have hcS : cS ≤ cS*(q + b + 1)^(DP+DW+DL+3) := Nat.le_mul_of_pos_right _ hY1
  have hcR : cR ≤ cR*(q + b + 1)^(DP+DW+DL+3) := Nat.le_mul_of_pos_right _ hY1
  have hLY : L ≤ L*(q + b + 1)^(DP+DW+DL+3) := Nat.le_mul_of_pos_right _ hY1
  have htY : target ≤ target*(q + b + 1)^(DP+DW+DL+3) := Nat.le_mul_of_pos_right _ hY1
  have hVT : cVc * tableClass L (eR+1) q ≥ cVc * tableClass L eV q := hV
  unfold InitRun.Place.init2Cost InitRun.Place.initCost InitPost.cost InitRun.Place.headCost
  rw [rewind_eq, uniform_eq, xfer_eq, eT, eP]
  omega

end
end NearCubicWires.SourceBudget
end

