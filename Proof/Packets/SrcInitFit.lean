import Proof.Packets.SrcMetaStepGF
import Proof.Packets.SrcMetaCost
import Proof.SourceAssembly.SourceSkelInitE2
import Proof.Packets.BudgetInitAll

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceStart.InitFit
open NearCubicWires.SourceBudget NearCubicWires.RuntimeShape NearCubicWires.PolynomialSchedule
open NearCubicWires.SourceSkeleton
noncomputable section

/-! ## 1. The erase's cost -/

theorem initAllCostE_eq {d : Dims} {eX pX gW eR eV X T : ℕ} (pl : Place d eX pX gW eR eV X T)
    (L C cVc cS cR DP CP DW CW DL CL : ℕ) (mode : Bool) (target q b DD CD Dcw Ccw : ℕ) :
    InitS.initAllCostE pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw =
      InitS.initAllCost pl L C cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw +
        (1 + (2*(cVc*tableClass L eV q) + 4)) := by
  unfold InitS.initAllCostE InitS.initAllCost InitS.initRCostE InitS.initRCost InitS.initSCostE InitS.initSCost
    InitE.init2CostE InitRun.Place.init2Cost InitE.initCostE InitRun.Place.initCost
  omega

/-! ## 2. The polynomial collector -/

/-- The code width at the description cap is polynomial in `q`. -/
theorem cwid_poly (mode : Bool) (CL DL : ℕ) : PolynomiallyBounded (fun q => InitS.cwidOf mode (CL*(q+1)^DL)) := by
  cases mode
  · exact polynomiallyBounded_comp thrWidth_poly (MetaCost.pb_cpow CL DL)
  · exact polynomiallyBounded_comp symWidth_poly (MetaCost.pb_cpow CL DL)

def polyPart (L cS cR DP CP DW CW DL CL : ℕ) (mode : Bool) (target DD CD Dcw Ccw : ℕ) (mcost bB : ℕ → ℕ) (q : ℕ) : ℕ :=
  initP L target cS cR DP CP DW CW DL CL * (q + bB q + 1)^(DP+DW+DL+3) +
    PCPSerializerCapacity.coefficient DD CD*(q+1)^(DD+1) + PCPSerializerCapacity.coefficient Dcw Ccw*(q+1)^(Dcw+1) +
    ((InitS.cwCs mode).length * (6*(InitS.cwidOf mode (CL*(q+1)^DL)*(CL*(q+1)^DL+1)) + 4*(InitS.cwCs mode).sum + 17) +
      2*(CL*(q+1)^DL) + 2*InitS.cwidOf mode (CL*(q+1)^DL) + 8220) +
    26*q + 400 + (20*q + 30 + 2*(UnaryTemplate.tape 2).length) + 2*bB q + mcost q + 20

theorem polyPart_poly (L cS cR DP CP DW CW DL CL : ℕ) (mode : Bool) (target DD CD Dcw Ccw : ℕ) (mcost bB : ℕ → ℕ)
    (hm : PolynomiallyBounded mcost) (hb : PolynomiallyBounded bB) :
    PolynomiallyBounded (polyPart L cS cR DP CP DW CW DL CL mode target DD CD Dcw Ccw mcost bB) := by
  have hq1 : PolynomiallyBounded (fun q => q + bB q + 1) :=
    polynomiallyBounded_add (polynomiallyBounded_add polynomiallyBounded_id hb) (polynomiallyBounded_constant 1)
  have hld : PolynomiallyBounded (fun q => CL*(q+1)^DL) := MetaCost.pb_cpow CL DL
  have hcw := cwid_poly mode CL DL
  have hcwB : PolynomiallyBounded (fun q => (InitS.cwCs mode).length * (6*(InitS.cwidOf mode (CL*(q+1)^DL)*(CL*(q+1)^DL+1)) +
      4*(InitS.cwCs mode).sum + 17) + 2*(CL*(q+1)^DL) + 2*InitS.cwidOf mode (CL*(q+1)^DL) + 8220) :=
    polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_mul (polynomiallyBounded_constant _)
        (polynomiallyBounded_add (polynomiallyBounded_add
          (polynomiallyBounded_mul (polynomiallyBounded_constant 6)
            (polynomiallyBounded_mul hcw (polynomiallyBounded_add hld (polynomiallyBounded_constant 1))))
          (polynomiallyBounded_constant _)) (polynomiallyBounded_constant 17)))
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hld))
      (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hcw)) (polynomiallyBounded_constant 8220)
  unfold polyPart
  exact polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
    (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_constant _) (polynomiallyBounded_pow hq1 _))
        (MetaCost.pb_cpow _ _)) (MetaCost.pb_cpow _ _)) hcwB)
      (polynomiallyBounded_mul (polynomiallyBounded_constant 26) polynomiallyBounded_id))
      (polynomiallyBounded_constant 400))
      (polynomiallyBounded_add (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_constant 20) polynomiallyBounded_id) (polynomiallyBounded_constant 30))
        (polynomiallyBounded_constant _)))
    (polynomiallyBounded_mul (polynomiallyBounded_constant 2) hb)) hm) (polynomiallyBounded_constant 20)

/-! ## 3. The fit -/

theorem initX_fit {d : Dims} {eX pX gW eR eV X T : ℕ} (pl : Place d eX pX gW eR eV X T) (h2 : 2 ≤ eR) (hVR : eV + 1 ≤ eR)
    (L cVc cS cR DP CP DW CW DL CL : ℕ) (hCL : 1 ≤ CL) (mode : Bool) (target DD CD Dcw Ccw : ℕ)
    (mcost bB : ℕ → ℕ) (hm : PolynomiallyBounded mcost) (hb : PolynomiallyBounded bB) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ b, b ≤ bB q →
      InitS.initAllXCostE pl L 1 cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw (mcost q) + 2 ≤
        (initT eR eV L 1 cVc cS cR + 98 + 1024*(cVc+1)) * tableClass L (eR+1) q := by
  obtain ⟨q0, h0⟩ := polyBounded_le_Rc _ (polyPart_poly L cS cR DP CP DW CW DL CL mode target DD CD Dcw Ccw mcost bB hm hb) L
  refine ⟨q0, fun q hq b hb' => ?_⟩
  have hA := initAll_le pl h2 hVR L 1 cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw
  have hE := initAllCostE_eq pl L 1 cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw
  have hT : cVc * tableClass L eV q ≤ cVc * tableClass L (eR+1) q :=
    Nat.mul_le_mul_left _ (tableClass_mono (by omega))
  have hP := h0 q hq 1 (eR+1) le_rfl
  have hcw := cwCost_le mode (CL*(q+1)^DL) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity)))
  have hK := normalizedLiveCount_le q L
  have hpow : (q + b + 1)^(DP+DW+DL+3) ≤ (q + bB q + 1)^(DP+DW+DL+3) := Nat.pow_le_pow_left (by omega) _
  have hpm : initP L target cS cR DP CP DW CW DL CL * (q + b + 1)^(DP+DW+DL+3) ≤
      initP L target cS cR DP CP DW CW DL CL * (q + bB q + 1)^(DP+DW+DL+3) := Nat.mul_le_mul_left _ hpow
  have htk : InitS.tkCost (normalizedLiveCount q L) ≤ 20*q + 30 + 2*(UnaryTemplate.tape 2).length := by
    unfold InitS.tkCost; omega
  have hsplit : (initT eR eV L 1 cVc cS cR + 98 + 1024*(cVc+1)) * tableClass L (eR+1) q =
      (initT eR eV L 1 cVc cS cR + 98*1) * tableClass L (eR+1) q + 2*(cVc * tableClass L (eR+1) q) +
        tableClass L (eR+1) q + (1022*cVc + 1023) * tableClass L (eR+1) q := by ring
  unfold polyPart at hP
  unfold InitS.initAllXCostE
  rw [hE, hsplit]
  have hz : 0 ≤ (1022*cVc + 1023) * tableClass L (eR+1) q := Nat.zero_le _
  omega

theorem metaCostG_poly (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) :
    PolynomiallyBounded (MetaStepGF.metaCostG selector s p packets L) :=
  MetaCost.progCost_poly selector s p packets L (SourceFactorSel.MetaPipe.metaVals2 selector s p packets L)
    (MetaStep.czOf selector s p) (MetaStep.vzOf selector s p) (MetaStep.czOf_iff selector s p) (MetaStep.vzOf_iff selector s p)

theorem initX_fitG (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    {d : Dims} {eX pX gW eR eV X T : ℕ} (pl : Place d eX pX gW eR eV X T) (h2 : 2 ≤ eR) (hVR : eV + 1 ≤ eR)
    (L cVc cS cR DP CP DW CW DL CL : ℕ) (hCL : 1 ≤ CL) (mode : Bool) (target DD CD Dcw Ccw : ℕ)
    (bB : ℕ → ℕ) (hb : PolynomiallyBounded bB) :
    ∃ q0, ∀ q, q0 ≤ q → ∀ b, b ≤ bB q →
      InitS.initAllXCostE pl L 1 cVc cS cR DP CP DW CW DL CL mode target q b DD CD Dcw Ccw
          (MetaStepGF.metaCostG selector s p packets L q) + 2 ≤
        (initT eR eV L 1 cVc cS cR + 98 + 1024*(cVc+1)) * tableClass L (eR+1) q :=
  initX_fit pl h2 hVR L cVc cS cR DP CP DW CW DL CL hCL mode target DD CD Dcw Ccw
    (MetaStepGF.metaCostG selector s p packets L) bB (metaCostG_poly selector s p packets L) hb

end
end NearCubicWires.SourceStart.InitFit

