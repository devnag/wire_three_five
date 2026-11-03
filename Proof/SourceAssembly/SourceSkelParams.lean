import Proof.SourceAssembly.SourceSkelInitK
import Proof.SourceAssembly.SourceSkelFillB
import Proof.SourceAssembly.SourceSkelGen
import Proof.SourceAssembly.SourceSkelLayout
import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceSkelInitC
import Proof.Packets.BudgetSiteAssembly
import Proof.Packets.BudgetSeamScalars
import Proof.SourceAssembly.SourceStepsSat
import Proof.SourceAssembly.AdmissionSmall

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.Params
noncomputable section

structure ParamIn (selector : CyclicChoice.Laws) where
  cVc : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat
  hV : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat
  y : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ClsFam
  yF0 : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ClsFam
  I : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ClsFam
  target : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat
  smallDeg : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat
  gwW : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat

variable {selector : CyclicChoice.Laws} (P : ParamIn selector) (mask : MaskProducer)
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (rows : PCJc4297ab269d8423a_Source.RowLibrary selector)

/-! ## 2. `gW`, `xR` -/

def gG7 : SourceBudget.ParNat := fun s _ _ _ _ =>
  7000 + 19 + 4 * max (3864 + 2 * PCJ6e421fabe2aa4155_SourceTopNative.tapes (decompositionOf s)) 3778

def gWP : (mask : MaskProducer) → PCJc4297ab269d8423a_Source.PacketLibrary selector →
    PCJc4297ab269d8423a_Source.RowLibrary selector → SourceBudget.ParNat :=
  fun mask packets rows s g hg hh p => gG7 s g hg hh p + P.gwW mask packets rows s g hg hh p

/-! ## 3. `den0` -/

/-- **The init's windows** at the site's reserve `Rc = 1·tableClass L eR q` (the premises of `InitS.entry_init` other than `hv`,
which is SS's `enc_sat`), plus `Mb ≤ Rc`. -/
def InitWin (eR eV L cVc cS cR CL DL target q : ℕ) : Prop :=
  q + 3 + Dimension.prefixCost eR eV L 1 cVc q ≤ Once.Rc eR L 1 q ∧
  cVc * RuntimeShape.tableClass L eV q ≤ Once.Rc eR L 1 q ∧ VLog eV L cVc q ≤ Once.Rc eR L 1 q ∧ 2 ≤ Once.Rc eR L 1 q ∧
  U0 L q ≤ Once.Rc eR L 1 q ∧
  cS * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L 1 q ∧
  cR * (cVc * RuntimeShape.tableClass L eV q + 1) + 2 ≤ Once.Rc eR L 1 q ∧
  cVc * RuntimeShape.tableClass L eV q + 1 + 2 ≤ Once.Rc eR L 1 q ∧
  CloseoutRowsEstimatorParity.Capacity.value q ≤ Once.Rc eR L 1 q ∧ q ≤ Once.Rc eR L 1 q ∧
  (RepairOrdinary.frame (natWord L)).length ≤ Once.Rc eR L 1 q + 2 ∧ (RepairOrdinary.frame (natWord target)).length ≤ Once.Rc eR L 1 q + 2 ∧
  5 ≤ Once.Rc eR L 1 q ∧ CL * (q+1)^DL + 2 ≤ Once.Rc eR L 1 q ∧ 82472 ≤ Once.Rc eR L 1 q ∧
  2 * q + 1 ≤ Once.Rc eR L 1 q ∧ 2 * InitPost.Ms L q + 5 ≤ Once.Rc eR L 1 q ∧ Mb L q ≤ Once.Rc eR L 1 q

/-! ## 5. `extra` -/

/-! ## 6. The grouped source hole at the closed parameters -/

end
end NearCubicWires.SourceSkeleton.Params
end

