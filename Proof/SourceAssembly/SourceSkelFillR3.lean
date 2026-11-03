import Proof.SourceAssembly.SourceSkelSeam3
import Proof.SourceAssembly.SourceSkelFillR

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-- S's `RestExt3` (twelve high residents `hrT 0..11`) holds at `resOfX D xR` whenever `2 ≤ xR`. -/
theorem restExt3X (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
    (D : RestData (decompositionOf sources)) (xR : Nat) (hxR : 2 ≤ xR) {gamma : Real} (p : Parameters sources gamma)
    (k r : Nat) :
    (SourceConstruction.dimsOf mask packets rows sources (resOfX D xR) p k r).RestExt3 D.se.extra D.sp.extra D.gW :=
  ⟨restExt2X mask packets rows sources D xR p k r,
    by show 19 + SourceConstruction.restPc D.se.extra D.sp.extra D.gW + 22 ≤ resOfX D xR; unfold resOfX; omega⟩

def refillFam3 (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (gW xR : SourceBudget.ParNat)
    (hxR : ∀ sources gamma hg hh p, 2 ≤ xR sources gamma hg hh p) (f : SourceConstruction.FreeChoices)
    (g7 : RefillFamR mask packets rows (resR gW xR) f) : RefillFamR mask packets rows (resR gW xR) f :=
  fun sources gamma hg hh p mode ph =>
    refill3 mask packets rows sources (resR gW xR sources gamma hg hh p) p
      (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p) (f.r sources gamma hg hh p)
      (restDataOf gW sources gamma hg hh p).se (restDataOf gW sources gamma hg hh p).sp
      (restExt3X mask packets rows sources (restDataOf gW sources gamma hg hh p) (xR sources gamma hg hh p)
        (hxR sources gamma hg hh p) p _ _)
      (g7 sources gamma hg hh p mode ph).2

end
end NearCubicWires.SourceSkeleton
end
