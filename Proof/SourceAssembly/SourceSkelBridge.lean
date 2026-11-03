import Proof.SourceAssembly.SourceSkelSeam3

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
namespace NearCubicWires.SourceSkeleton
noncomputable section

section bridge
variable (sources : EightSources) (selector : CyclicChoice.Laws) (compiler : Packets.CompilerLaws)
  {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
  (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
    ComponentwisePolynomial.CircuitPolynomial (C10TotalDecode.Atom pcpp) 1)
  (ph : CloseoutRowsOriginalSchedule.Phase) (ci : Fin (2 ^ pcpp.clauseBits)) (L target : Nat)

/-- The admission's layout family, in the seam's request form. -/
def layoutAtOf : (mode : Bool) → SourceConstruction.TraceData.LayoutFamily coordinate ph ci sources L target mode selector →
    ∀ m : Nat, Packets.Layout (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m))
  | true, lay => lay
  | false, lay => lay

include compiler in
/-- The compiler's facts, in the seam's request form. -/
theorem factsAtOf : ∀ (mode : Bool) (m : Nat), ∀ row ∈ ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources)).rows,
    Packets.PacketFacts (decompositionOf sources) ((requestAt coordinate ph ci L target mode m).family (decompositionOf sources))
      (geometryOf selector (decompositionOf sources) (requestAt coordinate ph ci L target mode m)) row
  | true, m, row, hrow => compiler sources L target true (SourceRequest.FactorLoop.factorsAt coordinate ph ci m) _ row hrow
  | false, m, row, hrow => compiler sources L target false (SourceRequest.FactorLoop.factorsAt coordinate ph ci m) _ row hrow

end bridge

end
end NearCubicWires.SourceSkeleton
end
