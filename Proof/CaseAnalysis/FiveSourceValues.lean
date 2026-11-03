import Proof.CaseAnalysis.FiveSourceCode

section
/- Source body: PCJ38fbfed565f64139_Source.lean; adapted only for the paid mask load. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
namespace RCFive.Source
open PCJc4297ab269d8423a_Source
attribute [local irreducible] P1TopDownPaidPayload.tapes

/- Per-call values for one already fixed SourceCode. -/
structure CallValues (Atom : Type) (sourceTapes : Nat) where
  order :
    List (CircuitMonomial Atom 4)
  L :
    Nat
  target :
    Nat
  dflt :
    P1TopDownPaidReusable.Datum
  ds :
    Nat → List P1TopDownPaidReusable.Datum
  xs :
    Nat → List Nat
  S :
    Nat → Nat
  R :
    Nat → Nat
  B :
    Nat → Nat
  rowWidth :
    Nat → Nat
  total :
    Nat → Nat
  denominator :
    Nat → Nat
  D :
    Nat → Nat
  cap :
    Nat → Nat
  logSize :
    Nat → Nat
  resetSize :
    Nat → Nat
  coefficient :
    Nat → CompetitorValidity.Estimate
  old :
    Nat → List Bool
  phasePrefix :
    List Stream.Entry
  entries :
    List Stream.Entry
  H :
    Nat → Fin sourceTapes → Nat
  A :
    Nat → Fin sourceTapes → List Bool
  reserveSize :
    Nat
  familyCost :
    Nat
  refillCost :
    Nat
  firstCost :
    Nat
  counterReserve :
    Nat



end RCFive.Source
end
