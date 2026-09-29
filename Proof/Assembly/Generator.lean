import Proof.Assembly.NativeBase
import Proof.Assembly.NativeValues
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves


open PCJ1fef9807c6954e94_Native
namespace PCJf990607ff5714139_Generator

/-! Unchecked interface draft for the COMPLETE native-family input producer.
Not a supplied proof or local plan. The eventual enclosing application must
consume Correct at _hnative and _htail before any implementation begins. -/

structure Policy where
  width : Bool → Nat → Nat → Nat → Nat
  degree : Bool → Nat → Nat → Nat → Nat
  cacheCoefficient : Nat
  cacheDegree : Nat
  inputCoefficient : Nat
  inputDegree : Nat
  sourceCoefficient : Nat
  sourceDegree : Nat
  syntaxCoefficient : Nat
  syntaxDegree : Nat
  tableCoefficient : Nat
  tableDegree : Nat

structure Input where
  native : List Bool
  support : List Bool
  count : List Bool
  q : Nat
  L : Nat
  target : Nat
  recordWidth : Nat
  mode : Bool
  active : Bool


@[irreducible] noncomputable def tapes (printer : WilliamsAlgorithm) (scratch : Nat) : Nat :=
 r_tapes printer+(10+scratch)

structure Result (t : Nat) where
 ds : List P1TopDownPaidReusable.Datum
 S : Nat
 R : Nat
 B : Nat
 rowWidth : Nat
 total : Nat
 denominator : Nat
 residual : Nat
 fuel : Nat
 H : Fin t → Nat
 A : Fin t → List Bool

end PCJf990607ff5714139_Generator
