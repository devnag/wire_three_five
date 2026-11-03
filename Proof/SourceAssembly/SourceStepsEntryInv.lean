import Proof.SourceAssembly.SourceSkelProt
import Proof.SourceAssembly.SourceSkelInitAll
import Proof.SourceAssembly.SourceSkelInitC
import Proof.SourceAssembly.SourcePhaseLater

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 400000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction NearCubicWires.SourceSkeleton
namespace NearCubicWires.SourceSteps
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

/-! ## 1. The query install at a clause index -/

section query
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (k n : Nat) (x : BitInput n) (bits : List Bool)

/-- **Clause `ci`'s query word** (`natListWord [left, right]` of its two literals), empty past the last clause. -/
def qwordAt (ci : Nat) : List Bool :=
  if h : ci < NC sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) then
    natListWord [literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ⟨ci, h⟩).left,
      literalIndex (((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))).clauses ⟨ci, h⟩).right]
  else []

/-- **The query cache at clause `ci`**: `clauseData … ci capC (qwordAt ci)`. -/
def cdAt (ci : Nat) : Fin 19 → List Bool :=
  PCPPQueryIndexPadding.clauseData (pcppOutput (req sources k (PolynomialClock.ordinaryClock k) x
      (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
      ((CloseoutLanguage.selectedPCPP sources).output (req sources k (PolynomialClock.ordinaryClock k) x
        (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))))
    (req sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)).arity ci
    (capC sources k (PolynomialClock.ordinaryClock k) x (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits))
    (qwordAt sources p k n x bits ci)

end query

section queried
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma) (den : Nat) (hden : 0 < den) (k r scratch n : Nat)
  (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- **The site's queried bank at clause `ci`**: the cache holds `cdAt ci`. -/
def queriedAt (ci : Nat) (A : Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool) :
    Fin (ControllerSelectedContinuation.bodyTapes sources p k r scratch) → List Bool :=
  install (PCJda54a286946142d3_BranchPhases.cache sources p k r scratch (PCJ374c44bb8b7f47d9_.S.mode sources p den hden k r scratch n x bits hp))
    A (cdAt sources p k n x bits ci)

end queried

/-! ## 2. `FirstEntry3`, the site data, and `entryInvAt` -/

section inv
open NearCubicWires.SourceConstruction.InitRun

/-- **The site data of the clause-entry invariant** (R-SA31's parameters, `Ce` after `Rk`): the source layout `d`, the site universe `T` with
its embedding `whole` into the body, the per-phase placement (`wd = Wd ph 218`), the rest layout, the kept set with its per-`(phase, clause)`
values, the counter, the query tapes and the init's constants. -/
structure EntrySite (BT : Nat) where
  d : SourceConstruction.Dims
  eX : Nat
  pX : Nat
  gW : Nat
  eR : Nat
  eV : Nat
  X : Nat
  T : Nat
  whole : Fin T → Fin BT
  pl : Phase → Place d eX pX gW eR eV X T
  e : d.RestExt3 eX pX gW
  Rc : Nat
  Rk : Nat
  Ce : Nat
  Kc : Fin T → Prop
  K0 : Phase → Nat → Fin T → List Bool
  KH0 : Fin T → Nat
  cnt : Fin T
  c15 : Fin T
  q284 : Fin T
  c17 : Fin T
  c18 : Fin T
  b : Nat
  q : Nat
  Mb : Nat
  Ms : Nat
  S : Nat
  Rw : Nat
  B : Nat
  U0 : Nat

end inv

/-! ## 3. The cross-phase bridge on `entryInvAt` -/

section bridge

end bridge

end
end NearCubicWires.SourceSteps
end
