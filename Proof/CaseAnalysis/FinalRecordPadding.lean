import Proof.CaseAnalysis.FinalPartsSchedule
import Proof.CaseAnalysis.FinalStageSeamBridge
import Proof.CaseAnalysis.FinalCallCountCap
import Proof.CaseAnalysis.FinalEnvelopeCounter

namespace NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (worker)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock (DockReady joinScalarWidth flag
  result inputTape)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape (EmitEntry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1  The words stage's budget is monotone in the call count -/

/-- The address counter's own budget (`Proof/PCP/ProjectionNormalizationCounter.lean`)
is linear. -/
theorem counterBudget_mono {c c' : ℕ} (h : c ≤ c') :
    ProjectionNormalization.Counter.budget c ≤ ProjectionNormalization.Counter.budget c' := by
  unfold ProjectionNormalization.Counter.budget
  omega

theorem wordsFuel_mono (entryWidth : ℕ) {c c' : ℕ} (h : c ≤ c') :
    CloseoutFinalC10WordsStage.wordsFuel entryWidth c
      ≤ CloseoutFinalC10WordsStage.wordsFuel entryWidth c' := by
  have hj : joinScalarWidth entryWidth c ≤ joinScalarWidth entryWidth c' :=
    CloseoutFinalC10CallCountMajorant.joinScalarWidth_mono entryWidth h
  have hdim : CompetitorDimensions.budget (joinScalarWidth entryWidth c)
      ≤ CompetitorDimensions.budget (joinScalarWidth entryWidth c') :=
    CloseoutFinalC10CallCountMajorant.dimensions_budget_mono hj
  have hcap : CompetitorReusableDecision.capacity (joinScalarWidth entryWidth c)
      ≤ CompetitorReusableDecision.capacity (joinScalarWidth entryWidth c') :=
    CloseoutFinalC10CallCountMajorant.capacity_mono hj
  have hwid : CompetitorRationalDecision.width (joinScalarWidth entryWidth c)
      ≤ CompetitorRationalDecision.width (joinScalarWidth entryWidth c') := by
    unfold CompetitorRationalDecision.width
    omega
  have hcnt := counterBudget_mono h
  have hmulA : (CompetitorRationalDecision.width entryWidth + 1) * (2 * c + 3)
      ≤ (CompetitorRationalDecision.width entryWidth + 1) * (2 * c' + 3) :=
    Nat.mul_le_mul_left _ (by omega)
  have hmulB : (CompetitorRationalDecision.width entryWidth + 1) * c
      ≤ (CompetitorRationalDecision.width entryWidth + 1) * c' :=
    Nat.mul_le_mul_left _ h
  unfold CloseoutFinalC10WordsStage.wordsFuel
  omega

/-- **The stage's budget is monotone in the `Parts.callCount` field.**  This is
the whole content of the separation: `callCount` reaches `stageFuel`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`) only inside `wordsFuel`. -/
theorem stageFuel_mono (callFuel : Phase → ℕ → ℕ) (entryWidth callCount callCount' : ℕ → ℕ)
    (ph : Phase) (n : ℕ) (h : callCount n ≤ callCount' n) :
    C10SupplierStage.stageFuel callFuel entryWidth callCount ph n
      ≤ C10SupplierStage.stageFuel callFuel entryWidth callCount' ph n := by
  have hw := wordsFuel_mono (entryWidth n) h
  unfold C10SupplierStage.stageFuel
  omega

/-! ## Section 2  The stage, run at a length-only fuel over the UNPADDED stream -/

/-! ## Section 3  The seam, with the equality replaced by the paper's bound -/

/-! ## Section 4  The producer side: the loop writes its own count, with no hypothesis -/

/-! ## Section 5  The cap, and where it lands on the width schedule -/

/-! ## Section 6  The payoff: `StageReady` at the schedule, with no record-count
hypothesis -/


end NearCubicWires.RepairSource.CloseoutFinal.C10RecordPadding
