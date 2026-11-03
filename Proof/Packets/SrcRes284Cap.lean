import Proof.Packets.SrcRes284Ready
import Proof.SourceAssembly.SourceStepsResidue
import Proof.SourceAssembly.AdmissionSource
import Proof.Packets.BudgetTableOnset

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires NearCubicWires.ComponentwisePolynomial LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown
open NearCubicWires.SourceParent
namespace NearCubicWires.SourceStart.Res284
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceSteps
noncomputable section

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (den : Nat) (hden : 0 < den) (k r scratch n : Nat) (x : BitInput n) (bits : List Bool)
  (hp : P1Independent.CappedLegalAdmission.passed sources p
    (ControllerCappedSelected.reference den hden k (PolynomialClock.ordinaryClock k))
    (WorkspaceSelectedAdmission.coldCutoff sources) n x bits = true)

/-- **The two windows hold past one onset.** -/
theorem res284_onset (D : ℕ) :
    ∃ n0, ∀ n, n0 ≤ n → CloseoutWitnessPolicy.inputCutoff sources ≤ n ∧ 2 * D + 6 ≤ C10PartsSchedule.widthAt sources k n := by
  obtain ⟨n1, h1⟩ := SourceBudget.widthAt_ge_eventually sources k (2 * D + 6)
  exact ⟨max n1 (CloseoutWitnessPolicy.inputCutoff sources), fun n hn =>
    ⟨le_of_max_le_right hn, h1 n (le_of_max_le_left hn)⟩⟩

end
end NearCubicWires.SourceStart.Res284

