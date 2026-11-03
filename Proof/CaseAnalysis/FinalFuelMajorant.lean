import Proof.CaseAnalysis.FinalTailComposeUniform
import Proof.CaseAnalysis.FinalCallCountMajorant

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelMajorant

open ComponentwisePolynomial CanonicalWitnessCodec
open RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairOrdinary.CloseoutFinalC10StageSeam
open RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10CallCountMajorant
open CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem emitFuel_mono {b b' : ℕ} (h : b ≤ b') :
    CloseoutFinalC10WorkerEmitLoader.emitFuel b ≤ CloseoutFinalC10WorkerEmitLoader.emitFuel b' := by
  unfold CloseoutFinalC10WorkerEmitLoader.emitFuel CompetitorRationalDecision.width
  omega

theorem stagedFuel_mono (stageFuel : ℕ → ℕ) (entryWidth n : ℕ) {c c' : ℕ} (h : c ≤ c') :
    stagedFuel stageFuel (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth entryWidth c))
      entryWidth c n ≤
    stagedFuel stageFuel (fun _ => CloseoutFinalC10WorkerEmitLoader.emitFuel (joinScalarWidth entryWidth c'))
      entryWidth c' n := by
  have hd := dockBudget_mono entryWidth h
  have hw := joinScalarWidth_mono entryWidth h
  have he := emitFuel_mono hw
  have ha := append_budget_mono hw
  dsimp only [stagedFuel, dockedFuel]
  omega

theorem bodyThreeFuel_mono {F G : Phase → ℕ} (h : ∀ ph, F ph ≤ G ph) :
    C10TailCompose.bodyThreeFuel F ≤ C10TailCompose.bodyThreeFuel G := by
  have hp := h .penalty
  have hm := h .moment
  have hc := h .clause
  unfold C10TailCompose.bodyThreeFuel
  omega

end NearCubicWires.RepairSource.CloseoutFinal.C10FuelMajorant
