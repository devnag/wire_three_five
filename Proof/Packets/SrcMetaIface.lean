import Proof.Packets.SrcCapsPow2

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceStart.Meta
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission NearCubicWires.SourceConstruction
noncomputable section

/-- The `C`-mantissa `cc0·(q+1)^ce0` (`COf q = mC q · 2^(q/4)`). -/
def mC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) : ℕ :=
  cc0 selector (decompositionOf s) p.clauseDegree (tgt s p)*(q+1)^ce0 selector (decompositionOf s) p.clauseDegree (tgt s p)

theorem COf_eq (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (q : ℕ) :
    COf selector s p q = mC selector s p q * 2^(q/4) := by
  unfold COf mC RuntimeShape.smallClass
  ring

end
end NearCubicWires.SourceStart.Meta

