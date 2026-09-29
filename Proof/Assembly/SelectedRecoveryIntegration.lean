import Proof.Amplification.RecoveryRefuterReplayWhole
import Proof.Hierarchy.HierarchyNormalizedRealization

/-! Early integration at the actual fixed-U source, normalized outer PCP and
selected ordinary refuter. The legal weak machine remains an explicit local
input; this theorem does not assert the repaired headline. -/
namespace NearCubicWires.RepairSource.SelectedRecoveryIntegration
open RepairOrdinary ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def fixedProjection (sources : EightSources) := UWhole.projectionSource sources.pcp.projection
def padding (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  max (sources.hierarchy (fun n => n^(k+2)) clock).hierarchy.coefficient (k+3)
def outer (sources : EightSources) (k : ℕ) (clock : OrdinaryClock (fun n => n^(k+2))) :=
  HierarchyNormalized.outer (fixedProjection sources)
    (sources.hierarchy (fun n => n^(k+2)) clock).joint (padding sources k clock)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)

end
end NearCubicWires.RepairSource.SelectedRecoveryIntegration
