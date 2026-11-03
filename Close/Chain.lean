import Close.Sources
import Proof.Assembly.SelectedRecoveryIntegration
import Outer.Apply

set_option autoImplicit false

namespace NearCubicGates.Close

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary

namespace GateSources
variable (s : GateSources)

/-- The fixed-machine refuter at clock `T` (input 7). -/
noncomputable def hierarchy (T : ℕ → ℕ) (clock : OrdinaryClock T) : HierarchyRefuterAlgorithm T :=
  Classical.choice (s.hierarchyRefuter T clock)

/-- lem:succinct-verifier at clock `n^{k+2}` and instance-length exponent `G` (the near-cubic-gates paper app:multitape). -/
noncomputable def sv (k : ℕ) (clock : OrdinaryClock (fun n => n ^ (k + 2))) (G : ℕ) :
    Outer.SuccinctVerifier (s.hierarchy (fun n => n ^ (k + 2)) clock).hierarchy G :=
  Classical.choice (s.succinct k _ G)

end GateSources

end NearCubicGates.Close
