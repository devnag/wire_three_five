import Proof.CaseAnalysis.RowsModeElementary
import Proof.PCP.PCPSerializerTapeSupport

/-! A paid recorded return prepares the concrete elementary writer bank for
reuse. Its append cursor is excluded from every reset and space charge. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReset
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 45) : Bool:=decide (i≠44)
def caps (C : Nat) (i : Fin 45):=if selected i then C else 0

noncomputable def machine {s : ℕ} (p : Machine 45 s) := MaskedReset.machine p selected
noncomputable def input {s : ℕ} (c : Configuration 45 s) (C : ℕ) :=
  ZeroPadding.config (Rewind.Workspace.capacities 45 C)
    (Rewind.recording (ZeroPadding.config (caps C) c) 0)

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReset
