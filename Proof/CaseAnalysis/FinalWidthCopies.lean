import Proof.CaseAnalysis.FinalBodyWidths
import Proof.CaseAnalysis.FinalWordEngines

/-! Paper C.10's fixed decision tail reads the three records at their own widths.
The six unary widths retained at block tapes 274/275 are copied into tail tapes
2..7. Tape 8 is the restored blank second input; tapes 9..14 are six fresh logs.
Each copy uses the named `copy_dock` budget 2*r+6; all five joins are paid. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10WidthCopies

open LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10WordEngines
open C10TailCompose C10BodyWidths C10TailSlotsUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (e : ℕ) (he : 58 ≤ e)

def phaseOf (k : Fin 6) : Phase :=
  if k.val < 2 then .penalty else if k.val < 4 then .moment else .clause

def partOf (k : Fin 6) : Fin 2 := ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩


def charge (r : ℕ) : ℕ := 2*(r+0)+6

def budget (W : Fin 6 → ℕ) : ℕ :=
  ((((charge (W 0)+1+charge (W 1))+1+charge (W 2))+1+charge (W 3))+1+charge (W 4))+1+charge (W 5)

end
end NearCubicWires.RepairSource.CloseoutFinal.C10WidthCopies
