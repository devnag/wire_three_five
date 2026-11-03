import Proof.MachineModel.BlockScrubEntry
import Proof.SourceAssembly.SourceCodeFamily
import Proof.SourceAssembly.SourceRefill

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction
noncomputable section

/-! ## 1. The dirty bound from a run's cost alone -/

/-! ## 2. The clear set and the two docking maps -/

namespace Dims
variable (d : Dims)

/-- Size of the private scratch (every loader tape of the cycle). -/
def pscr : Nat := d.R1 + 408 + d.w + d.tc
/-- Size of the clear set: family bank + private scratch. -/
def tcl : Nat := d.rt + d.pscr

/-- The clear set, by value. -/
def clearV (i : Nat) : Nat := if i < d.rt then d.F + i else d.G + (i - d.rt)

end Dims

/-! ## 3. The prologue clear on the layout -/

/-! ## 4. What the call cost must pay: the typed bound -/

end
end NearCubicWires.SourceConstruction
end
