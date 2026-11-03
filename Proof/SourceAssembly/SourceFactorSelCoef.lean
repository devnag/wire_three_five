import Proof.SourceAssembly.SourceFactorSelCoefReduce
import Proof.SourceAssembly.SourceFactorSelCoefValue

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Coef
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding RepairOrdinary.RadixSemantics RepairOrdinary.SignedSortKey
open NearCubicWires.SourceFactorSel.CoefPrim NearCubicWires.SourceFactorSel.CoefAcc NearCubicWires.SourceFactorSel.CoefBin
open NearCubicWires.SourceFactorSel.CoefReduce NearCubicWires.SourceFactorSel.CoefValue
noncomputable section

/-! ## Generic docking with a kept set -/

/-! ## One slot, docked -/

/-! ## The per-slot values passed to the accumulator -/

def nS (f : Bool) (t : ℚ) : ℕ := if f then t.num.natAbs else 0
def dS (f : Bool) (t : ℚ) : ℕ := if f then t.den else 0
def sS (f : Bool) (t : ℚ) : Bool := if f then decide (t.num < 0) else false


/-! ## The machine -/





/-! ## The run -/

end
end NearCubicWires.SourceFactorSel.Coef

