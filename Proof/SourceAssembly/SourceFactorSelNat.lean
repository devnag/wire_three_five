import Proof.SourceAssembly.SourceFactorSelDesc
import Proof.SourceAssembly.SourceFactorSelHeader
import Proof.CaseAnalysis.RowsEstimatorParityNatural
import Proof.Hierarchy.HierarchyFixedWord
import Proof.SourceAssembly.SLoadMaskFrame

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Nat
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation
noncomputable section

open CloseoutRowsEstimatorParity

def natM := Composition.machine (Desc.copyM (22 : Fin 25) 0 23 24) (TapeEmbedding.machine 3 Natural.machine)

def natCost (n D : Nat) : Nat := 2 * D + 4 + 1 + Natural.budget n

/-! ## The mode tag -/

/-- The header's first field (`1` THR, `0` SYM), framed. -/
def tagWord (mode : Bool) : List Bool := frame (natWord (if mode then 0 else 1))


end
end NearCubicWires.SourceFactorSel.Nat
