import Proof.SourceAssembly.SourceRequestFieldPass
import Proof.SourceAssembly.SourceRequestSegments

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceFactorSel.Header
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation
noncomputable section

/-- The header's five fields, in order. -/
def fields (mode : Bool) (q L target k : Nat) : Fin 5 → List Bool :=
  ![natWord (if mode then 0 else 1), natWord q, natWord L, natWord target, natWord k]

/-- The docked header machine. -/
def stage {U : Nat} (sl : Fin 11 → Fin U) := RecoveryFocus.machine sl (SourceRequest.FieldPass.machine 5)


end
end NearCubicWires.SourceFactorSel.Header
