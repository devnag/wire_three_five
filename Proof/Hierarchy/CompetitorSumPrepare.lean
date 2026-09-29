import Proof.Hierarchy.CompetitorSumFields
import Proof.Hierarchy.CompetitorSumWidth

/-! The actual term-stream producer for one rational-fold addition. The
retained accumulator is preserved while the old workspace is cleared and
the next three signed-rational fields are loaded at the global cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSumFold
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorReusableDecision CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def termTargets : List (Fin 6) := [2,3,5]
def termFields (b : ℕ) (c : CompetitorValidity.Estimate) : Fin 6 → List Bool :=
  ![[],[],binary (width b) c.negative,binary (width b) c.positive,[],binary b c.denominator]
def termWord (b : ℕ) (c : CompetitorValidity.Estimate) := fieldStream (termFields b c) termTargets
noncomputable def termProgram := fieldsProgram termTargets
noncomputable def prepareProgram := Composition.machine (clearProgram workSlot) termProgram


end NearCubicWires.RepairOrdinary.CompetitorSumFold
