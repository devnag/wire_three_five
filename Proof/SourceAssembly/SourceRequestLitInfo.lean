import Proof.SourceAssembly.SourceRequestCurClause
import Proof.SourceAssembly.SourcePairSupport
import Proof.MachineModel.ClosureLocalSupport

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.LitInfo
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value result slots words outPort refPort flagPort)
noncomputable section

def litM := Composition.machine PCJ6e421fabe2aa4155_SourceLiteralRefs.bump
  (Composition.machine CloseoutRowsOriginalSource.machine
    (Composition.machine (PCJ6e421fabe2aa4155_SourceLiteralSupport.machine false)
      (Composition.machine (PCJ6e421fabe2aa4155_SourceLiteralSupport.machine true)
        PCJ6e421fabe2aa4155_SourcePairSupport.finish)))

def litCost (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) (C : Nat) : Nat :=
  1 + 1 + (PCJ6e421fabe2aa4155_SourceLiteralRefs.sourceCost a r ci C + 1 +
    (PCPPQueryCachedBounds.callBudget a (r.circuit.size + r.arity) + 6 + 1 +
      (PCPPQueryCachedBounds.callBudget a (r.circuit.size + r.arity) + 6 + 1 + 1)))

/-! ## Docked and padded: the refill cache read in place, every other bank port on the caller's scratch -/

/-- Bank ports read from the caller's refill cache in place (their words and heads are returned). -/
def cacheSide (b : Fin 91) : Prop := b.val < 19 ∧ b.val ≠ 3 ∧ b.val ≠ 4 ∧ b.val ≠ 15

instance (b : Fin 91) : Decidable (cacheSide b) := by unfold cacheSide; infer_instance

end
end NearCubicWires.SourceRequest.LitInfo

