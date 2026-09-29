import Proof.CaseAnalysis.RecoverySelectorState

/-! Exact output bytes and fixed restoration ports of the repeated original
selector. These describe the checked body; they add no machine operations. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nextOut {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value ref : ℕ) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :=
  out++((compileExpr b (unaryEqualsExpr row start limit value hblock)).extension.suffix).flatMap
    PCPPRequestNodeSchema.native++PCPPNativeClauseBank.nodeBits 3 0 3 0 1
      (RecoveryBoundedNativeFold.values ref (RecoveryBoundedSelectorJoin.counter b row start limit value hblock))

theorem condition_output {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (hblock : start+limit ≤ rowWidth n bound) :
    (compileExpr b (unaryEqualsExpr row start limit value hblock)).output.val=
      RecoveryBoundedSelectorJoin.counter b row start limit value hblock := by
  rw [compileExpr_output,unary_expression,all_nodeCount]
  have hl : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
  rw [hl]
  unfold RecoveryBoundedSelectorJoin.counter
  omega

theorem nextOut_eq {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (wire : LiveWire b) (out : List Bool)
    (hblock : start+limit ≤ rowWidth n bound) :
    nextOut b row start limit value wire.output.val out hblock=
      out++(head b (unaryEqualsExpr row start limit value hblock) wire).extension.suffix.flatMap
        PCPPRequestNodeSchema.native := by
  rw [head_suffix,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    condition_output]
  simp [nextOut,PCPPNativeClauseBank.nodeBits,RecoveryBoundedNativeFold.values,
    PCPPRequestNodeSchema.native,PCPPRequestNodeSchema.fields,List.append_assoc]

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
