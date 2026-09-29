import Proof.CaseAnalysis.RecoveryGrammarLessShortcut

/-! The literal original grammar has the same forward-child/reverse-fold
schedule already executed by the original address and unary workers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammar
open SourceInterfaces FinitePredicateCircuit BoundedOracleStructuralCircuit
open RecoveryBoundedNative RecoveryBoundedAddress
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem all_count {n : ℕ} (xs : List (BoolExpr n)) :
    (BoolExpr.all xs).nodeCount=prefixSize xs+xs.length+1 := by
  induction xs with
  | nil=>rfl
  | cons e xs ih=>
    simp only [BoolExpr.all,BoolExpr.nodeCount,prefixSize,List.length_cons,ih]
    omega

theorem all_nodes {n : ℕ} (base : ℕ) (xs : List (BoolExpr n)) :
    exprNodes base (BoolExpr.all xs)=prefixNodes base xs++[BooleanNode.const true]++
      foldNodes true (base+prefixSize xs) (references base xs).reverse := by
  induction xs generalizing base with
  | nil=>rfl
  | cons e xs ih=>
    rw [BoolExpr.all,exprNodes,ih,references,List.reverse_cons,foldNodes_append,
      List.length_reverse,RecoveryBoundedAddress.references_length,all_count]
    simp only [prefixNodes,prefixSize,foldNodes,List.append_assoc]
    have he : base+e.nodeCount+prefixSize xs=base+(e.nodeCount+prefixSize xs) := by omega
    rw [he]
    have hf : base+e.nodeCount+(prefixSize xs+xs.length+1)-1=
        base+(e.nodeCount+prefixSize xs)+xs.length := by omega
    rw [hf]
    rfl

theorem prefixSize_append {n : ℕ} (xs ys : List (BoolExpr n)) :
    prefixSize (xs++ys)=prefixSize xs+prefixSize ys := by
  induction xs with
  | nil=>simp only [List.nil_append,prefixSize,Nat.zero_add]
  | cons x xs ih=>simp only [List.cons_append,prefixSize,ih,Nat.add_assoc]

theorem references_append {n : ℕ} (base : ℕ) (xs ys : List (BoolExpr n)) :
    references base (xs++ys)=references base xs++references (base+prefixSize xs) ys := by
  induction xs generalizing base with
  | nil=>simp only [List.nil_append,references,prefixSize,Nat.add_zero]
  | cons x xs ih=>simp only [List.cons_append,references,ih,prefixSize,Nat.add_assoc]

def rows {q bound : ℕ} (count : Fin bound) : List (BoolExpr (descriptionWidth q bound)) :=
  countNodeRows count++outputRowExpr ⟨count.val+1,by omega⟩::countPaddingRows count

theorem original_rows {q bound : ℕ} (count : Fin bound) :
    fixedCountGrammarExpr (n:=q) count=BoolExpr.all (rows (q:=q) count) := rfl

theorem rows_length {q bound : ℕ} (count : Fin bound) :
    (rows (q:=q) count).length=bound+1 := by
  simp only [rows,countNodeRows,countPaddingRows,List.length_append,List.length_cons,List.length_ofFn]
  have hc:=count.isLt
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammar
