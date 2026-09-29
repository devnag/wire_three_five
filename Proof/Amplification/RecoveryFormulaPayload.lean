import Proof.Amplification.RecoveryFormulaSerializeFrame

/-! The exact existing balanced CNF payload is produced on a fresh framed
oracle output. Its sole input is the actual stream of ordinary clause codes;
the following formula emitter must produce that stream from the same PCP. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaPayload
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open ProjectionNormalization CanonicalBinary BalancedCNFSATEncoding OrdinaryOracleCompose
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ports : Ports 133 := ⟨by decide,131,by decide,131,by decide⟩
noncomputable def program := ports.program (ordinary RecoveryFormulaFrame.machine)

theorem input_tapes (fields : List (List Bool)) :
    RecoveryFormulaFrame.input fields=(program.base.inputTapes (FieldList.stream fields)) := by
  funext i
  change Fin.addCases (RecoveryFormulaSerialize.input fields) (fun _ : Fin 2=>[]) i=
    (if i.val=0 then RepairOrdinary.frame (FieldList.stream fields) else [])
  refine Fin.addCases (m:=131) (n:=2) (fun j=>?_) (fun j=>?_) i
  · simp only [Fin.addCases_left,Fin.val_castAdd,RecoveryFormulaSerialize.input]
    rfl
  · simp only [Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]

def fields (formula : EncodedCNF) := formula.map (fun clause=>(Encodable.encode clause).bits)
def input (formula : EncodedCNF) := FieldList.stream (fields formula)

theorem exact_code (formula : EncodedCNF) : PCPTraversal.code (fields formula)=balancedCNFPayload formula := by
  have hf : fields formula=(formula.map Encodable.encode).map Nat.bits := by simp [fields]
  rw [hf,PCPTripleNative.code_values]
  rfl

end NearCubicWires.RepairSource.RecoveryFormulaPayload
