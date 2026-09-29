import Proof.CaseAnalysis.CaseTwoRankField

/-! One paid fixed-width field lookup in the original canonical description,
followed by its existing unary-to-binary converter.  The actual source word,
offset and width are retained; all heads return to zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankSlice
open LocalBitMultitape RepairSource.VerifierDecoding OuterPCPRecovery
open RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slice := Rewind.machine SliceMachine.machine
def sliceInput (pre field tail : List Bool) : Fin 5→List Bool :=
  ![frame (pre++field++tail),[],List.replicate pre.length true,
    List.replicate field.length true,[]]
def sliceOutput (pre field tail : List Bool) : Fin 5→List Bool :=
  ![frame (pre++field++tail),field,List.replicate pre.length true,
    List.replicate field.length true,List.replicate (2*pre.length+2*field.length+2) false]
def sliceBudget (offset width : Nat) := 4*offset+4*width+6

theorem slice_ready (pre field tail : List Bool) :
    ClockJoin.ReadyRun slice (sliceBudget pre.length field.length)
      (sliceInput pre field tail) (sliceOutput pre field tail) := by
  obtain ⟨base,hr,hf,hs,_⟩ := SliceMachine.field_run pre field tail
  obtain ⟨r,rr,rt,rl,rh,rs,_⟩ := Rewind.Workspace.reset_workspace SliceMachine.machine _ _ base hr 0
  have hb : 2*base.steps+2=sliceBudget pre.length field.length := by rw [hs];unfold sliceBudget;omega
  have hin : Fin.addCases (motive:=fun _ : Fin 5=>List Bool) (SliceMachine.input pre field tail)
      (fun _ : Fin 1=>List.replicate 0 false)=sliceInput pre field tail := by
    funext i;fin_cases i <;> rfl
  rw [hb,hin] at rr
  refine ⟨r,rr,?_,rh,rs.le.trans_eq hb⟩
  funext i
  fin_cases i
  · exact (rt 0).trans (by rw [hf];rfl)
  · exact (rt 1).trans (by rw [hf];rfl)
  · exact (rt 2).trans (by rw [hf];rfl)
  · exact (rt 3).trans (by rw [hf];rfl)
  · change r.final.tapes 4=List.replicate (2*pre.length+2*field.length+2) false
    have hj : (0 : Fin 1).natAdd 4=(4 : Fin 5) := by decide
    rw [hj,Nat.zero_max,hs] at rl
    exact rl


end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.RankSlice
