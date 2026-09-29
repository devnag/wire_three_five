import Proof.MachineModel.OrdinaryAmplifierReplayBounds
import Proof.MachineModel.OrdinaryOracleComposeGraph

/-! Literal selected-amplifier replay in the ordinary oracle interface.
The imported ordinary constructor is actually executed; the raw schema is
physically framed using its produced arity and complete table. -/
namespace NearCubicWires.RepairSource.OrdinaryAmplifierReplay
open LocalBitMultitape RepairOrdinary RepairOrdinary.AmplifierReplay ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def ports (p : OrdinaryProgram) : OrdinaryOracleCompose.Ports (p.tapeCount+1+27) where
  twoTapes := by omega
  outputTape := Dock.output p.tapeCount
  outputFresh := by change p.tapeCount+1+26≠0; omega
  queryTape := Dock.output p.tapeCount
  queryFresh := by change p.tapeCount+1+26≠0; omega

def program (p : OrdinaryProgram) : OrdinaryOracleProgram :=
  (ports p).program (OrdinaryOracleCompose.ordinary (Dock.machine p.machine p.outputTape))

theorem input_tapes (p : OrdinaryProgram) (word : List Bool) :
    Dock.input (p.inputTapes word)=(program p).base.inputTapes word := by
  have ht : 0<p.tapeCount := lt_of_lt_of_le (by decide : 0<2) p.twoTapes
  funext i
  change Dock.input (p.inputTapes word) i=(if i.val=0 then RepairOrdinary.frame word else [])
  refine Fin.addCases (m:=p.tapeCount+1) (n:=27) (fun j => ?_) (fun j => ?_) i
  · refine Fin.addCases (m:=p.tapeCount) (n:=1) (fun j => ?_) (fun j => ?_) j
    · simp only [Dock.input,Fin.addCases_left,Program.inputTapes,Fin.val_castAdd]
      rfl
    · simp only [Dock.input,Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd]
      rw [if_neg (by omega)]
  · simp only [Dock.input,Fin.addCases_right,Fin.val_natAdd]
    rw [if_neg (by omega)]


end
end NearCubicWires.RepairSource.OrdinaryAmplifierReplay
