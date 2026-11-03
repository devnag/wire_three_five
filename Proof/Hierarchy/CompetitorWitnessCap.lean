import Proof.Hierarchy.CompetitorWitnessCapLoop

/-! Cold whole-witness cap, with the rewind physically paid. The bound is
linear in the actual input length for every witness, including an overlong
one; only a true result licenses the subsequent nested decoder. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessCap
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def guard := Rewind.machine machine
def input (x w : List Bool) : Fin 4→List Bool := ![frame x,frame w,[],[]]
def output (x w : List Bool) (scratch : ℕ) : Fin 4→List Bool :=
  ![frame x,frame w,[decide (16*w.length≤x.length)],List.replicate scratch false]

theorem cap_ready (x w : List Bool) :
    ∃ scratch,scratch≤3*x.length+2 ∧
      ReadyRun guard (2*scratch+2) (input x w) (output x w scratch) := by
  obtain ⟨base,hbase,hbt,hbs⟩ := raw_run x w
  obtain ⟨r,hr,ht,hcounter,hh,hsteps,_⟩ := Rewind.Workspace.reset_workspace machine
    (3*x.length+2) ![frame x,frame w,[]] base hbase 0
  have hin : (Fin.addCases (m:=3) (n:=1) (motive:=fun _ : Fin 4=>List Bool)
      ![frame x,frame w,[]] (fun _ : Fin 1=>List.replicate 0 false))=input x w := by
    funext i; fin_cases i <;> rfl
  rw [hin] at hr
  refine ⟨base.steps,hbs,r,hr,?_,hh,hsteps⟩
  funext i
  fin_cases i
  · exact (ht 0).trans (congrFun hbt 0)
  · exact (ht 1).trans (congrFun hbt 1)
  · exact (ht 2).trans (congrFun hbt 2)
  · simpa [output] using hcounter

end NearCubicWires.RepairOrdinary.CompetitorWitnessCap
