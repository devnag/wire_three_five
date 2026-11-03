import Proof.CaseAnalysis.RowsTupleSeekDock

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.CopyFrames
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
noncomputable section

/-- The concatenated framed fields. -/
def frames (gs : List (List Bool)) : List Bool := gs.flatMap frame
/-- One copy's cost. -/
def cost1 (g : List Bool) : ℕ := 2*g.length+1
/-- The whole loop's cost. -/
def copyCost (gs : List (List Bool)) : ℕ := (gs.map cost1).sum+3*gs.length+3

/-- The loop: repeat the frame copier while the unary driver lasts. -/
def machine := RepeatMachine.machine (frameMachine true) (fun _ _=>true)
def entry (ns : List Bool) (np : ℕ) (out : List Bool) : Configuration 2 3 :=
  ⟨(frameMachine true).start,fieldHeads np out,fieldData ns out⟩
def cfg (phase : Fin 5) (ns : List Bool) (np : ℕ) (out : List Bool) (total cursor : ℕ) :=
  RepeatMachine.cfg phase (entry ns np out) total cursor

theorem frames_cons (g : List Bool) (gs : List (List Bool)) : frames (g::gs)=frame g++frames gs := by
  simp [frames]

theorem remaining (gs : List (List Bool)) (np nt out : List Bool) (total done : ℕ) (hn : done+gs.length=total) :
    ∃ time ≤ (gs.map cost1).sum+2*gs.length+total+3,
      Timed machine time
        (cfg 0 (np++frames gs++nt) np.length out total (done+1))
        (cfg 3 (np++frames gs++nt) (np.length+(frames gs).length) (out++frames gs) total 1) := by
  induction gs generalizing np out done with
  | nil=>
    have hd : done=total := by simpa using hn
    subst done
    refine ⟨total+3,by simp,?_⟩
    simpa [machine,cfg,frames] using
      RepeatMachine.exhaust (frameMachine true) (fun _ _=>true) (entry (np++nt) np.length out) total
  | cons g gs ih=>
    obtain ⟨r,hr,rh,rt,rs⟩ := frame_run true np g (frames gs++nt) out
    have hstep := RepeatMachine.iteration (frameMachine true) (fun _ _=>true)
      (entry (np++frame g++(frames gs++nt)) np.length out) total done r (by rfl)
        (by simp only [List.length_cons] at hn;omega) hr
    simp only [↓reduceIte] at hstep
    rw [RowOccurrenceLoop.cfg_eq 0 r.final
      (entry (np++frame g++(frames gs++nt)) (np.length+(frame g).length) (out++frame g)) total (done+2)
      (by rw [rh];rfl) (by rw [rt];rfl)] at hstep
    obtain ⟨time,ht,tailRun⟩ := ih (np++frame g) (out++frame g) (done+1)
      (by simp only [List.length_cons] at hn;omega)
    simp only [List.append_assoc] at hstep tailRun
    simp only [List.length_append] at tailRun
    rw [show done+1+1=done+2 by omega] at tailRun
    have all := hstep.trans tailRun
    refine ⟨r.steps+2+time,?_,?_⟩
    · simp only [List.map_cons,List.sum_cons,List.length_cons,cost1] at *
      omega
    · simpa only [machine,cfg,frames_cons,List.length_append,List.append_assoc,Nat.add_assoc] using all

theorem run (gs : List (List Bool)) (np nt out : List Bool) :
    ∃ r,runFrom machine (copyCost gs)
      (cfg 0 (np++frames gs++nt) np.length out gs.length 1)=some r ∧
      r.final=cfg 3 (np++frames gs++nt) (np.length+(frames gs).length) (out++frames gs) gs.length 1 ∧
      r.steps ≤ copyCost gs := by
  obtain ⟨time,hb,tr⟩ := remaining gs np nt out gs.length 0 (by omega)
  have hbound : time ≤ copyCost gs := by unfold copyCost;omega
  obtain ⟨r,hr,rf,rs⟩ := tr.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel machine time (copyCost gs-time) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r,more,rf,by omega⟩

/-- The source / output / driver heads of the local bank. -/
def heads (np : ℕ) (out : List Bool) : Fin 3→ℕ := ![np,out.length,1]
/-- The source / output / driver words of the local bank. -/
def data (ns out : List Bool) (n : ℕ) : Fin 3→List Bool := ![ns,out,UnaryTemplate.tape n]

/-- **Copy `|gs|` framed fields**: from `np ++ frames gs ++ nt` at cursor `np.length`, append `frames gs` to the output
(head at its end), driver `UnaryTemplate.tape |gs|` (head 1) unchanged. -/
theorem copy_step (gs : List (List Bool)) (np nt out : List Bool) :
    Step machine (copyCost gs) (heads np.length out) (data (np++frames gs++nt) out gs.length)
      (heads (np.length+(frames gs).length) (out++frames gs))
      (data (np++frames gs++nt) (out++frames gs) gs.length) := by
  obtain ⟨r,hr,rf,_⟩ := run gs np nt out
  have raw := Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have padded := raw.pad (fun i=>if i=2 then gs.length+2 else 0)
  refine (padded.congr_in ?_ ?_).congr ?_ ?_
  all_goals
    funext i;fin_cases i <;>
      simp [cfg,entry,data,heads,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,fieldHeads,fieldData,
        UnaryTemplate.tape,CompareMachine.word,Fin.addCases,ZeroPadding.pad,List.append_assoc]

end
end NearCubicWires.SourceStart.CopyFrames
