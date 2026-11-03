import Proof.Packets.DeltaSplitCounters

/-! A finite-control division by two of the actual retained counter. Each
second source mark writes one output mark; paid reset restores all cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.UnaryHalf
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open RecoveryExecution NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 2 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q scan=>if q.val=0 then some ⟨1,![none,some false],fun _=>.right⟩
    else if q.val=3 then none
    else if scan 0 then
      if q.val=1 then some ⟨2,fun _=>none,![.right,.stay]⟩
      else some ⟨1,![none,some true],fun _=>.right⟩
    else some ⟨3,fun _=>none,fun _=>.stay⟩
def phase (k : Nat) : Fin 4 := ⟨k%2+1,by omega⟩
def data (N k : Nat) : Fin 2→List Bool := ![CompareMachine.word N,CompareMachine.word (k/2)]
def heads (k : Nat) : Fin 2→Nat := ![k+1,k/2+1]
def cfg (q : Fin 4) (N k : Nat) : Configuration 2 4 := ⟨q,heads k,data N k⟩

theorem scan_step (N k : Nat) (hk : k<N) :
    step machine (cfg (phase k) N k)=some (cfg (phase (k+1)) N (k+1)) := by
  have hn : readTapeBit (CompareMachine.word N) (k+1)=true :=
    (CompareMachine.read_mark N k).trans (decide_eq_true hk)
  have hm : k%2=0 ∨ k%2=1 := by omega
  rcases hm with hm|hm
  all_goals
    have hp : (k+1)%2=(if k%2=1 then 0 else k%2+1) := by simp [hm];omega
    have hd : (k+1)/2=k/2+(if k%2=1 then 1 else 0) := by simp [hm];omega
    have rule : machine.rule (phase k) (cfg (phase k) N k).scanned=
        some ⟨phase (k+1),![none,if k%2=1 then some true else none],
          ![.right,if k%2=1 then .right else .stay]⟩ := by
      simp [machine,cfg,Configuration.scanned,heads,data,phase,hn,hm,hp]
      funext i;fin_cases i <;>rfl
    change Option.map (applyAction (cfg (phase k) N k))
      (machine.rule (phase k) (cfg (phase k) N k).scanned)=_
    rw [rule]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;>simp [applyAction,cfg,heads,HeadMove.apply,hd,hm]
    · funext i;fin_cases i <;>simp [applyAction,cfg,heads,data,hd,hm,CompareMachine.word,DeltaSplitCounters.write_word]

theorem scan (N n k : Nat) (h : k+n≤N) :
    Timed machine n (cfg (phase k) N k) (cfg (phase (k+n)) N (k+n)) := by
  induction n generalizing k with
  | zero=>simpa only [Nat.add_zero] using Timed.refl machine (cfg (phase k) N k)
  | succ n ih=>
    have first:=Timed.single (by simp [machine,cfg,phase];omega) (scan_step N k (by omega))
    have rest:=ih (k+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using first.trans rest

noncomputable def returned := MaskedReset.machine machine (fun _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.UnaryHalf
