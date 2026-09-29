import Proof.Amplification.RecoveryScratchErase
import Proof.Hierarchy.CompetitorCountProducer

/-! Bounded reusable scalar workspace for the validity-list consumer.
Padding records actual retained zero cells; the local machine executes the
same transitions on them, and its output support fits the next paid erase.
The framed scalar loader retains the global stream cursor. -/
namespace NearCubicWires.RepairOrdinary.CompetitorReusableDecision
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalDecision
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity (b : ℕ) := 4096*(b+1)^2

theorem bounded_focused_run {t u s time : ℕ} (slot : Fin t → Fin u)
    (hi : Function.Injective slot) (p : Machine t s)
    (input output : Fin t → List Bool) (h : ClockJoin.ReadyRun p time input output)
    (heads : Fin u → ℕ) (ambient : Fin u → List Bool)
    (hh : ∀ j,heads (slot j)=0) (ht : ∀ j,ambient (slot j)=input j) :
    ∃ r : ExecutionReceipt u s,
      runFrom (RecoveryFocus.machine slot p) time
        (RecoveryCalls.restarted (RecoveryFocus.machine slot p) heads ambient)=some r ∧
      r.final.heads=heads ∧ r.final.tapes=install slot ambient output ∧ r.steps≤time := by
  obtain ⟨base,hr,hout,hheads,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps⟩ := RecoveryFocus.run_config slot hi p heads ambient time
    (initialConfiguration p input) base hr
  have hin : RecoveryFocus.config slot heads ambient (initialConfiguration p input)=
      RecoveryCalls.restarted (RecoveryFocus.machine slot p) heads ambient := by
    apply configuration_ext
    · rfl
    · funext i
      cases hp : RecoveryFocus.pick slot i with
      | none => simp [RecoveryFocus.config,hp,RecoveryCalls.restarted]
      | some j =>
        have he := RecoveryFocus.slot_of_pick slot hp
        simp only [RecoveryFocus.config,hp,initialConfiguration,RecoveryCalls.restarted]
        exact (hh j).symm.trans (congrArg heads he)
    · exact install_existing slot ambient input ht
  rw [hin] at hrun
  refine ⟨r,hrun,?_,?_,hsteps.trans_le hs⟩
  · rw [hf]
    funext i
    cases hp : RecoveryFocus.pick slot i with
    | none => simp [RecoveryFocus.config,hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slot hp
      simp only [RecoveryFocus.config,hp]
      exact (hheads j).trans ((hh j).symm.trans (congrArg heads he))
  · rw [hf]
    change install slot ambient base.final.tapes=install slot ambient output
    rw [hout]

theorem pad_zeros (cap n : ℕ) :
    ZeroPadding.pad cap (List.replicate n false)=List.replicate (max cap n) false := by
  simp only [ZeroPadding.pad,List.length_replicate,← List.replicate_add]
  congr 1
  omega

def loadCfg (q : Fin 4) (source : List Bool) (pos cap : ℕ) (target : List Bool) : Configuration 3 4 :=
  ⟨q,![pos,0,0],![source,target,List.replicate cap false]⟩

theorem padded_load_run (pre bits suffix : List Bool) (cap : ℕ) (hc : 2*bits.length+1≤cap) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom FrameLoad.machine (4*bits.length+3)
        (loadCfg 0 (pre++frame bits++suffix) pre.length cap (List.replicate cap false))=some r ∧
      r.final=loadCfg 3 (pre++frame bits++suffix) (pre.length+2*bits.length+1) cap
        (ZeroPadding.pad cap (frame bits)) ∧ r.steps=4*bits.length+3 := by
  obtain ⟨base,hr,hf,hs,_⟩ := FrameLoad.load_run pre bits suffix [] (by simp)
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config FrameLoad.machine ![0,cap,cap] _ _ base hr
  have hi : ZeroPadding.config ![0,cap,cap]
      (FrameLoad.scan 0 (pre++frame bits++suffix) pre.length [] [])=
      loadCfg 0 (pre++frame bits++suffix) pre.length cap (List.replicate cap false) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,FrameLoad.scan,loadCfg,
        ZeroPadding.pad,StablePartition.Workspace.overlay]
  rw [hi] at hrun
  refine ⟨r,hrun,?_,hsteps.trans hs⟩
  rw [hfinal,hf]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> simp [ZeroPadding.config,FrameLoad.reset,loadCfg,pad_zeros,max_eq_left hc]

end NearCubicWires.RepairOrdinary.CompetitorReusableDecision
