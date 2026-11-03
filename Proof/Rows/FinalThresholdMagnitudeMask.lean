import Proof.Rows.FinalThresholdChildMagnitude
import Proof.MachineModel.UWalkUnary
import Proof.Circuits.DecompositionCountPosition

/-! Paid all-true magnitude mask and n+1 field counter from the retained native
arity template. Both copies reuse the SAME padded reset log; the arity returns
to head 1. Source/cache location and cold allocation remain caller duties. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdMagnitudeMask
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000

def input (n D : ℕ) : Fin 4 → List Bool :=
  ![UnaryTemplate.tape n,[],[],List.replicate D false]
def output (n D : ℕ) : Fin 4 → List Bool :=
  ![UnaryTemplate.tape n,List.replicate (n+1) true,CompareMachine.word (n+1),List.replicate D false]
def retreat : Fin 4 → HeadMove := ![.left,.stay,.stay,.stay]
def advance : Fin 4 → HeadMove := ![.right,.stay,.right,.stay]
def maskSlots : Fin 3 → Fin 4 := ![0,1,3]
def countSlots : Fin 3 → Fin 4 := ![0,2,3]
noncomputable def mask := RecoveryFocus.machine maskSlots (UWalkUnary.machine false true)
noncomputable def count := RecoveryFocus.machine countSlots (UWalkUnary.machine true true)
noncomputable def machine := Composition.machine
  (Composition.machine (Composition.machine (DecompositionCountPosition.move retreat) mask) count)
  (DecompositionCountPosition.move advance)

private theorem copy_step (sentinel : Bool) (n D : ℕ) (hD : n+2≤D) :
    Step (UWalkUnary.machine sentinel true) (2*n+6) (fun _=>0)
      (![UnaryTemplate.tape n,[],List.replicate D false] : Fin 3 → List Bool)
      (fun _=>0) ![UnaryTemplate.tape n,UWalkUnary.output sentinel true n,List.replicate D false] := by
  have h := (CloseoutFinalSelector.step_of_clock (UWalkUnary.ready sentinel true (n+2) n)).pad (![0,0,D] : Fin 3 → ℕ)
  refine (h.congr_in rfl ?_).congr rfl ?_
  all_goals funext i; fin_cases i
  all_goals simp [UWalkUnary.input,UWalkUnary.result,UWalkUnary.source,
    ZeroPadding.pad,CompareMachine.word,UnaryTemplate.tape,List.length_replicate] <;> omega

theorem mask_count_run (n D : ℕ) (hD : n+2≤D) :
    Step machine (4*n+17) (![1,0,0,0] : Fin 4 → ℕ) (input n D)
      (![1,0,1,0] : Fin 4 → ℕ) (output n D) := by
  obtain ⟨r,hr,hf,_⟩ := DecompositionCountPosition.move_run retreat (![1,0,0,0] : Fin 4 → ℕ) (input n D)
  have first := (Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=(fun _ : Fin 4=>0) by funext i;fin_cases i <;>rfl) rfl
  let middle : Fin 4 → List Bool :=
    ![UnaryTemplate.tape n,List.replicate (n+1) true,[],List.replicate D false]
  have maskRun := (copy_step false n D hD).dock maskSlots (by decide) (fun _ : Fin 4=>0) (input n D)
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  have second : Step mask (2*n+6) (fun _=>0) (input n D) (fun _=>0) middle := by
    refine maskRun.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)) ?_
    funext i;fin_cases i
    all_goals first
      | exact install_slot maskSlots (by decide) _ _ 0
      | exact install_slot maskSlots (by decide) _ _ 2
      | exact install_other maskSlots _ _ _ (by decide)
      | simpa [maskSlots,UWalkUnary.output,UWalkUnary.lead,middle] using install_slot maskSlots (by decide) (input n D)
          (![UnaryTemplate.tape n,UWalkUnary.output false true n,List.replicate D false] : Fin 3 → List Bool) 1
  have countRun := (copy_step true n D hD).dock countSlots (by decide) (fun _ : Fin 4=>0) middle
    (by intro i;fin_cases i <;>rfl) (by intro i;fin_cases i <;>rfl)
  have third : Step count (2*n+6) (fun _=>0) middle (fun _=>0) (output n D) := by
    refine countRun.congr (dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)) ?_
    funext i;fin_cases i
    all_goals first
      | exact install_slot countSlots (by decide) _ _ 0
      | exact install_slot countSlots (by decide) _ _ 2
      | exact install_other countSlots _ _ _ (by decide)
      | simpa [countSlots,UWalkUnary.output,UWalkUnary.lead,output,CompareMachine.word] using install_slot countSlots (by decide) middle
          (![UnaryTemplate.tape n,UWalkUnary.output true true n,List.replicate D false] : Fin 3 → List Bool) 1
  obtain ⟨s,hs,sf,_⟩ := DecompositionCountPosition.move_run advance (fun _ : Fin 4=>0) (output n D)
  have last := (Step.of_run hs (congrArg Configuration.heads sf) (congrArg Configuration.tapes sf)).congr
    (show _=(![1,0,1,0] : Fin 4 → ℕ) by funext i;fin_cases i <;>rfl) rfl
  have all := ((first.seq second).seq third).seq last
  simpa only [machine,show ((1+1+(2*n+6))+1+(2*n+6))+1+1=4*n+17 by omega] using all

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdMagnitudeMask
