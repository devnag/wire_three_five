import Proof.Rows.Plan
import Proof.Circuits.DecompositionCachedChildAccess

/-! The actual topWord circuit payload has TWO native headers and unframed
children. This paid locator reads those headers and the preceding fixed-arity
children; it leaves the original source at the chosen child's first field. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopChildCursor
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads (pos : Nat) (out : List Bool) : Fin 5→Nat := ![pos,0,out.length,1,1]
def bank (source backing out : List Bool) (n index : Nat) : Fin 5→List Bool :=
  ![source,backing,out,UnaryTemplate.tape n,UnaryTemplate.tape index]
def header := TapeEmbedding.machine 2 (PCPPQueryField.machine false)
def machine := Composition.machine header (Composition.machine header DecompositionSource.Records.machine)
def payload {n : Nat} (gs : List (ExactThresholdGate n)) :=natWord n++exactListWord gs
def prefixWord {n : Nat} (gs : List (ExactThresholdGate n)) (index : Nat) :=
  natWord n++natWord gs.length++(gs.take index).flatMap exactWord
def afterHeaders (n count : Nat) :=PCPPQueryField.saved count (PCPPQueryField.saved n [])
def budget {n : Nat} (gs : List (ExactThresholdGate n)) (index : Nat) :=
  2*natBitLength n+2*natBitLength gs.length+((gs.take index).flatMap exactWord).length+
    (6*n+10)*index+11

theorem header_run (value n index : Nat) (pre tail backing out : List Bool) :
    Step header (2*natBitLength value+3) (heads pre.length out)
      (bank (pre++natWord value++tail) backing out n index)
      (heads (pre.length+(natWord value).length) out)
      (bank (pre++natWord value++tail) (PCPPQueryField.saved value backing) out n index) := by
  obtain ⟨r,hr,hf,_⟩:=PCPPQueryField.nat_run false pre tail backing out value
  have base:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have h:=base.embed (fun _ : Fin 2=>1) (![UnaryTemplate.tape n,UnaryTemplate.tape index] : Fin 2→List Bool)
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>
    simp [heads,bank,PCPPQueryField.cfg,PCPPQueryField.payload,PCPPQueryField.selected,
      PCPPQueryField.saved,DecompositionSource.natWord_length]
      <;>simp [Fin.addCases,Nat.add_assoc]

theorem run {n : Nat} (gs : List (ExactThresholdGate n)) (index : Nat) (hi : index≤gs.length) :
    Step machine (budget gs index) (heads 0 []) (bank (payload gs) [] [] n index)
      (heads (prefixWord gs index).length ((gs.take index).flatMap exactWord))
      (bank (payload gs)
        (DecompositionSource.Records.savedList (gs.take index) (afterHeaders n gs.length))
        ((gs.take index).flatMap exactWord) n index) := by
  have h1:=header_run n n index [] (exactListWord gs) [] []
  have h2:=header_run gs.length n index (natWord n) (gs.flatMap exactWord)
    (PCPPQueryField.saved n []) []
  have hn : (gs.take index).length=index := by simp [List.length_take,Nat.min_eq_left hi]
  obtain ⟨r,hr,ht,hh,_⟩:=DecompositionSource.Records.padded_run (gs.take index)
    (natWord n++natWord gs.length) ((gs.drop index).flatMap exactWord)
    (afterHeaders n gs.length) []
  have hword : (natWord n++natWord gs.length)++(gs.take index).flatMap exactWord++
      (gs.drop index).flatMap exactWord=payload gs := by
    simp only [payload,exactListWord,List.append_assoc]
    rw [←List.flatMap_append,List.take_append_drop]
  rw [hword,hn] at hr ht
  rw [List.nil_append] at ht hh
  have h3:=Step.of_run hr hh ht
  have first : Step header (2*natBitLength n+3) (heads 0 [])
      (bank (payload gs) [] [] n index) (heads (natWord n).length [])
      (bank (payload gs) (PCPPQueryField.saved n []) [] n index) := by
    simpa only [payload,List.length_nil,List.nil_append,Nat.zero_add] using h1
  have second : Step header (2*natBitLength gs.length+3) (heads (natWord n).length [])
      (bank (payload gs) (PCPPQueryField.saved n []) [] n index)
      (heads (natWord n++natWord gs.length).length [])
      (bank (payload gs) (afterHeaders n gs.length) [] n index) := by
    simpa only [payload,exactListWord,afterHeaders,List.length_append,List.append_assoc] using h2
  have last : Step DecompositionSource.Records.machine
      (((gs.take index).flatMap exactWord).length+(6*n+10)*index+3)
      (heads (natWord n++natWord gs.length).length [])
      (bank (payload gs) (afterHeaders n gs.length) [] n index)
      (heads (prefixWord gs index).length ((gs.take index).flatMap exactWord))
      (bank (payload gs)
        (DecompositionSource.Records.savedList (gs.take index) (afterHeaders n gs.length))
        ((gs.take index).flatMap exactWord) n index) := by
    simpa only [hn,heads,bank,prefixWord,List.length_append,List.length_nil] using h3
  have h:=first.seq (second.seq last)
  rw [show (2*natBitLength n+3)+1+((2*natBitLength gs.length+3)+1+
      (((gs.take index).flatMap exactWord).length+(6*n+10)*index+3))=budget gs index by
      unfold budget;omega] at h
  exact h

theorem selected_word {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) :
    payload gs=prefixWord gs i.val++exactWord (gs.get i)++(gs.drop (i.val+1)).flatMap exactWord := by
  rw [payload,DecompositionCachedChild.selected_word gs i.val i.isLt]
  simp only [prefixWord,List.append_assoc,List.get_eq_getElem]

end
end PCJ45bee56da9f34d5a_TopChildCursor
