import Proof.SourceAssembly.SourcePoolHeader
import Proof.SourceAssembly.SourceTopExtract
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolBoot
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
noncomputable section

theorem skip_step (n : Nat) (tail : List Bool) :
    Step (PCPPQueryField.machine false) (2*natBitLength n+3)
      (fun _=>0) ![natWord n++tail,[],[]] (![(natWord n).length,0,0])
      ![natWord n++tail,PCPPQueryField.saved n [],[]] := by
  obtain ⟨f,hf,ff,_⟩:=PCPPQueryField.nat_run false [] tail [] [] n
  apply ((Step.of_run hf (congrArg Configuration.heads ff) (congrArg Configuration.tapes ff)).congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;>simp [PCPPQueryField.cfg,PCPPQueryField.payload,
    PCPPQueryField.selected,PCPPQueryField.saved,DecompositionSource.natWord_length]

def slots : Fin 3→Fin 134:=![61,132,133]
def scan:=RecoveryFocus.machine slots (PCPPQueryField.machine false)
def directions (i : Fin 134) : HeadMove:=if i=61 ∨ i=131 then .right else .stay
def finish:=DecompositionCountPosition.move directions
def machine:=Composition.machine scan finish
def heads (N : Nat) (i : Fin 134):=if i=61 then (natWord (2*N)).length+1 else if i=131 then 1 else 0

theorem run (N P : Nat) (A : Fin 134→List Bool)
    (h61:A 61=ZeroPadding.pad P (natWord (2*N))) (h132:A 132=[]) (h133:A 133=[]) :
    ∃ F,Step machine (2*natBitLength (2*N)+5) (fun _=>0) A (heads N) F ∧
      ∀i : Fin 134,i≠132→F i=A i := by
  let tail:=List.replicate (P-(natWord (2*N)).length) false
  let words : Fin 3→List Bool:=![natWord (2*N)++tail,PCPPQueryField.saved (2*N) [],[]]
  let H:=dockH slots (fun _=>0) (![(natWord (2*N)).length,0,0])
  let F:=install slots A words
  have first:= (skip_step (2*N) tail).dock slots (by decide) (fun _=>0) A
    (by intro i;fin_cases i <;>rfl) (by
      intro i;fin_cases i
      · exact h61
      · exact h132
      · exact h133)
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run directions H F
  have last:Step finish 1 H F (heads N) F:=Step.of_run hr (by
    rw [hf]
    funext i
    have hi:∀i : Fin 134,(∀j,slots j≠i)→H i=0:=by
      intro i h;exact dockH_other slots _ _ i h
    by_cases h:i=61
    · subst i
      have he:H 61=(natWord (2*N)).length:=dockH_slot slots (by decide) _ _ 0
      simp only [directions,heads,ite_true,true_or,he,HeadMove.apply]
    by_cases h':i=131
    · subst i
      have he:H 131=0:=hi _ (by decide)
      simp only [directions,heads,if_neg h,or_true,ite_true,he,HeadMove.apply]
    have he:H i=0:=by
      by_cases h132':i=132
      · subst i;exact dockH_slot slots (by decide) _ _ 1
      by_cases h133':i=133
      · subst i;exact dockH_slot slots (by decide) _ _ 2
      exact hi i (by intro j;fin_cases j <;>first | exact Ne.symm h | exact Ne.symm h132' | exact Ne.symm h133')
    simp only [directions,heads,if_neg h,if_neg h',if_neg (not_or_intro h h'),he,HeadMove.apply])
    (by rw [hf])
  refine ⟨F,first.seq last,?_⟩
  intro i hi
  by_cases h:i=61
  · subst i;exact (install_slot slots (by decide) A words 0).trans h61.symm
  by_cases h':i=133
  · subst i;exact (install_slot slots (by decide) A words 2).trans h133.symm
  exact install_other slots A words i (by intro j;fin_cases j <;>first | exact Ne.symm h | exact Ne.symm hi | exact Ne.symm h')

end
end PCJ6e421fabe2aa4155_SourcePoolBoot
