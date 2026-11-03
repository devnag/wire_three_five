import Proof.SourceAssembly.SourceLiveCount
import Proof.Supplier.EquationNaturalHeader

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolHeader
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open PCJ6e421fabe2aa4155_SourceLog (clock_step dock_zero install_blank)
noncomputable section

def fixedSlots : Fin 2→Fin 20:=![1,2]
def productSlots : Fin 4→Fin 20:=![1,0,3,4]
def headerSlots (i : Fin 16) : Fin 20:=if i=0 then 3 else ⟨i.val+4,by omega⟩
theorem header_inj : Function.Injective headerSlots:=by decide
def fixed:=RecoveryFocus.machine fixedSlots (HierarchyFixedWord.machine [true,true])
def product:=RecoveryFocus.machine productSlots ClockUnaryProduct.machine
def header:=RecoveryFocus.machine headerSlots EquationNaturalHeader.machine
def machine:=Composition.machine (Composition.machine fixed product) header
def input (N : Nat) : Fin 20→List Bool:=fun i=>if i=0 then CompareMachine.word N else []
def budget (N : Nat):=6+1+(2*(2*(2*N+3)+2)+2)+1+(EquationNaturalHeader.budget (2*N)+2)

theorem run (N : Nat) : ∃ A,Step machine (budget N) (fun _=>0) (input N) (fun _=>0) A ∧
    A 0=CompareMachine.word N ∧A 18=natWord (2*N) := by
  have h1:=dock_zero (Step.of_ready (HierarchyFixedWord.word_ready [true,true]))
    fixedSlots (by decide) (input N) (by intro i;fin_cases i <;>rfl)
  let A1:=install fixedSlots (input N) (![([true,true] : List Bool),[false,false]])
  have b1:∀i : Fin 20,3≤ i.val→A1 i=[]:=by
    apply install_blank fixedSlots (input N) _ (old:=1) (by omega) (by decide)
    intro i hi
    have hn:i≠0:=by intro h;subst i;contradiction
    exact if_neg hn
  have p1:A1 1=List.replicate 2 true:=install_slot fixedSlots (by decide) (input N) _ 0
  have p0:A1 0=CompareMachine.word N:=install_other fixedSlots (input N) _ 0 (by decide)
  have h2:=dock_zero (PCJ6e421fabe2aa4155_SourceLiveCount.product_step 2 N)
    productSlots (by decide) A1 (by
      intro i;fin_cases i
      · exact p1
      · exact p0
      · exact b1 3 (by decide)
      · exact b1 4 (by decide))
  let A2:=install productSlots A1
    (![List.replicate 2 true,CompareMachine.word N,List.replicate (2*N) true,
      List.replicate (2*(2*N+3)+2) false])
  have b2:∀i : Fin 20,5≤ i.val→A2 i=[]:=
    install_blank productSlots A1 _ (old:=3) (by omega) (by decide) b1
  obtain ⟨H,hH,_h1,h14⟩:=EquationNaturalHeader.header_ready (2*N)
  have h3:=dock_zero (clock_step hH) headerSlots header_inj A2 (by
    intro i;by_cases hi:i=0
    · subst i;exact install_slot productSlots (by decide) A1 _ 2
    · rw [headerSlots,if_neg hi,b2 _ (by
        have hn:i.val≠0:=by intro h;exact hi (Fin.ext h)
        change 5≤ i.val+4
        omega)]
      exact (if_neg hi).symm)
  refine ⟨_,(h1.seq h2).seq h3,?_,?_⟩
  · exact (install_other headerSlots A2 H 0 (by decide)).trans
      (install_slot productSlots (by decide) A1 _ 1)
  · exact (install_slot headerSlots header_inj A2 H 14).trans h14

end
end PCJ6e421fabe2aa4155_SourcePoolHeader
