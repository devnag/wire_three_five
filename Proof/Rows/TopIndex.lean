import Proof.Rows.TopArity
import Proof.MachineModel.OrdinaryMatrixUnaryTemplate

/-! A resident framed binary child digit is converted to the actual unary
locator driver. Four private tapes are cleared; the digit and width survive. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopIndex
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.P1Closure SignedSortKey
noncomputable section

def heads (i : Fin 9) : Nat:=if i=6 then 1 else 0
def bank (w n U : Nat) (arity : List Bool) : Fin 9→List Bool:=
  ![List.replicate w true,List.replicate U false,List.replicate U false,
    List.replicate U false,List.replicate U false,frame (binary w n),arity,
    List.replicate U true,List.replicate (U+1) false]
def caps (U : Nat) (i : Fin 7):=if i=0 ∨ i=5 then 0 else U
def clearSlots : Fin 6→Fin 9:=![1,2,3,4,7,8]
def make:=TapeEmbedding.machine 2 MatrixUnaryTemplate.machine
def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 4)
def machine:=Composition.machine make clear

theorem run (w n U : Nat) (hn : n<2^w) (hU : MatrixUnaryTemplate.budget w n<U) :
    Step machine (MatrixUnaryTemplate.budget w n+2*U+5)
      (fun _=>0) (bank w n U (List.replicate U false))
      heads (bank w n U (ZeroPadding.pad U (UnaryTemplate.tape n))):=by
  obtain ⟨r,hr,r0,r5,r6,h6,hh,_⟩:=MatrixUnaryTemplate.template_run w n hn
  have hheads : r.final.heads=fun i=>if i=6 then 1 else 0:=by
    funext i;by_cases h:i=6
    · subst i;exact h6
    · simp only [h,if_false];exact hh i h
  have base:=Step.of_run hr hheads rfl
  let out : Fin 9→List Bool:=Fin.addCases (m:=7) (n:=2) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps U i) (r.final.tapes i))
    (![List.replicate U true,List.replicate (U+1) false] : Fin 2→List Bool)
  have first:=(base.pad (caps U)).embed (fun _ : Fin 2=>0)
    (![List.replicate U true,List.replicate (U+1) false] : Fin 2→List Bool)
  have first':Step make (MatrixUnaryTemplate.budget w n)
      (fun _=>0) (bank w n U (List.replicate U false)) heads out:=by
    refine (first.congr_in ?_ ?_).congr ?_ rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [MatrixUnaryTemplate.input,caps,bank,Fin.addCases,ZeroPadding.pad]
    · funext i;fin_cases i <;>rfl
  have o0:out 0=List.replicate w true:=by
    change ZeroPadding.pad 0 (r.final.tapes 0)=_;rw [ZeroPadding.pad_zero,r0]
  have o5:out 5=frame (binary w n):=by
    change ZeroPadding.pad 0 (r.final.tapes 5)=_;rw [ZeroPadding.pad_zero,r5]
  have o6:out 6=ZeroPadding.pad U (UnaryTemplate.tape n):=by
    change ZeroPadding.pad U (r.final.tapes 6)=_;rw [r6]
  let dirty : Fin 4→List Bool:=fun i=>out ⟨i.val+1,by omega⟩
  have hd:∀i,(dirty i).length≤U:=by
    intro i
    have hf:=LocalSupport.step_fits base (⟨i.val+1,by omega⟩ : Fin 7) U
      (by fin_cases i <;>simp [MatrixUnaryTemplate.input]) (by omega)
    fin_cases i <;>simpa [dirty,out,Fin.addCases,caps,ZeroPadding.pad_length] using hf
  have last:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) dirty hd)).dock
    clearSlots (by decide) heads out (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>rfl)
  have last':Step clear (2*U+4) heads out heads
      (bank w n U (ZeroPadding.pad U (UnaryTemplate.tape n))):=by
    apply last.congr
    · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
    · apply HierarchyAllocation.install_eq clearSlots (by decide)
      · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
      · intro i hi;fin_cases i
        all_goals first
          | exact o0.symm
          | exact o5.symm
          | exact o6.symm
          | exact False.elim (hi 0 rfl)
          | exact False.elim (hi 1 rfl)
          | exact False.elim (hi 2 rfl)
          | exact False.elim (hi 3 rfl)
          | exact False.elim (hi 4 rfl)
          | exact False.elim (hi 5 rfl)
  have all:=first'.seq last'
  simpa only [machine,show MatrixUnaryTemplate.budget w n+1+(2*U+4)=
    MatrixUnaryTemplate.budget w n+2*U+5 by omega] using all
end
end PCJ45bee56da9f34d5a_TopIndex
