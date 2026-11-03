import Proof.Rows.CanonicalBasePrepared
import Proof.Rows.PreludeNatural

/-! Read the actual first native header of a circuit payload. The source is
physically rewound, nine private reader tapes are erased, and the padded unary
arity remains at head one for the selected-child cursor and magnitude update. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopArity
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def heads (pos arity : Nat) (i : Fin 13) : Nat:=if i=0 then pos else if i=10 then arity else 0
def bank (source arity : List Bool) (U : Nat) (i : Fin 13) : List Bool:=
  if i=0 then source else if i=10 then arity else if i=11 then List.replicate (U+1) false
  else if i=12 then List.replicate U true else List.replicate U false
def caps (U : Nat) (i : Fin 12):=if i=10 then U else if i=11 then U+1 else 0
def clearSlots (i : Fin 11) : Fin 13:=if h:i.val<9 then ⟨i.val+1,by omega⟩ else if i=9 then 12 else 11
theorem clear_injective : Function.Injective clearSlots:=by decide

def read:=TapeEmbedding.machine 1 PCJ45bee56da9f34d5a_PreludeNatural.machine
def rewind:=RecoveryFocus.machine (![0,12,11] : Fin 3→Fin 13) CompetitorRecordRewind.machine
def clear:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 9)
def machine:=Composition.machine (Composition.machine read rewind) clear

theorem run (n U : Nat) (tail : List Bool) (hU : PCPPQueryNatural.budget n<U) :
    Step machine (2*PCPPQueryNatural.budget n+4*U+10)
      (heads 0 0) (bank (natWord n++tail) (List.replicate U false) U)
      (heads 0 1) (bank (natWord n++tail) (ZeroPadding.pad U (UnaryTemplate.tape n)) U):=by
  obtain ⟨A,base,asrc,arity,alen⟩:=PCJ45bee56da9f34d5a_PreludeNatural.masked_run U n tail hU
  let out : Fin 13→List Bool:=Fin.addCases (m:=12) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps U i) (Fin.addCases A (fun _ : Fin 1=>List.replicate U false) i))
    (fun _ : Fin 1=>List.replicate U true)
  have first:=(base.pad (caps U)).embed (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate U true)
  have first':Step read (2*PCPPQueryNatural.budget n+2)
      (heads 0 0) (bank (natWord n++tail) (List.replicate U false) U)
      (heads (natWord n).length 1) out:=by
    refine (first.congr_in ?_ ?_).congr ?_ rfl
    · funext i;fin_cases i <;>rfl
    · funext i;fin_cases i <;>simp [caps,bank,PCJ45bee56da9f34d5a_PreludeNatural.input,Fin.addCases,
        ZeroPadding.pad]
    · funext i;fin_cases i <;>simp [heads,PCJ45bee56da9f34d5a_PreludeNatural.heads,Fin.addCases]
  have a0:out 0=natWord n++tail:=by
    change ZeroPadding.pad 0 (A 0)=_
    rw [ZeroPadding.pad_zero,asrc]
  have a10:out 10=ZeroPadding.pad U (UnaryTemplate.tape n):=by
    change ZeroPadding.pad U (A 10)=_
    rw [arity]
  have a11:out 11=List.replicate (U+1) false:=by
    change ZeroPadding.pad (U+1) (List.replicate U false)=_
    exact pad_replicate_false (U+1) U (by omega)
  have a12:out 12=List.replicate U true:=rfl
  have hpos : (natWord n).length≤U:=by
    rw [DecompositionSource.natWord_length]
    unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hU
    omega
  have rew:=CloseoutRowsTupleSeek.rewind_at (0 : Fin 13) 12 11 (by decide) (by decide) (by decide)
    U (heads (natWord n).length 1) out hpos rfl rfl a12 a11
  have second:Step rewind (2*U+2) (heads (natWord n).length 1) out (heads 0 1) out:=by
    refine rew.congr ?_ rfl
    funext i;fin_cases i <;>simp [heads,Function.update]
  let dirty : Fin 9→List Bool:=fun i=>out ⟨i.val+1,by omega⟩
  have hd : ∀ i,(dirty i).length≤U:=by
    intro i
    have h:=alen (⟨i.val+1,by omega⟩ : Fin 11) (by intro h;have:=congrArg Fin.val h;simp at this)
      (by intro h;have:=congrArg Fin.val h;simp at this;have:=i.isLt;omega)
    have ho:dirty i=A ⟨i.val+1,by omega⟩:=by
      fin_cases i <;>exact ZeroPadding.pad_zero _
    rw [ho,h]
  have erased:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1) dirty hd)).dock
    clearSlots clear_injective (heads 0 1) out
    (by intro i;fin_cases i <;>rfl)
    (by intro i;fin_cases i <;>first | rfl | exact a12 | exact a11)
  have last:Step clear (2*U+4) (heads 0 1) out (heads 0 1)
      (bank (natWord n++tail) (ZeroPadding.pad U (UnaryTemplate.tape n)) U):=by
    apply erased.congr
    · exact dockH_existing _ _ _ (by intro i;fin_cases i <;>rfl)
    · apply HierarchyAllocation.install_eq clearSlots clear_injective
      · intro i;fin_cases i <;>simp only [Nat.max_self] <;>rfl
      · intro i hi;fin_cases i
        all_goals first
          | exact a0.symm
          | exact a10.symm
          | exact False.elim (hi 0 rfl)
          | exact False.elim (hi 1 rfl)
          | exact False.elim (hi 2 rfl)
          | exact False.elim (hi 3 rfl)
          | exact False.elim (hi 4 rfl)
          | exact False.elim (hi 5 rfl)
          | exact False.elim (hi 6 rfl)
          | exact False.elim (hi 7 rfl)
          | exact False.elim (hi 8 rfl)
          | exact False.elim (hi 9 rfl)
          | exact False.elim (hi 10 rfl)
  have all:=(first'.seq second).seq last
  simpa only [machine,show (2*PCPPQueryNatural.budget n+2+1+(2*U+2))+1+(2*U+4)=
    2*PCPPQueryNatural.budget n+4*U+10 by omega] using all
end
end PCJ45bee56da9f34d5a_TopArity
