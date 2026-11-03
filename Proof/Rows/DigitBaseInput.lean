import Proof.Rows.CircuitBaseRun
import Proof.Rows.TopIndex

/-! The selected child digit enters as its retained framed binary master.
Its paid unary locator is temporary and is erased after each circuit call. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_DigitBaseInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section

def bank (source locator : List Bool) (circuit child v w C U a : Nat):Fin 75→List Bool:=
  Fin.addCases (m:=73) (n:=2) (motive:=fun _=>List Bool)
    (fun j=>if j=60 then locator else PCJ45bee56da9f34d5a_CircuitBaseInput.bank source [] circuit 0 w C U a j)
    (![List.replicate v true,frame (binary v child)] : Fin 2→List Bool)
def heads (pos : Nat):Fin 75→Nat:=Fin.addCases (m:=73) (n:=2) (motive:=fun _=>Nat)
  (fun j=>if j=60 then pos else PCJ45bee56da9f34d5a_CircuitBaseInput.heads j) (fun _=>0)
def slots:Fin 9→Fin 75:=![73,58,59,61,62,74,60,54,55]
def prepare:=RecoveryFocus.machine slots PCJ45bee56da9f34d5a_TopIndex.machine
def evaluate:=TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_CircuitBaseInput.machine
def lower:=DecompositionCountPosition.move (fun j : Fin 75=>if j=60 then .left else .stay)
def clearSlots:Fin 3→Fin 75:=![60,54,55]
def erase:=RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 1)
def clear:=Composition.machine lower erase
def machine:=Composition.machine (Composition.machine prepare evaluate) clear

theorem bank_driver (source locator : List Bool) (circuit child v w C U a : Nat):
    bank source locator circuit child v w C U a 54=List.replicate U true:=
  PCJ45bee56da9f34d5a_CircuitBaseInput.bank_driver source [] circuit 0 w C U a
theorem bank_log (source locator : List Bool) (circuit child v w C U a : Nat):
    bank source locator circuit child v w C U a 55=List.replicate (U+1) false:=
  PCJ45bee56da9f34d5a_CircuitBaseInput.bank_log source [] circuit 0 w C U a

theorem prepare_run (source : List Bool) (circuit child v w C U a : Nat)
    (hi : child<2^v) (hU : MatrixUnaryTemplate.budget v child<U) :
    Step prepare (MatrixUnaryTemplate.budget v child+2*U+5)
      (heads 0) (bank source (List.replicate U false) circuit child v w C U a)
      (heads 1) (bank source (ZeroPadding.pad U (UnaryTemplate.tape child)) circuit child v w C U a):=by
  have h:=(PCJ45bee56da9f34d5a_TopIndex.run v child U hi hU).dock slots (by decide)
    (heads 0) (bank source (List.replicate U false) circuit child v w C U a)
    (by intro j;fin_cases j <;>rfl)
    (by intro j;fin_cases j <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _ _ | exact ZeroPadding.pad_zero _)
  apply h.congr
  · funext j;fin_cases j
    all_goals first
      | exact (dockH_other slots _ _ _ (by decide)).trans rfl
      | exact dockH_slot slots (by decide) _ _ 0
      | exact dockH_slot slots (by decide) _ _ 1
      | exact dockH_slot slots (by decide) _ _ 2
      | exact dockH_slot slots (by decide) _ _ 3
      | exact dockH_slot slots (by decide) _ _ 4
      | exact dockH_slot slots (by decide) _ _ 5
      | exact dockH_slot slots (by decide) _ _ 6
      | exact dockH_slot slots (by decide) _ _ 7
      | exact dockH_slot slots (by decide) _ _ 8
  · apply HierarchyAllocation.install_eq slots (by decide)
    · intro j;fin_cases j <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _ _ | exact ZeroPadding.pad_zero _
    · intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 6 rfl)

theorem clear_run (source locator : List Bool) (circuit child v w C U a : Nat)
    (hl : locator.length≤U):
    Step clear (2*U+6) (heads 1) (bank source locator circuit child v w C U a)
      (heads 0) (bank source (List.replicate U false) circuit child v w C U a):=by
  obtain ⟨r,hr,hf,_⟩:=DecompositionCountPosition.move_run
    (fun j : Fin 75=>if j=60 then .left else .stay) (heads 1) (bank source locator circuit child v w C U a)
  have first:=(Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)).congr
    (show _=heads 0 by funext j;fin_cases j <;>rfl) rfl
  have last:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1)
    (![locator] : Fin 1→List Bool) (by intro j;fin_cases j;exact hl))).dock clearSlots (by decide)
      (heads 0) (bank source locator circuit child v w C U a)
      (by intro j;fin_cases j <;>rfl)
      (by intro j;fin_cases j <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _ _)
  have last':Step erase (2*U+4) (heads 0) (bank source locator circuit child v w C U a)
      (heads 0) (bank source (List.replicate U false) circuit child v w C U a):=by
    apply last.congr
    · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
    · apply HierarchyAllocation.install_eq clearSlots (by decide)
      · intro j;fin_cases j <;>simp only [Nat.max_self] <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _ _
      · intro j hj;fin_cases j
        all_goals first | rfl | exact False.elim (hj 0 rfl)
  have all:=first.seq last'
  unfold clear lower
  convert all using 1
  first | rfl | omega

theorem prepared_eq (source : List Bool) (circuit child v w C U a : Nat):
    Fin.addCases (m:=73) (n:=2) (motive:=fun _=>List Bool)
      (PCJ45bee56da9f34d5a_CircuitBaseInput.bank source [] circuit child w C U a)
      (![List.replicate v true,frame (binary v child)] : Fin 2→List Bool)=
      bank source (ZeroPadding.pad U (UnaryTemplate.tape child)) circuit child v w C U a:=by
  funext j;fin_cases j <;>first | rfl | exact ZeroPadding.pad_zero _

theorem prepared_heads:
    Fin.addCases (m:=73) (n:=2) (motive:=fun _=>Nat)
      PCJ45bee56da9f34d5a_CircuitBaseInput.heads (fun _=>0)=heads 1:=by
  funext j;fin_cases j <;>rfl
end
end PCJ45bee56da9f34d5a_DigitBaseInput
