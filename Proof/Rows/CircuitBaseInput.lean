import Proof.Rows.TopFrameReentry
import Proof.Rows.SelectedBaseRun

/-! Actual framed top-source extraction shares the selected-child base bank.
The extracted payload is padded on private57 and erased after consumption. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CircuitBaseInput
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def caps (U : Nat) (j : Fin 71):=if j=57 then U else 0
def bank (source payload : List Bool) (circuit child w C U a : Nat):Fin 73→List Bool:=
  Fin.addCases (m:=71) (n:=2) (motive:=fun _=>List Bool)
    (fun j=>ZeroPadding.pad (caps U j) (PCJ45bee56da9f34d5a_SelectedBase.bank payload
      (List.replicate U false) (List.replicate U false) child w C U a j))
    (![frame source,ZeroPadding.pad U (CompareMachine.word circuit)] : Fin 2→List Bool)
def heads:Fin 73→Nat:=Fin.addCases (m:=71) (n:=2) (motive:=fun _=>Nat)
  (PCJ45bee56da9f34d5a_SelectedBase.heads 0) (![0,1] : Fin 2→Nat)
def slots:Fin 10→Fin 73:=![71,58,59,72,61,62,57,63,54,55]
def extract:=RecoveryFocus.machine slots PCJ45bee56da9f34d5a_TopFrameReentry.machine
def evaluate:=TapeEmbedding.machine 2 PCJ45bee56da9f34d5a_SelectedBase.machine
def wipeSlots:Fin 3→Fin 73:=![57,54,55]
def wipe:=RecoveryFocus.machine wipeSlots (RecoveryScratchErase.resetMachine 1)
def machine:=Composition.machine (Composition.machine extract evaluate) wipe

theorem bank_driver (source payload : List Bool) (circuit child w C U a : Nat) :
    bank source payload circuit child w C U a 54=List.replicate U true:=by
  change ZeroPadding.pad 0 (PCJ45bee56da9f34d5a_SelectedBase.Base.input (List.replicate U false) 0 w C U a 54)=_
  rw [ZeroPadding.pad_zero,PCJ45bee56da9f34d5a_SelectedBase.input_driver]
theorem bank_log (source payload : List Bool) (circuit child w C U a : Nat) :
    bank source payload circuit child w C U a 55=List.replicate (U+1) false:=by
  change ZeroPadding.pad 0 (PCJ45bee56da9f34d5a_SelectedBase.Base.input (List.replicate U false) 0 w C U a 55)=_
  rw [ZeroPadding.pad_zero,PCJ45bee56da9f34d5a_SelectedBase.input_log]

theorem extract_run (words : List (List Bool)) (i : Fin words.length) (B child w C U a : Nat)
    (hb : ∀x∈words,x.length≤B) (hu : PCJ45bee56da9f34d5a_TopFrameReentry.budget words i B+2≤U) :
    Step extract (PCJ45bee56da9f34d5a_TopFrameReentry.budget words i B+4*U+12)
      heads (bank (words.flatMap frame) [] i.val child w C U a)
      heads (bank (words.flatMap frame) (words.get i) i.val child w C U a):=by
  have h:=(PCJ45bee56da9f34d5a_TopFrameReentry.run words i B U hb hu).dock slots (by decide)
    heads (bank (words.flatMap frame) [] i.val child w C U a)
    (by intro j;fin_cases j <;>rfl)
    (by intro j;fin_cases j <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _ | exact ZeroPadding.pad_zero _)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
  · apply HierarchyAllocation.install_eq slots (by decide)
    · intro j;fin_cases j <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _ | exact ZeroPadding.pad_zero _
    · intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 6 rfl)

theorem wipe_run (source payload : List Bool) (circuit child w C U a : Nat)
    (hp : payload.length≤U) :
    Step wipe (2*U+4) heads (bank source payload circuit child w C U a)
      heads (bank source [] circuit child w C U a):=by
  have h:=(Step.of_ready (RecoveryScratchErase.erase_ready U (U+1)
    (![ZeroPadding.pad U payload] : Fin 1→List Bool)
    (by intro j;fin_cases j;simp [ZeroPadding.pad_length];omega))).dock wipeSlots (by decide)
      heads (bank source payload circuit child w C U a)
      (by intro j;fin_cases j <;>rfl) (by intro j;fin_cases j <;>first | rfl | exact bank_driver _ _ _ _ _ _ _ _ | exact bank_log _ _ _ _ _ _ _ _)
  apply h.congr
  · exact dockH_existing _ _ _ (by intro j;fin_cases j <;>rfl)
  · apply HierarchyAllocation.install_eq wipeSlots (by decide)
    · intro j;fin_cases j <;>simp only [Nat.max_self]
      · simp [bank,caps,wipeSlots,Fin.addCases,PCJ45bee56da9f34d5a_SelectedBase.bank,
          PCJ45bee56da9f34d5a_SelectedBase.extras,ZeroPadding.pad]
      · exact bank_driver _ _ _ _ _ _ _ _
      · exact bank_log _ _ _ _ _ _ _ _
    · intro j hj;fin_cases j
      all_goals first | rfl | exact False.elim (hj 0 rfl)
end
end PCJ45bee56da9f34d5a_CircuitBaseInput
