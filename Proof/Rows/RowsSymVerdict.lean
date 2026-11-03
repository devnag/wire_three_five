import Proof.Rows.RowsSymMeaning
import Proof.Rows.CountFlags
import Proof.Hierarchy.CompetitorCountTable
import Proof.MachineModel.OrdinaryCompare
import Proof.Rows.FinalDominanceEncoder

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymVerdict
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.CloseoutFinal
open SignedSortKey
noncomputable section

/-! ## 1. Generic focusing -/

theorem focus_at {t u s : Nat} {p : Machine t s} {n : Nat} {hin hout : Fin t → ℕ}
    {tin tout : Fin t → List Bool} (h : Step p n hin tin hout tout) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = hin j) (hA : ∀ j, A (slots j) = tin j) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have h' := h.focus slots hi H A
  rwa [dockH_existing slots H hin hH, install_existing slots A tin hA] at h'

/-! ## 2. The comparator and the counter as `Step`s -/

/-! ## 3. Updating one port -/

theorem install_update {t u : Nat} (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (A : Fin u → List Bool) (tout : Fin t → List Bool) (j0 : Fin t)
    (h : ∀ j, j ≠ j0 → tout j = A (slots j)) :
    install slots A tout = Function.update A (slots j0) (tout j0) := by
  funext x
  by_cases hx : x = slots j0
  · subst hx
    rw [install_slot _ hi, Function.update_self]
  · rw [Function.update_of_ne hx]
    cases hp : RecoveryFocus.pick slots x with
    | none => simp [install, hp]
    | some j =>
      have he := RecoveryFocus.slot_of_pick slots hp
      simp only [install, hp]
      have hj : j ≠ j0 := fun hj => hx (by rw [← he, hj])
      rw [h j hj, he]

/-! ## 4. The local compare phase: four comparisons appended to one bit list -/


/-! ## 5. The SYM cell layout (254 tapes) -/

def symLayout {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) : Fin 254 → α :=
  Fin.addCases (m:=128) (n:=126) F
    (Fin.addCases (m:=18) (n:=108) A (Fin.addCases (m:=107) (n:=1) (fun _ => b) (fun _ => o)))

def auxP (j : Fin 18) : Fin 254 := (j.castAdd 108).natAdd 128
def outP : Fin 254 := (((0 : Fin 1).natAdd 107).natAdd 18).natAdd 128

@[simp] theorem layout_aux {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) (j : Fin 18) :
    symLayout F A b o (auxP j) = A j := by simp [symLayout, auxP]
@[simp] theorem layout_out {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) :
    symLayout F A b o outP = o := rfl

theorem auxP_val (j : Fin 18) : (auxP j).val = 128+j.val := rfl

/-! ## 6. Stages at arbitrary distinct ports -/

/-! ## 7. The bit the machine writes is the row selector -/

variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-! ## 8. The flag stage and the compare stage on the SYM layout -/

def src (L target : Nat) := PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r)

def tIdx (c : Fin 4) : Fin 18 := ⟨12+c.val, by omega⟩

/-! ## 9. The SYM verdict machine and its run -/

def auxIn (w Dc cap : Nat) (N T : Fin 4 → Nat) : Fin 18 → List Bool :=
  ![frame (binary w 0), frame (binary w 0), frame (binary w 0), frame (binary w 0), frame (binary w 0),
    List.replicate Dc false, List.replicate cap false,
    CompareMachine.word (N 0), CompareMachine.word (N 1), CompareMachine.word (N 2), CompareMachine.word (N 3),
    CompareMachine.word 4,
    frame (binary w (T 0)), frame (binary w (T 1)), frame (binary w (T 2)), frame (binary w (T 3)),
    frame (binary w 4), []]


/-- Resident drivers and targets (cell-free: they depend only on the request and the row's offsets). -/
def N (c : Fin 4) : Nat := SymMeaning.driverLen r c.val
def Tg (offset : Fin r.circuits.length → Nat) (c : Fin 4) : Nat := SymMeaning.targetCount r offset c.val

def input (I : Finset (Fin r.q)) (x : BitInput r.q) (L target T w Dc cap : Nat)
    (offset : Fin r.circuits.length → Nat) : Fin 254 → List Bool :=
  symLayout (PCJ45bee56da9f34d5a_NativeFamilyCount.bank I x T 0 (src r L target) []
      (List.replicate (PCJ45bee56da9f34d5a_UniformMinimumBounds.U T r.q (T+1)) false))
    (auxIn w Dc cap (N r) (Tg r offset)) [] []

def cmpCost (w : Nat) : Nat := 2*((2*w+1)+1+((2*w+1)+1+((2*w+1)+1+(2*w+1))))+2

def cost (L target T w : Nat) : Nat :=
  (2*PCJ45bee56da9f34d5a_NativeFamilyFlags.budget 0 r.q L target (SymMeaning.circuits r).length T+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 0) w+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 1) w+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 2) w+2)+1+
  ((2*PCJ45bee56da9f34d5a_CountFlags.budget (N r 3) w+2)+1+
  (cmpCost w+1+((2*PCJ45bee56da9f34d5a_CountFlags.budget 4 w+2)+1+(2*(2*w+1)+2)))))))

end
end RowsConstruction.SymVerdict
