import Proof.Rows.FinalCellComparator
import Proof.Rows.FinalWalkStep
import Proof.Rows.RowsSymMeaning

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

/-! ## 2. The comparator and the counter as `Step`s -/

/-! ## 3. Updating one port -/

/-! ## 4. The local compare phase: four comparisons appended to one bit list -/


/-! ## 5. The SYM cell layout (254 tapes) -/

def symLayout {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) : Fin 254 → α :=
  Fin.addCases (m:=128) (n:=126) F
    (Fin.addCases (m:=18) (n:=108) A (Fin.addCases (m:=107) (n:=1) (fun _ => b) (fun _ => o)))

def outP : Fin 254 := (((0 : Fin 1).natAdd 107).natAdd 18).natAdd 128

@[simp] theorem layout_out {α : Type} (F : Fin 128 → α) (A : Fin 18 → α) (b o : α) :
    symLayout F A b o outP = o := rfl


/-! ## 6. Stages at arbitrary distinct ports -/

/-! ## 7. The bit the machine writes is the row selector -/

variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-! ## 8. The flag stage and the compare stage on the SYM layout -/

def src (L target : Nat) := PCJ45bee56da9f34d5a_NativeFamilyFlags.source 0 L target (SymMeaning.circuits r)


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

end
end RowsConstruction.SymVerdict
