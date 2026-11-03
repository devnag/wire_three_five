import Proof.SourceAssembly.SourceInv
import Proof.SourceAssembly.SourcePrologue

/-! # The per-call driver refresh: `cs 2` and `drv 0, 1, 2, 4` rebuilt from resident masters

**Consumer.** `SourceCyclePad.cycle_prepared_pad`'s `hU0`, `hS`, `hR`, `hB`, `hv`, `hdH` and `hcsH` (`k = 2`) at the refill
prologue's exit. The cycle's frame exports nothing on `cs`/`drv` tapes (see `SourceInv`), so the refill prologue
`clear ; rest ; refresh` rebuilds these five tapes every call: `refreshMachine` clears `rfT 0..4 = B+14..B+18` (the
H1 clear, docked with the resident driver/log `scr 11/12`), copies each master `mT i` onto `rfT i`
(`RecoveryBoundedTapeCopy.copy_ready`, driver/log `scr 11/12`), then moves the four driver heads to `1`.

Also here: `Refill.clear_on`, the H1 clear on ANY injective clear map (the proof of
`SourceClearBound.clear_on_layout`, generalized).

**Paper.** Input processing inside the call (`paper.tex:721-733`). **Budget**: `refreshCost Rc =
(4Rc+7) + 5·((2Rc+4)+1) + 2`, TABLE class through `Rc` (the class of the per-call clear,
`SourceCleanupClass.perCall_class`).
-/
section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction
noncomputable section

namespace Refill

end Refill

namespace Rest

variable {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt2 eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- The refresh's clear map, by value: `B+14 .. B+18`, then `scr 11`, `scr 12`. -/
def clr5V (d : SourceConstruction.Dims) (k : Nat) : Nat :=
  if k < 5 then d.B + 14 + k else if k = 5 then d.scrV 11 else d.scrV 12

def clr5 : Fin (5+1+1) → Fin V := fun k =>
  ⟨clr5V d k.val, Nat.lt_of_lt_of_le (by
    have := k.isLt; have := e.hres2
    simp only [clr5V, SourceConstruction.Dims.scrV, SourceConstruction.Dims.B, SourceConstruction.Dims.U,
      SourceConstruction.Dims.G, SourceConstruction.Dims.prepT]
    split_ifs <;> omega) hV⟩

/-- The copy of master `i` onto target `i`. -/
def copyM (i : Fin 5) :=
  RecoveryFocus.machine (![Dims.mT e hV i, Dims.rfT e hV i, d.scr hV 11, d.scr hV 12] : Fin 4 → Fin V)
    RecoveryBoundedTapeCopy.machine

/-- The four driver heads move right by one. -/
def moveDirs : Fin V → HeadMove := fun x =>
  if d.B + 15 ≤ x.val ∧ x.val ≤ d.B + 18 then HeadMove.right else HeadMove.stay

def moveM := DecompositionCountPosition.move (moveDirs (d := d) (V := V))

/-- **The refresh machine.** ONE fixed machine from the layout. -/
def refreshMachine :=
  Composition.machine (RecoveryFocus.machine (clr5 e hV) (PCJ6e421fabe2aa4155_SourceClear.machine 5))
    (Composition.machine (copyM e hV 0) (Composition.machine (copyM e hV 1)
      (Composition.machine (copyM e hV 2) (Composition.machine (copyM e hV 3)
        (Composition.machine (copyM e hV 4) (moveM (d := d) (V := V)))))))

end Rest
end
end NearCubicWires.SourceConstruction
end
