import Proof.SourceAssembly.SourceLoop
import Proof.SourceAssembly.SourceWiring

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
namespace NearCubicWires.SourceConstruction
noncomputable section

/-- The size of the per-call block. -/
def restPc (eX pX gW : Nat) : Nat := 71 + eX + pX + gW

namespace Dims
variable (d : Dims)
/-- The enlarged clear set's stage count. -/
def tcl2 (eX pX gW : Nat) : Nat := d.tcl + 14 + restPc eX pX gW

/-- The extra fact this placement needs: the reserved region holds `B .. B+18`, the per-call block and five
residents. -/
structure RestExt (eX pX gW : Nat) : Prop where
  ext : d.Ext
  hres : 19 + restPc eX pX gW + 5 ≤ d.res

/-- The enlarged clear set, by value. -/
def clr2V (eX pX gW i : Nat) : Nat :=
  if i < d.tcl then d.clearV i
  else if i < d.tcl + 14 then d.B + (i - d.tcl)
  else if i < d.tcl2 eX pX gW then d.B + 19 + (i - d.tcl - 14)
  else if i = d.tcl2 eX pX gW then d.scrV 11
  else d.scrV 12

/-- Membership in the enlarged clear set, by value. -/
def InClear (eX pX gW v : Nat) : Prop :=
  (d.F ≤ v ∧ v < d.F + d.rt) ∨ (d.G ≤ v ∧ v < d.G + d.pscr) ∨ (d.B ≤ v ∧ v < d.B + 14) ∨
    (d.B + 19 ≤ v ∧ v < d.B + 19 + restPc eX pX gW)

variable {d} {eX pX gW : Nat} (e : d.RestExt eX pX gW) {V : Nat} (hV : d.U ≤ V)

/-- A per-call block tape. -/
def pcT (i : Fin (restPc eX pX gW)) : Fin V :=
  ⟨d.B + 19 + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres; unfold B U G prepT; omega) hV⟩
/-- A prologue resident. -/
def rsT (i : Fin 5) : Fin V :=
  ⟨d.B + 19 + restPc eX pX gW + i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres; unfold B U G prepT; omega) hV⟩
/-- The thirteen tapes between the family bank and `G` (`enc 0..4`, `enc 6..10`, `app 2, 4, 5`). -/
def encT (k : Fin 13) : Fin V :=
  ⟨d.F + d.rt + k.val, Nat.lt_of_lt_of_le (by have := k.isLt; unfold U G prepT; omega) hV⟩

/-- The enlarged clear set: stage tapes, then the driver `scr 11`, then the log `scr 12`. -/
def clr2 : Fin (d.tcl2 eX pX gW + 1 + 1) → Fin V := fun i =>
  ⟨d.clr2V eX pX gW i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := e.hres
    simp only [clr2V, clearV, scrV, tcl2, tcl, pscr, restPc, B, U, G, prepT] at *
    split_ifs <;> omega) hV⟩

end Dims

/-- Unfold every value of the rest layout and close an interval (in)equality. -/
macro "rgeo" : tactic => `(tactic| (simp only [Dims.pcT, Dims.rsT, Dims.encT, Dims.clr2, Dims.clr2V,
  Dims.clearV, Dims.scrV, Dims.tcl2, Dims.tcl, Dims.pscr, restPc, Dims.B, Dims.G, Dims.slot, Dims.maskSlots,
  Dims.pslots, Dims.poolSlots, Dims.ret, Dims.scr, Dims.familySlots, Dims.rewind2Slots, Dims.csSlots,
  Dims.drvSlots, Dims.natSlots, Dims.lenTape, Dims.slotV, Dims.maskV, Dims.pV, Dims.poolV, Dims.retV,
  Dims.famV, Dims.rw2V, Dims.csV, Dims.drvV, Dims.InClear, Fin.val_mk] at * <;> (try split_ifs at *) <;> omega))

namespace Dims

end Dims

end
end NearCubicWires.SourceConstruction
end
