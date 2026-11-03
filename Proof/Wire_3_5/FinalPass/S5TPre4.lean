import Proof.Wire_3_5.FinalPass.S5TPre3
import Proof.Wire_3_5.Primitive.Writers.DockW
import Proof.Wire_3_5.UnionMachine.FrontFill

/-! # S5-THR, part 4: the front's prelude as a machine (P3:3170-3181)

From the final pass's entry bank (the framed input on tape `0`, every other tape blank, every head at `0`) to a
register-program state at capacity `2W + 2`, `W = (|u|+1)^{D+1}`, on any layout `(ns, nr)`:
1. the cell `[false]` (`cellP`);
2. the count program `preW` on its own register-free layout (`preSub`), docked on the streams `fs` (`Step.dock`);
3. `FrontFill.fillP` from the count `C = 1^W`: every register tape `regTape (2W+2) 0 = 0^{2W+3}`, the marker tape
   `aux` likewise.

**`pre_step`**: the whole prelude as one `Step`, ending at `wenc (2W+2) (σ0 …)` with every head at `0`; `σ0`'s
streams are the count program's words on `fs`, `0^{2W+3}` on `aux`, blank elsewhere. No tape holds anything but
these words: the prelude leaves no junk.

Paper quantity of the main type: the front's register capacity `2(|fpIn|+1)^{D+1} + 2`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj sTape_ne_c sTape_ne_r cTape_ne_r wslot
  wslot_s wslot_c wenc_A_c wenc_H_c)

/-! ## The count program's own layout -/


/-! ## The prelude on a layout -/

variable {ns nr : ℕ}

/-- The cell `[false]`. -/
def cellP : Prog (ns + 2 + nr) := .act (writeAt cTape false) (fun _ => .stay)

/-- The prelude's slot map (the count program's streams by `fs`, its cell to the cell). -/
def preSlots (D : ℕ) (fs : Fin (D + 4) → Fin (ns + 1)) : Fin (D + 3 + 2 + 0) → Fin (ns + 2 + nr) :=
  wslot fs Fin.elim0

theorem preSlots_inj (D : ℕ) (fs : Fin (D + 4) → Fin (ns + 1)) (hfs : Function.Injective fs) :
    Function.Injective (preSlots (nr := nr) D fs) := by
  intro a b h
  rcases tape_cases a with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rcases tape_cases b with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
    · simp only [preSlots, wslot_s] at h; rw [hfs (sTape_inj h)]
    · simp only [preSlots, wslot_s, wslot_c] at h; exact absurd h (sTape_ne_c _)
    · exact r.elim0
  · rcases tape_cases b with ⟨k, rfl⟩ | rfl | ⟨r, rfl⟩
    · simp only [preSlots, wslot_s, wslot_c] at h; exact absurd h.symm (sTape_ne_c _)
    · rfl
    · exact r.elim0
  · exact r.elim0

end NearCubicWires.WireExponent3_5.FinalPass.S5T
