import Proof.Wire_3_5.FinalPass.Core9Base

/-! # S5Core, part 10: a writer's stage in the core's room (P3:3170-3181)

A writer (any machine on its encoded bank, `CoreWordsM` / `SymWordsM`; this is the generic dock of a machine writer into
a bigger bank, `dock_stage`, reusable by any sub-writer) runs on the room's block `[o, o + sz)`, its registers padded
against the reference `Tc = sent c` from the count's block. **`wstage`**: the room invariant (every room tape within
`c + 1`, the tapes from `o` on blank) moves from `o` to `o + sz`; the outputs are written, the input, the reference and
every tape off the room and the outputs are kept.

Paper quantity: none (the front's machine assembly, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length read_sent)

section Stage
variable {nw : ℕ} (L : S5Lay nw) {mTh mC : ℕ} (hR : Bank.HalfRoom2 L mTh mC)

/-- **The room invariant** at offset `o`: every room tape within `c + 1`, the tapes from `o` on blank. -/
def RInv (c : ℕ) (b : Fin L.t → List Bool) (o : ℕ) : Prop :=
  ∀ i : Fin mC, (b (hR.coreE i)).length ≤ c + 1 ∧ (o ≤ i.val → b (hR.coreE i) = [])

/-- A writer's stage machine on the block `[o, o + sz)`, its registers padded against `Tc`. -/
noncomputable def wstageM {ns nr m s : ℕ} (M : Machine (ns + 2 + nr) s) (sIn : Fin (ns + 1)) (sOut : Fin m → Fin (ns + 1))
    (out : Fin m → Fin L.t) (o : ℕ) (h : o + (ns + 2 + nr) ≤ mC) (Tc : Fin L.t) :=
  Composition.machine (prepP Tc (blk L hR o (ns + 2 + nr) h cTape) (regsOf (blk L hR o (ns + 2 + nr) h))).compile
    (RecoveryFocus.machine (wslots sIn sOut (i0 L) out (blk L hR o (ns + 2 + nr) h)) M)

end Stage

end NearCubicWires.WireExponent3_5.FinalPass.Core
