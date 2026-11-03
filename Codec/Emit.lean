import Codec.Copy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Joins

variable {ns nr : ℕ} (cap : ℕ)

theorem appendO_nil (σ : WState ns nr) (o : Fin (ns + 1)) (OP : Fin nr) (ho : σ.sh o = (σ.st o).length) :
    appendO σ o OP [] = σ := by
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = o
    · subst hj; simp [appendO]
    · simp [appendO, Function.update_of_ne hj]
  · funext j; by_cases hj : j = o
    · subst hj; simp [appendO]
    · simp [appendO, Function.update_of_ne hj]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [appendO]
    · simp [appendO, Function.update_of_ne hr]

/-- Append one raw bit. -/
theorem emitBit_spec (o : Fin (ns + 1)) (OP : Fin nr) (b : Bool) (σ : WState ns nr) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP < cap) : WExec cap (emitC o OP b) σ (appendO σ o OP [b]) 7 := by
  have h := emitC_spec cap o OP b σ ho hc
  simpa [appendO] using h

def emitMarks (o : Fin (ns + 1)) (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: bs => .seq (emitPair o OP b) (emitMarks o OP bs)

theorem emitMarks_spec (o : Fin (ns + 1)) (OP : Fin nr) :
    ∀ (bs : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length → σ.val OP + 2 * bs.length ≤ cap →
      WExec cap (emitMarks o OP bs) σ (appendO σ o OP (marks bs)) (16 * bs.length)
  | [], σ, ho, _ => by
    rw [show marks ([] : List Bool) = [] by simp [marks], appendO_nil σ o OP ho]
    exact WExec.mono (WExec.skip σ) (by simp)
  | b :: bs, σ, ho, hc => by
    have h1 := emitPair_spec cap o OP b σ ho (by simp at hc; omega)
    have h2 := emitMarks_spec o OP bs (appendO σ o OP [true, b]) (by simp [appendO, ho])
      (by simp [appendO] at hc ⊢; omega)
    refine WExec.cast cap (WExec.seq h1 h2) ?_ (by simp; omega)
    rw [appendO_append]; simp [marks]

end NearCubicGates.Close.Codec
