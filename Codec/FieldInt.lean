import Codec.FieldNum

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Worker.Format

variable {ns nr : ℕ} (cap : ℕ)

/-! ## A counted loop -/

/-- Run `body` while `C ≠ 0`, decrementing `C` first. -/
def repLoop (C : Fin nr) (body : WM ns nr) : WM ns nr := .whr C (.seq (.dec C) body)

/-- `m` iterations along a family of states `g 0, …, g m` (`C = m − i` at `g i`; the body takes `g i` with `C`
decremented to `g (i + 1)`). -/
theorem repLoop_spec (C : Fin nr) (body : WM ns nr) (m c : ℕ) (g : ℕ → WState ns nr)
    (hC : ∀ i ≤ m, (g i).val C = m - i) (hcap : m ≤ cap)
    (hbody : ∀ i < m, WExec cap body ((g i).setv C (m - i - 1)) (g (i + 1)) c) :
    WExec cap (repLoop C body) (g 0) (g m) (m * (c + 4) + 1) := by
  suffices h : ∀ k, k ≤ m → WExec cap (repLoop C body) (g (m - k)) (g m) (k * (c + 4) + 1) by
    simpa using h m le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    have h := WExec.whrF (cap := cap) (P := .seq (.dec C) body) (σ := g m) (by rw [hC m le_rfl]; simp)
    simpa [repLoop] using h
  | succ k ih =>
    intro hk
    have hi : m - (k + 1) < m := by omega
    have hval := hC (m - (k + 1)) (by omega)
    have e1 := WExec.dec (cap := cap) C (g (m - (k + 1))) (by rw [hval]; omega)
    have hd : (g (m - (k + 1))).val C - 1 = m - (m - (k + 1)) - 1 := by rw [hval]
    rw [hd] at e1
    have e2 := hbody (m - (k + 1)) hi
    have hidx : m - (k + 1) + 1 = m - k := by omega
    rw [hidx] at e2
    refine WExec.mono (WExec.whrT (by rw [hval]; omega) (WExec.seq e1 e2) (ih (by omega))) ?_
    have : (k + 1) * (c + 4) = k * (c + 4) + c + 4 := by ring
    omega

/-! ## The integer transcoder -/

/-- The end of an integer field at `p`. -/
def intEnd (w : List Bool) (p : ℕ) : ℕ := p + 1 + fieldLen w (p + 1) + 1 + fieldLen w (p + 1)

end NearCubicGates.Close.Codec
