import Proof.Wire_3_5.Primitive.Writers.ThrStrip5
import Proof.Wire_3_5.Primitive.SeedFix.C4SI
import Proof.Wire_3_5.Primitive.Writers.ShellLayout
import Proof.SourceAssembly.SourceFactorSelRunBound

/-! # c4 THR block, the THR compiler writer on the THR input: **`thrC3`**, **`thrC3_run`**

The THR stage's port holds `frame (req.word ++ hbF)`; the compiler writer `C` (`C3ReqAt3.thr`) reads `frame req.word`.
`thrC3 C` is one strip step (`stripW` on the numbers machine kit, its capacity the writer's own `1^{pr}` port) then
`C.M` with its request port on the strip's output tape. Its run on `req.word ++ hbF` has the same outputs `frame PRE`,
`frame POST` (`thrC3_run`); the stripped copy and the strip's tapes are residues.

Paper quantity of the main type: the THR call's compiler request fields `PRE`/`POST` (P3:1886-1906), from the THR
input word. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C3ReqIface (C3Stage C3Run c3In c3Out)

variable (C : C3Stage)

/-- The strip machine's inputs on the wrapper: the request port, the capacity `1^{pr}`. -/
def stripExt (j : Fin (BX + 1)) : Option (Fin (C.t + (BX + 1))) :=
  if j.val = 0 then some (Fin.castAdd _ C.inS) else if j.val = 674 then some (Fin.castAdd _ C.pS) else none

theorem hoffS : C.t + (BX + 1) ≤ C.t + (BX + 1) := le_rfl

/-- The stripped request's tape (the strip's stream `122`). -/
def yT : Fin (C.t + (BX + 1)) := ⟨C.t + 123, by have : BX = 676 := rfl; omega⟩

/-- The writer's slots: its request port on the stripped tape, every other tape in place. -/
def c3Sl (j : Fin C.t) : Fin (C.t + (BX + 1)) := if j = C.inS then yT C else Fin.castAdd _ j

theorem c3Sl_inj : Function.Injective (c3Sl C) := by
  intro x y h
  unfold c3Sl at h
  by_cases hx : x = C.inS <;> by_cases hy : y = C.inS
  · rw [hx, hy]
  · rw [if_pos hx, if_neg hy] at h
    have := congrArg Fin.val h; simp [yT] at this; have := y.isLt; omega
  · rw [if_neg hx, if_pos hy] at h
    have := congrArg Fin.val h; simp [yT] at this; have := x.isLt; omega
  · rw [if_neg hx, if_neg hy] at h
    exact Fin.castAdd_injective _ _ h

theorem distinctT : [Fin.castAdd (BX + 1) C.inS, Fin.castAdd (BX + 1) C.hS, Fin.castAdd (BX + 1) C.qS,
    Fin.castAdd (BX + 1) C.mS, Fin.castAdd (BX + 1) C.pS, Fin.castAdd (BX + 1) C.preS,
    Fin.castAdd (BX + 1) C.postS].Nodup := by
  have h := C.distinct
  have e : [Fin.castAdd (BX + 1) C.inS, Fin.castAdd (BX + 1) C.hS, Fin.castAdd (BX + 1) C.qS,
      Fin.castAdd (BX + 1) C.mS, Fin.castAdd (BX + 1) C.pS, Fin.castAdd (BX + 1) C.preS,
      Fin.castAdd (BX + 1) C.postS] = [C.inS, C.hS, C.qS, C.mS, C.pS, C.preS, C.postS].map (Fin.castAdd (BX + 1)) := rfl
  rw [e]
  exact h.map (Fin.castAdd_injective C.t (BX + 1))

/-- **The THR compiler writer**: the strip, then `C.M` on the stripped request. -/
noncomputable def thrC3 : C3Stage where
  t := C.t + (BX + 1)
  s := _
  M := Composition.machine (RecoveryFocus.machine (slx C.t (hoffS C) (stripExt C)) (bigM stripW))
    (RecoveryFocus.machine (c3Sl C) C.M)
  inS := Fin.castAdd _ C.inS
  hS := Fin.castAdd _ C.hS
  qS := Fin.castAdd _ C.qS
  mS := Fin.castAdd _ C.mS
  pS := Fin.castAdd _ C.pS
  preS := Fin.castAdd _ C.preS
  postS := Fin.castAdd _ C.postS
  distinct := distinctT C

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
