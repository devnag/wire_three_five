import Proof.Wire_3_5.UnionMachine.FrontKit

/-! # C6 front, U1b: the atom loop's verdict step (P3:3670)

After one padded decoder run (`FrontAtomDecoder.dec_step`), a register program (C5's `WM`) reads the decoder's flag
tape, raises `BAD` on a rejected atom, counts the atom off `J`, and writes the loop's condition `J ≠ 0 ∧ BAD = 0` into
its cell (the tape the loop controller reads). Main statement: **`tail_spec`**. Paper quantity: the rejection of a
malformed atom. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomTail
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout: stream `F` (the decoder's flag tape); registers `J BAD`; the cell is the loop's condition -/

abbrev TS := WState 0 2

local notation "sF" => (0 : Fin 1)
local notation "rJ" => (0 : Fin 2)
local notation "rBAD" => (1 : Fin 2)

/-- The state: the flag tape `f` (head `0`), the count `J`, the flag `BAD`, the cell. -/
def st (f : List Bool) (J bad : ℕ) (c : Bool) : TS := ⟨![0], ![f], ![J, bad], c⟩

/-- **The verdict step.** -/
def tailP : WM 0 2 :=
  .seq (.ifs sF .skip (WM.setF rBAD)) (.seq (.dec rJ) (.ifr rBAD (.setc false) (.ifr rJ (.setc true) (.setc false))))

/-- The new `BAD`: raised on a rejected atom. -/
def badNext (f : List Bool) (bad : ℕ) : ℕ := if readTapeBit f 0 = true then bad else 1

/-- The loop's condition after the step. -/
def condOf (J bad : ℕ) : Bool := decide (J ≠ 0) && decide (bad = 0)

variable (cap : ℕ)

theorem tail_spec (f : List Bool) (J bad : ℕ) (c : Bool) (hbad : bad ≤ 1) (hJ : J ≤ cap) (hcap : 1 ≤ cap) :
    WExec cap tailP (st f J bad c) (st f (J - 1) (badNext f bad) (condOf (J - 1) (badNext f bad))) 12 := by
  -- the flag
  have s1 : WExec cap (.ifs sF .skip (WM.setF rBAD)) (st f J bad c) (st f J (badNext f bad) c) 5 := by
    by_cases hf : readTapeBit f 0 = true
    · refine WExec.mono (WExec.cast cap (WExec.ifsT (by simpa [wbit, st] using hf) (WExec.skip _)) ?_ le_rfl)
        (by omega)
      simp [badNext, hf]
    · have h := wsetF_spec cap rBAD (st f J bad c) (by simpa [st] using hbad) hcap
      refine WExec.cast cap (WExec.ifsF (by simpa [wbit, st] using hf) h) ?_ le_rfl
      refine WState.eq rfl rfl ?_ rfl
      funext i; fin_cases i <;> simp [st, badNext, hf, Function.update_apply]
  -- the count
  have s2 : WExec cap (.dec rJ) (st f J (badNext f bad) c) (st f (J - 1) (badNext f bad) c) 1 := by
    refine WExec.cast cap (WExec.dec (cap := cap) rJ _ (by simpa [st] using hJ)) ?_ le_rfl
    refine WState.eq rfl rfl ?_ rfl
    funext i; fin_cases i <;> simp [st, Function.update_apply]
  -- the condition
  have s3 : WExec cap (.ifr rBAD (.setc false) (.ifr rJ (.setc true) (.setc false))) (st f (J - 1) (badNext f bad) c)
      (st f (J - 1) (badNext f bad) (condOf (J - 1) (badNext f bad))) 3 := by
    by_cases hb : badNext f bad = 0
    · by_cases hj : J - 1 = 0
      · refine WExec.mono (WExec.ifrF (by simpa [st] using hb) (WExec.ifrF (by simpa [st] using hj)
          (WExec.cast cap (WExec.setc false _) ?_ le_rfl))) (by omega)
        simp [st, WState.setc, condOf, hj, hb]
      · refine WExec.mono (WExec.ifrF (by simpa [st] using hb) (WExec.ifrT (by simpa [st] using hj)
          (WExec.cast cap (WExec.setc true _) ?_ le_rfl))) (by omega)
        simp [st, WState.setc, condOf, hj, hb]
    · refine WExec.mono (WExec.ifrT (by simpa [st] using hb) (WExec.cast cap (WExec.setc false _) ?_ le_rfl))
        (by omega)
      simp [st, WState.setc, condOf, hb]
  exact WExec.mono (s1.seq (s2.seq s3)) (by omega)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomTail
