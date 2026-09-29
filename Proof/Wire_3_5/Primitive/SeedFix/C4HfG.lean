import Proof.Wire_3_5.Primitive.SeedFix.C4HfF

/-! # The HASH child family, part 7: the read-out's terminator

`filt:soft`, P3:2285-2290: the printer leaves the terms' records `hashTermsM.flatMap (true :: termWord ·)` on its
output stream, with the ruler `1^{|OUT|}`; the expression word (`exprWord`) ends with the terminator `false`. **`app_spec`**:
`appW` walks the ruler and writes the terminator at the output's end.

Paper quantity of the main type: the printed expression's word `exprWord V_p`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Append the terminator to stream `0` at the length of the ruler on stream `1`. -/
def appW : WM 1 0 := .seq (.whs 1 (.seq (.fwd 1) (.fwd 0))) (.wr 0 false)

/-- The state with `x` on stream `0` and the ruler `1^{|x|}` on stream `1`, both heads at `k`. -/
def apSt (x : List Bool) (k : ℕ) : WState 1 0 :=
  ⟨fun _ => k, fun i => if i.val = 0 then x else List.replicate x.length true, Fin.elim0, false⟩

theorem term_loop (cap : ℕ) (x : List Bool) :
    ∀ i k : ℕ, i + k = x.length → WExec cap (.whs 1 (.seq (.fwd 1) (.fwd 0)) : WM 1 0) (apSt x k) (apSt x x.length)
      (5 * i + 1)
  | 0, k, h => by
    simp only [Nat.zero_add] at h
    subst h
    refine WExec.whsF ?_
    show readTapeBit (List.replicate x.length true) x.length = false
    simp [readTapeBit]
  | i + 1, k, h => by
    have hb : wbit (apSt x k) 1 = true := by
      show readTapeBit (List.replicate x.length true) k = true
      rw [readTapeBit, List.getD_eq_getElem _ _ (by simp; omega)]; simp
    have a1 := WExec.fwd (cap := cap) (1 : Fin 2) (apSt x k)
    have a2 := WExec.fwd (cap := cap) (0 : Fin 2) ((apSt x k).seth 1 ((apSt x k).sh 1 + 1))
    have e : ((apSt x k).seth 1 ((apSt x k).sh 1 + 1)).seth 0
        (((apSt x k).seth 1 ((apSt x k).sh 1 + 1)).sh 0 + 1) = apSt x (k + 1) := by
      apply WState.eq
      · funext j; fin_cases j <;> simp [apSt, WState.seth, Function.update_apply]
      · rfl
      · funext r; exact r.elim0
      · rfl
    rw [e] at a2
    have ih := term_loop cap x i (k + 1) (by omega)
    exact WExec.cast cap (WExec.whsT hb (WExec.seq a1 a2) ih) rfl (by omega)

/-- **The terminator**: from `x` and `1^{|x|}` (heads `0`), `x ++ [false]` on stream `0`. -/
theorem app_spec (cap : ℕ) (x : List Bool) :
    ∃ τ : WState 1 0, WExec cap appW (apSt x 0) τ (5 * x.length + 3) ∧ τ.st 0 = x ++ [false] := by
  have t1 := term_loop cap x x.length 0 (by omega)
  have t2 := WExec.wr (cap := cap) (0 : Fin 2) false (apSt x x.length)
  refine ⟨_, WExec.cast cap (WExec.seq t1 t2) rfl (by omega), ?_⟩
  show Function.update (apSt x x.length).st 0 (writeTapeBit x x.length false) 0 = _
  rw [Function.update_self, C4Pipe.write_end]

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
