import Proof.Wire_3_5.Primitive.Writers.ThrHB2
import Proof.Wire_3_5.Primitive.SeedFix.C4Pipe

/-! # c4 THR block, the request's strip, part 1: the register loops

The THR stage's input is `frame (req.word ++ hbF)`; the compiler's writer reads `frame req.word`. The strip program
copies the marked prefix of stream `0` (the request's bits) to an output stream and ends it with `false`: it counts the
word's pairs (`cnt3W`), rewinds (`rew2W`), parses the request (`hbXW`'s parse), counts the hash suffix down
(`suf1W`), rewinds, and copies the prefix's pairs (`cpyW`). This part: the four loops' runs.

Paper quantity of the main type: none (the loops' runs on the marked stream). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)

variable {ns nr : ℕ} (cap : ℕ)

theorem marks_cons (b : Bool) (u : List Bool) : marks (b :: u) = true :: b :: marks u := by
  simp [marks]

theorem marks_len (u : List Bool) : (marks u).length = 2 * u.length := by
  induction u with
  | nil => simp [marks]
  | cons b u ih => rw [marks_cons]; simp only [List.length_cons, ih]; ring

theorem rd_at (pre rest : List Bool) (b : Bool) : readTapeBit (pre ++ b :: rest) pre.length = b := by
  simp [readTapeBit]

/-! ## Counting the pairs -/

/-- Count the pairs of the marked stream `i` into three registers. -/
def cnt3W (i : Fin (ns + 1)) (a b c : Fin nr) : WM ns nr :=
  .whs i (.seq (.fwd i) (.seq (.fwd i) (.seq (.inc a) (.seq (.inc b) (.inc c)))))

/-- The state after `k` counted pairs. -/
def cntS (i : Fin (ns + 1)) (a b c : Fin nr) (σ : WState ns nr) (k : ℕ) : WState ns nr :=
  (((σ.seth i (σ.sh i + 2 * k)).setv a (σ.val a + k)).setv b (σ.val b + k)).setv c (σ.val c + k)

theorem cntS_succ (i : Fin (ns + 1)) (a b c : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (σ : WState ns nr) (k : ℕ) : cntS i a b c (cntS i a b c σ 1) k = cntS i a b c σ (k + 1) := by
  unfold cntS
  apply WState.eq
  · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> omega
  · simp
  · funext r
    simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases h1 : r = c
    · subst h1; simp [Ne.symm hac, Ne.symm hbc]; omega
    · by_cases h2 : r = b
      · subst h2; simp [h1, Ne.symm hab]; omega
      · by_cases h3 : r = a
        · subst h3; simp [h1, h2]; omega
        · simp [h1, h2, h3]
  · simp

theorem cnt3W_spec (i : Fin (ns + 1)) (a b c : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (u : List Bool) :
    ∀ (σ : WState ns nr) (pre : List Bool), σ.st i = pre ++ marks u ++ [false] → σ.sh i = pre.length →
      σ.val a + u.length ≤ cap → σ.val b + u.length ≤ cap → σ.val c + u.length ≤ cap →
      WExec cap (cnt3W i a b c) σ (cntS i a b c σ u.length) (17 * u.length + 1) := by
  induction u with
  | nil =>
    intro σ pre hst hsh ha hb hc
    have hbit : wbit σ i = false := by
      simp only [wbit, hst, hsh]; simp [marks, readTapeBit]
    have e : cntS i a b c σ ([] : List Bool).length = σ := by
      unfold cntS
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs with h
        · subst h; simp
        · rfl
      · simp
      · funext r; simp only [WState.setv_val, WState.seth_val, Function.update_apply]; split_ifs <;> simp_all
      · simp
    rw [e]
    exact WExec.mono (WExec.whsF hbit) (by omega)
  | cons x u ih =>
    intro σ pre hst hsh ha hb hc
    have hbit : wbit σ i = true := by
      simp only [wbit, hst, hsh, marks_cons]
      have := rd_at pre (x :: (marks u ++ [false])) true
      simpa [List.append_assoc] using this
    have e1 := WExec.fwd (cap := cap) i σ
    have e2 := WExec.fwd (cap := cap) i (σ.seth i (σ.sh i + 1))
    set σ2 := (σ.seth i (σ.sh i + 1)).seth i ((σ.seth i (σ.sh i + 1)).sh i + 1) with hσ2
    have v2 : σ2.val = σ.val := rfl
    have e3 := WExec.inc (cap := cap) a σ2 (by rw [v2]; simp at ha; omega)
    set σ3 := σ2.setv a (σ2.val a + 1) with hσ3
    have e4 := WExec.inc (cap := cap) b σ3 (by rw [hσ3]; simp [Ne.symm hab, v2]; simp at hb; omega)
    set σ4 := σ3.setv b (σ3.val b + 1) with hσ4
    have e5 := WExec.inc (cap := cap) c σ4 (by rw [hσ4, hσ3]; simp [Ne.symm hac, Ne.symm hbc, v2]; simp at hc; omega)
    set σ5 := σ4.setv c (σ4.val c + 1) with hσ5
    have hs5 : σ5 = cntS i a b c σ 1 := by
      rw [hσ5, hσ4, hσ3, hσ2]
      unfold cntS
      apply WState.eq
      · funext j; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> omega
      · simp
      · funext r
        simp only [WState.setv_val, WState.seth_val, Function.update_apply]
        by_cases h1 : r = c
        · subst h1; simp [Ne.symm hac, Ne.symm hbc]
        · by_cases h2 : r = b
          · subst h2; simp [h1, Ne.symm hab]
          · by_cases h3 : r = a
            · subst h3; simp [h1, h2]
            · simp [h1, h2, h3]
      · simp
    have body : WExec cap (.seq (.fwd i) (.seq (.fwd i) (.seq (.inc a) (.seq (.inc b) (.inc c))))) σ
        (cntS i a b c σ 1) 15 := by
      rw [← hs5]
      exact WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))
    have st1 : (cntS i a b c σ 1).st i = (pre ++ [true, x]) ++ marks u ++ [false] := by
      unfold cntS; simp [hst, marks_cons]
    have sh1 : (cntS i a b c σ 1).sh i = (pre ++ [true, x]).length := by
      unfold cntS; simp [hsh]
    have ea : (cntS i a b c σ 1).val a = σ.val a + 1 := by
      unfold cntS; simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne hac, Function.update_of_ne hab, Function.update_self]
    have eb : (cntS i a b c σ 1).val b = σ.val b + 1 := by
      unfold cntS; simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne hbc, Function.update_self]
    have ec : (cntS i a b c σ 1).val c = σ.val c + 1 := by
      unfold cntS; simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_self]
    have va : (cntS i a b c σ 1).val a + u.length ≤ cap := by rw [ea]; simp at ha; omega
    have vb : (cntS i a b c σ 1).val b + u.length ≤ cap := by rw [eb]; simp at hb; omega
    have vc : (cntS i a b c σ 1).val c + u.length ≤ cap := by rw [ec]; simp at hc; omega
    have h2 := ih (cntS i a b c σ 1) (pre ++ [true, x]) st1 sh1 va vb vc
    rw [cntS_succ i a b c hab hac hbc] at h2
    exact WExec.mono (WExec.whsT hbit body h2) (by simp; omega)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
