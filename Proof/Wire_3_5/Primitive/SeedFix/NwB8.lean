import Proof.Wire_3_5.Primitive.SeedFix.NwB7

/-! # NW phase (b), part 8: the final clear and restore

**`finW`** (`fin_spec`): every register but the saves `s0 … s3` and `V`'s `rA` cleared (`NumsC.clearL`), then
the saves moved back into `rN, rM, rE, rT` and `V` into `rV`: the registers of `NumsPh3.AfterV`.

Paper quantity of the main type: phase (b)'s exit registers `n`, the mode bit, `e`, `T_f`, `V` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

/-- The registers the final clear keeps: the saves and `V`. -/
def keepR : List (Fin LNR) := [s0, s1, s2, s3, rA]

/-- The registers the final clear zeroes. -/
def clrR : List (Fin LNR) := (List.finRange LNR).filter (fun r => r ∉ keepR)

theorem mem_clrR (r : Fin LNR) : r ∈ clrR ↔ r ∉ keepR := by simp [clrR]

theorem clrR_len : clrR.length ≤ 512 := by
  unfold clrR
  exact (List.length_filter_le _ _).trans (by simp)

variable (cap : ℕ) (x : ℕ)

theorem zeroL_st' (σ : WState (LNS x) LNR) (rs : List (Fin LNR)) : (NumsC.zeroL σ rs).st = σ.st := rfl
theorem zeroL_sh' (σ : WState (LNS x) LNR) (rs : List (Fin LNR)) : (NumsC.zeroL σ rs).sh = σ.sh := rfl
theorem zeroL_cell' (σ : WState (LNS x) LNR) (rs : List (Fin LNR)) : (NumsC.zeroL σ rs).cell = σ.cell := rfl
theorem zeroL_val' (σ : WState (LNS x) LNR) (rs : List (Fin LNR)) (r : Fin LNR) :
    (NumsC.zeroL σ rs).val r = if r ∈ rs then 0 else σ.val r := rfl

/-- Register bookkeeping: `setv` chains at the literal registers. -/
local macro "vsimp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := {decide := true}) [WState.setv_val, Function.update_apply, $hs,*])

/-- **The final clear and restore.** -/
def finW : WM (LNS x) LNR :=
  .seq (NumsC.clearL clrR) (.seq (WM.move s0 NumsPh2.rN) (.seq (WM.move s1 NumsPh2.rM) (.seq (WM.move s2 NumsPh2.rE)
  (.seq (WM.move s3 NumsPh2.rT) (WM.move rA NumsPh2.rV)))))

theorem fin_spec (σ : WState (LNS x) LNR) (vN vM vE vT V : ℕ) (hN : σ.val s0 = vN) (hM : σ.val s1 = vM)
    (hE : σ.val s2 = vE) (hT : σ.val s3 = vT) (hV : σ.val rA = V) (hb : ∀ r, σ.val r ≤ cap) :
    ∃ τ c, WExec cap (finW x) σ τ c ∧ c ≤ 512 * (3 * cap + 2) + 7 * (vN + vM + vE + vT + V) + 10 ∧
      τ.val NumsPh2.rN = vN ∧ τ.val NumsPh2.rM = vM ∧ τ.val NumsPh2.rE = vE ∧ τ.val NumsPh2.rT = vT ∧
      τ.val NumsPh2.rV = V ∧
      (∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → q ≠ NumsPh2.rV → τ.val q = 0) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  obtain ⟨c1, e1, c1le⟩ := NumsC.clearL_spec cap cap le_rfl clrR σ (fun r _ => hb r)
  have hl := clrR_len
  have c1le' : c1 ≤ 512 * (3 * cap + 2) := c1le.trans (Nat.mul_le_mul_right _ hl)
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = NumsC.zeroL σ clrR := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have z1 : ∀ r, r ∉ keepR → σ1.val r = 0 := fun r hr => by
    rw [hσ1, zeroL_val', if_pos ((mem_clrR r).2 hr)]
  have k1 : ∀ r, r ∈ keepR → σ1.val r = σ.val r := fun r hr => by
    rw [hσ1, zeroL_val', if_neg (fun h => (mem_clrR r).1 h hr)]
  have st1 : σ1.st = σ.st := by rw [hσ1]; exact zeroL_st' x σ clrR
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; exact zeroL_sh' x σ clrR
  have cl1 : σ1.cell = σ.cell := by rw [hσ1]; exact zeroL_cell' x σ clrR
  have a0 : σ1.val s0 = vN := (k1 s0 (by decide)).trans hN
  have a1 : σ1.val s1 = vM := (k1 s1 (by decide)).trans hM
  have a2 : σ1.val s2 = vE := (k1 s2 (by decide)).trans hE
  have a3 : σ1.val s3 = vT := (k1 s3 (by decide)).trans hT
  have a4 : σ1.val rA = V := (k1 rA (by decide)).trans hV
  have b0 := z1 NumsPh2.rN (by decide)
  have b1 := z1 NumsPh2.rM (by decide)
  have b2 := z1 NumsPh2.rE (by decide)
  have b3 := z1 NumsPh2.rT (by decide)
  have b4 := z1 NumsPh2.rV (by decide)
  have cN : vN ≤ cap := hN ▸ hb s0
  have cM : vM ≤ cap := hM ▸ hb s1
  have cE : vE ≤ cap := hE ▸ hb s2
  have cT : vT ≤ cap := hT ▸ hb s3
  have cV : V ≤ cap := hV ▸ hb rA
  have e2 := wmove_spec cap s0 NumsPh2.rN (by decide) vN σ1 a0 (by rw [a0]; exact cN) (by rw [a0, b0]; omega)
  rw [a0, b0, Nat.zero_add] at e2
  have e3 := wmove_spec cap s1 NumsPh2.rM (by decide) vM ((σ1.setv s0 0).setv NumsPh2.rN vN) (by vsimp [a1])
    (by vsimp [a1]; exact cM) (by vsimp [a1, b1]; exact cM)
  have f3a : ((σ1.setv s0 0).setv NumsPh2.rN vN).val s1 = vM := by vsimp [a1]
  have f3b : ((σ1.setv s0 0).setv NumsPh2.rN vN).val NumsPh2.rM = 0 := by vsimp [b1]
  rw [f3a, f3b, Nat.zero_add] at e3
  have e4 := wmove_spec cap s2 NumsPh2.rE (by decide) vE
    ((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM) (by vsimp [a2])
    (by vsimp [a2]; exact cE) (by vsimp [a2, b2]; exact cE)
  have f4a : ((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).val s2 = vE := by vsimp [a2]
  have f4b : ((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).val NumsPh2.rE = 0 := by
    vsimp [b2]
  rw [f4a, f4b, Nat.zero_add] at e4
  have e5 := wmove_spec cap s3 NumsPh2.rT (by decide) vT
    ((((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).setv s2 0).setv NumsPh2.rE vE)
    (by vsimp [a3]) (by vsimp [a3]; exact cT) (by vsimp [a3, b3]; exact cT)
  have f5a : ((((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).setv s2 0).setv NumsPh2.rE
      vE).val s3 = vT := by vsimp [a3]
  have f5b : ((((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).setv s2 0).setv NumsPh2.rE
      vE).val NumsPh2.rT = 0 := by vsimp [b3]
  rw [f5a, f5b, Nat.zero_add] at e5
  have e6 := wmove_spec cap rA NumsPh2.rV (by decide) V
    ((((((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).setv s2 0).setv NumsPh2.rE
      vE).setv s3 0).setv NumsPh2.rT vT) (by vsimp [a4]) (by vsimp [a4]; exact cV) (by vsimp [a4, b4]; exact cV)
  have f6a : ((((((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).setv s2 0).setv NumsPh2.rE
      vE).setv s3 0).setv NumsPh2.rT vT).val rA = V := by vsimp [a4]
  have f6b : ((((((((σ1.setv s0 0).setv NumsPh2.rN vN).setv s1 0).setv NumsPh2.rM vM).setv s2 0).setv NumsPh2.rE
      vE).setv s3 0).setv NumsPh2.rT vT).val NumsPh2.rV = 0 := by vsimp [b4]
  rw [f6a, f6b, Nat.zero_add] at e6
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6)))), by omega,
    by vsimp [], by vsimp [], by vsimp [], by vsimp [], by vsimp [], fun q q1 q2 q3 q4 q5 => ?_, ?_, ?_, ?_⟩
  · by_cases hk : q ∈ keepR
    · simp only [keepR, List.mem_cons, List.mem_nil_iff, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> vsimp []
    · have n0 : q ≠ s0 := fun h => hk (by rw [h]; decide)
      have n1 : q ≠ s1 := fun h => hk (by rw [h]; decide)
      have n2 : q ≠ s2 := fun h => hk (by rw [h]; decide)
      have n3 : q ≠ s3 := fun h => hk (by rw [h]; decide)
      have n4 : q ≠ rA := fun h => hk (by rw [h]; decide)
      simp [WState.setv_val, Function.update_apply, q1, q2, q3, q4, q5, n0, n1, n2, n3, n4, z1 q hk]
  · simp only [WState.setv_st]; exact st1
  · simp only [WState.setv_sh]; exact sh1
  · simp only [WState.setv_cell]; exact cl1

end NearCubicWires.WireExponent3_5.PrimT.NwB
