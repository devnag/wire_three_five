import Proof.Wire_3_5.Primitive.SeedFix.NwB2
import Proof.Wire_3_5.UnionMachine.NumsC1

/-! # NW phase (b), part 4: the register moves around the decode's numbers

Phase (b)'s registers `rN, rM, rE, rT, rV` (`505 … 509`) lie in the decode's `H` block (`472 … 511`), which the pre-dock program needs at `0`; so (b) first moves `n`, the mode bit, `e`, `T_f` to `450 … 453` (`saveW`), and the
decode's star numbers `k_h`, `f_e·L` to `454`, `455` before the THR cap's program reuses the star block (`keepW`,
`clearL` of `SGb`); after the cap, `Hb 0 := |carriers|`, `Hb 1 := cap_T` (`setHbW`), the pre-dock program's inputs.

* `s0 … s3`, `sKH`, `sFL`; **`save_spec`**, **`keep_spec`**, **`setHb_spec`**.

Paper quantities of the main types: the call's `n`, `k_h`, `f_e·L`, `|carriers|`, `cap_T` (P3:1188-1189, 3425-3430). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

def s0 : Fin LNR := ⟨450, by decide⟩
def s1 : Fin LNR := ⟨451, by decide⟩
def s2 : Fin LNR := ⟨452, by decide⟩
def s3 : Fin LNR := ⟨453, by decide⟩
def sKH : Fin LNR := ⟨454, by decide⟩
def sFL : Fin LNR := ⟨455, by decide⟩

variable (cap : ℕ) (x : ℕ)

/-- **Save** `n`, the mode bit, `e`, `T_f`. -/
def saveW : WM (LNS x) LNR :=
  .seq (WM.move NumsPh2.rN s0) (.seq (WM.move NumsPh2.rM s1) (.seq (WM.move NumsPh2.rE s2) (WM.move NumsPh2.rT s3)))

theorem save_spec (σ : WState (LNS x) LNR) (vN vM vE vT : ℕ) (hN : σ.val NumsPh2.rN = vN)
    (hM : σ.val NumsPh2.rM = vM) (hE : σ.val NumsPh2.rE = vE) (hT : σ.val NumsPh2.rT = vT)
    (z0 : σ.val s0 = 0) (z1 : σ.val s1 = 0) (z2 : σ.val s2 = 0) (z3 : σ.val s3 = 0)
    (cN : vN ≤ cap) (cM : vM ≤ cap) (cE : vE ≤ cap) (cT : vT ≤ cap) :
    ∃ τ c, WExec cap (saveW x) σ τ c ∧ c ≤ 7 * (vN + vM + vE + vT) + 8 ∧
      τ.val NumsPh2.rN = 0 ∧ τ.val NumsPh2.rM = 0 ∧ τ.val NumsPh2.rE = 0 ∧ τ.val NumsPh2.rT = 0 ∧
      τ.val s0 = vN ∧ τ.val s1 = vM ∧ τ.val s2 = vE ∧ τ.val s3 = vT ∧
      (∀ r, r ≠ NumsPh2.rN → r ≠ NumsPh2.rM → r ≠ NumsPh2.rE → r ≠ NumsPh2.rT → r ≠ s0 → r ≠ s1 → r ≠ s2 →
        r ≠ s3 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have q1 : NumsPh2.rM ≠ s0 := by decide
  have q2 : NumsPh2.rM ≠ NumsPh2.rN := by decide
  have q3 : s1 ≠ s0 := by decide
  have q4 : s1 ≠ NumsPh2.rN := by decide
  have q5 : NumsPh2.rE ≠ s0 := by decide
  have q6 : NumsPh2.rE ≠ NumsPh2.rN := by decide
  have q7 : NumsPh2.rE ≠ s1 := by decide
  have q8 : NumsPh2.rE ≠ NumsPh2.rM := by decide
  have q9 : s2 ≠ s0 := by decide
  have q10 : s2 ≠ NumsPh2.rN := by decide
  have q11 : s2 ≠ s1 := by decide
  have q12 : s2 ≠ NumsPh2.rM := by decide
  have q13 : NumsPh2.rT ≠ s0 := by decide
  have q14 : NumsPh2.rT ≠ NumsPh2.rN := by decide
  have q15 : NumsPh2.rT ≠ s1 := by decide
  have q16 : NumsPh2.rT ≠ NumsPh2.rM := by decide
  have q17 : NumsPh2.rT ≠ s2 := by decide
  have q18 : NumsPh2.rT ≠ NumsPh2.rE := by decide
  have q19 : s3 ≠ s0 := by decide
  have q20 : s3 ≠ NumsPh2.rN := by decide
  have q21 : s3 ≠ s1 := by decide
  have q22 : s3 ≠ NumsPh2.rM := by decide
  have q23 : s3 ≠ s2 := by decide
  have q24 : s3 ≠ NumsPh2.rE := by decide
  have p1 : NumsPh2.rN ≠ s0 := by decide
  have p2 : NumsPh2.rM ≠ s1 := by decide
  have p3 : NumsPh2.rE ≠ s2 := by decide
  have p4 : NumsPh2.rT ≠ s3 := by decide
  have e1 := wmove_spec cap NumsPh2.rN s0 (by decide) vN σ hN (by omega) (by omega)
  obtain ⟨σ1, g1⟩ : ∃ y, y = (σ.setv NumsPh2.rN 0).setv s0 (σ.val s0 + σ.val NumsPh2.rN) := ⟨_, rfl⟩
  rw [← g1] at e1
  have e2 := wmove_spec cap NumsPh2.rM s1 (by decide) vM σ1 (by rw [g1]; simp [Function.update_apply, hM, q1, q2, q3, q4])
    (by rw [g1]; simp [Function.update_apply, hM, q1, q2, q3, q4]; omega) (by rw [g1]; simp [Function.update_apply, hM, z1, q1, q2, q3, q4]; omega)
  obtain ⟨σ2, g2⟩ : ∃ y, y = (σ1.setv NumsPh2.rM 0).setv s1 (σ1.val s1 + σ1.val NumsPh2.rM) := ⟨_, rfl⟩
  rw [← g2] at e2
  have e3 := wmove_spec cap NumsPh2.rE s2 (by decide) vE σ2 (by rw [g2, g1]; simp [Function.update_apply, hE, q5, q6, q7, q8, q9, q10, q11, q12])
    (by rw [g2, g1]; simp [Function.update_apply, hE, q5, q6, q7, q8, q9, q10, q11, q12]; omega)
    (by rw [g2, g1]; simp [Function.update_apply, hE, z2, q5, q6, q7, q8, q9, q10, q11, q12]; omega)
  obtain ⟨σ3, g3⟩ : ∃ y, y = (σ2.setv NumsPh2.rE 0).setv s2 (σ2.val s2 + σ2.val NumsPh2.rE) := ⟨_, rfl⟩
  rw [← g3] at e3
  have e4 := wmove_spec cap NumsPh2.rT s3 (by decide) vT σ3 (by rw [g3, g2, g1]; simp [Function.update_apply, hT, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24])
    (by rw [g3, g2, g1]; simp [Function.update_apply, hT, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24]; omega)
    (by rw [g3, g2, g1]; simp [Function.update_apply, hT, z3, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24]; omega)
  obtain ⟨σ4, g4⟩ : ∃ y, y = (σ3.setv NumsPh2.rT 0).setv s3 (σ3.val s3 + σ3.val NumsPh2.rT) := ⟨_, rfl⟩
  rw [← g4] at e4
  refine ⟨σ4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega, ?_⟩
  subst g4 g3 g2 g1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  all_goals try (simp only [WState.setv_val, Function.update_apply, hN, hM, hE, hT, z0, z1, z2, z3, p1, p2, p3, p4,
        Ne.symm p1, Ne.symm p2, Ne.symm p3, Ne.symm p4, q1, q2, q3, q4, q5, q6, q7,
        q8, q9, q10, q11, q12, q13, q14, q15, q16, q17, q18, q19, q20, q21, q22, q23, q24, Ne.symm q1, Ne.symm q2,
        Ne.symm q3, Ne.symm q4, Ne.symm q5, Ne.symm q6, Ne.symm q7, Ne.symm q8, Ne.symm q9, Ne.symm q10, Ne.symm q11,
        Ne.symm q12, Ne.symm q13, Ne.symm q14, Ne.symm q15, Ne.symm q16, Ne.symm q17, Ne.symm q18, Ne.symm q19,
        Ne.symm q20, Ne.symm q21, Ne.symm q22, Ne.symm q23, Ne.symm q24, if_true, if_false, Nat.zero_add]; done)
  intro r a1 a2 a3 a4 a5 a6 a7 a8
  simp only [WState.setv_val, Function.update_apply, a1, a2, a3, a4, a5, a6, a7, a8, if_false]

/-- **Keep** `k_h`, `f_e·L` (from the star block `SGb 8`, `SGb 10`). -/
def keepW : WM (LNS x) LNR := .seq (WM.move (SGb 8) sKH) (WM.move (SGb 10) sFL)

theorem keep_spec (σ : WState (LNS x) LNR) (vK vF : ℕ) (hK : σ.val (SGb 8) = vK) (hF : σ.val (SGb 10) = vF)
    (zK : σ.val sKH = 0) (zF : σ.val sFL = 0) (cK : vK ≤ cap) (cF : vF ≤ cap) :
    ∃ τ c, WExec cap (keepW x) σ τ c ∧ c ≤ 7 * (vK + vF) + 4 ∧ τ.val sKH = vK ∧ τ.val sFL = vF ∧
      (∀ r, r ≠ SGb 8 → r ≠ SGb 10 → r ≠ sKH → r ≠ sFL → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  have d1 : SGb 8 ≠ sKH := fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [sKH] at this
  have d2 : SGb 10 ≠ sFL := fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [sFL] at this
  have d3 : SGb 10 ≠ SGb 8 := fun e => by have := congrArg Fin.val e; rw [SGb_val, SGb_val] at this; simp at this
  have d4 : SGb 10 ≠ sKH := fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [sKH] at this
  have d5 : sFL ≠ sKH := by decide
  have d6 : sFL ≠ SGb 8 := fun e => by have := congrArg Fin.val e; rw [SGb_val] at this; simp [sFL] at this
  have e1 := wmove_spec cap (SGb 8) sKH d1 vK σ hK (by omega) (by omega)
  have e2 := wmove_spec cap (SGb 10) sFL d2 vF ((σ.setv (SGb 8) 0).setv sKH (σ.val sKH + σ.val (SGb 8)))
    (by simp [Function.update_apply, d3, d4, hF]) (by simp [Function.update_apply, d3, d4, hF]; omega)
    (by simp [Function.update_apply, d3, d4, d5, d6, hF, zF]; omega)
  refine ⟨_, _, WExec.seq e1 e2, by omega, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [Function.update_apply, Ne.symm d5, d5, Ne.symm d4, hK, zK]
  · simp [Function.update_apply, hF, zF, d3, d4, d5, d6]
  · intro r a1 a2 a3 a4; simp [Function.update_apply, a1, a2, a3, a4]

/-- **The pre-dock inputs**: `Hb 0 := |carriers|` (from `dNC`), `Hb 1 := cap_T` (from `Hb 13`). -/
def setHbW : WM (LNS x) LNR :=
  .seq (WM.clear (Hb 0)) (.seq (WM.clear (Hb 1)) (.seq (FinalPass.Hash4.wcopyR dNC (Hb 0) rTm)
    (FinalPass.Hash4.wcopyR (Hb 13) (Hb 1) rTm)))

theorem setHb_spec (σ : WState (LNS x) LNR) (vC vT : ℕ) (hC : σ.val dNC = vC) (hT : σ.val (Hb 13) = vT)
    (zT : σ.val rTm = 0) (hb : ∀ r, σ.val r ≤ cap) :
    ∃ τ c, WExec cap (setHbW x) σ τ c ∧ c ≤ 6 * cap + 6 + 2 * UnaryPow.sq cap ∧ τ.val (Hb 0) = vC ∧
      τ.val (Hb 1) = vT ∧ (∀ r, r ≠ Hb 0 → r ≠ Hb 1 → τ.val r = σ.val r) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      τ.cell = σ.cell := by
  have d01 : Hb 0 ≠ Hb 1 := Hb.injective.ne (by decide)
  have dC0 : dNC ≠ Hb 0 := fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dNC] at this
  have dC1 : dNC ≠ Hb 1 := fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [dNC] at this
  have d13_0 : Hb 13 ≠ Hb 0 := Hb.injective.ne (by decide)
  have d13_1 : Hb 13 ≠ Hb 1 := Hb.injective.ne (by decide)
  have dT0 : rTm ≠ Hb 0 := fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [rTm] at this
  have dT1 : rTm ≠ Hb 1 := fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [rTm] at this
  have dCT : dNC ≠ rTm := by decide
  have d13T : Hb 13 ≠ rTm := fun e => by have := congrArg Fin.val e; rw [Hb_val] at this; simp [rTm] at this
  have hl := UnaryPow.lin_le_sq cap
  have e1 := wclear_spec cap (Hb 0) (σ.val (Hb 0)) σ rfl (hb _)
  have e2 := wclear_spec cap (Hb 1) (σ.val (Hb 1)) (σ.setv (Hb 0) 0) (by simp [Function.update_apply, Ne.symm d01])
    (by simp [Function.update_apply, Ne.symm d01]; exact hb _)
  have e3 := SparseNum.copy1 cap dNC (Hb 0) rTm dC0 dCT (Ne.symm dT0) vC ((σ.setv (Hb 0) 0).setv (Hb 1) 0)
    (by simp [Function.update_apply, dC0, dC1, hC]) (by simp [Function.update_apply, d01])
    (by simp [Function.update_apply, dT0, dT1, zT]) (by rw [← hC]; exact hb _)
  have e4 := SparseNum.copy1 cap (Hb 13) (Hb 1) rTm d13_1 d13T (Ne.symm dT1) vT
    (((σ.setv (Hb 0) 0).setv (Hb 1) 0).setv (Hb 0) vC)
    (by simp [Function.update_apply, d13_0, d13_1, hT]) (by simp [Function.update_apply, Ne.symm d01])
    (by simp [Function.update_apply, dT0, dT1, zT]) (by rw [← hT]; exact hb _)
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · have a0 := hb (Hb 0); have a1 := hb (Hb 1); omega
  · simp [Function.update_apply, d01]
  · simp
  · intro r a0 a1; simp [Function.update_apply, a0, a1]

end NearCubicWires.WireExponent3_5.PrimT.NwB
