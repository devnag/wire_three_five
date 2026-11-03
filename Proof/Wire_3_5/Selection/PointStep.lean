import Proof.Wire_3_5.Selection.PointOps
import Proof.Wire_3_5.Selection.SortRound

/-! # C1.4: one position of the point routine (P3:1339-1344)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`"
(P3:1341-1342). The point routine walks the machine positions of one half. At a block position (machine block `t`,
index `i`) it counts `i + 1` (word `CI`), flags whether the error code of the block is `i + 1` (the flipped bit), reads
the position's signed weight, and, if the half's bit is set, adds `i + 1` into the block's syndrome (`SY`) and the
weight into the plain sum (`AC`); it adds the weight into the flipped sum (`AC'`) when the bit xor the flip is set.
At a free position it only reads the weight and updates both sums by the bit.

The routine's state `mkP σ0 …` records the heads (and their counters) of the half `X`, the errors word `U`, the coset
word `NS` and the weight table `WT`, the words `CI`, `SY`, `AC`, `AC'`, `WV` and the flags `OK`, `FL`, `SG`. Main
declarations: `posB`, **`posB_spec`**, `posF`, **`posF_spec`**. Paper quantity: a half's integer score (one term). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.UnionMachine.RegRat

variable {ns nr : ℕ}

/-- Clear a `0/1` flag. -/
def clrF (G : Fin nr) : WM ns nr := .ifr G (.dec G) .skip

theorem clrF_spec (cap : ℕ) (G : Fin nr) (σ : WState ns nr) (hG : σ.val G ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (clrF G) σ (σ.setv G 0) 2 := by
  unfold clrF
  by_cases h : σ.val G = 0
  · have e : σ.setv G 0 = σ := by rw [← h]; exact wsetv_same σ G
    rw [e]; exact WExec.mono (WExec.ifrF h (WExec.skip σ)) (by omega)
  · have hd := WExec.dec (cap := cap) G σ (by omega)
    have e : σ.val G - 1 = 0 := by omega
    rw [e] at hd
    exact WExec.ifrT h hd

section Step
variable (S : Fin 12 → Fin (ns + 1)) (hS : Function.Injective S) (Q : Fin 20 → Fin nr) (hQ : Function.Injective Q)
variable (s W : ℕ)


/-- **The point routine's state.** -/
def mkP (σ0 : WState ns nr) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) : WState ns nr :=
  ⟨fun j => if j = S 0 then pX else if j = S 3 then pW else if j = S 1 then pU else if j = S 2 then pN else σ0.sh j,
   fun j => if j = S 4 then frame (binary s ci) else if j = S 5 then frame (binary s sy) else
     if j = S 6 then frame (binary W a) else if j = S 7 then frame (binary W a') else
     if j = S 8 then frame (binary W wv) else σ0.st j,
   fun j => if j = Q 5 then pX else if j = Q 6 then pW else if j = Q 7 then pU else if j = Q 8 then pN else
     if j = Q 2 then ok else if j = Q 3 then fl else if j = Q 4 then sg else σ0.val j,
   σ0.cell⟩

end Step

section Trans
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
include hS hQ

theorem mkP_fwdX (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hp : pX < cap) :
    WExec cap (WM.fwdC (S 0) (Q 5)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 (pX + 1) pW pU pN ci sy a a' ok fl sg wv) 5 := by
  have h := wfwdC_spec cap (S 0) (Q 5) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (by simp [mkP]; exact hp)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl


theorem mkP_setv (r : Fin nr) (v : ℕ) (hr : ∀ i : Fin 20, i.val < 9 → r ≠ Q i)
    (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).setv r v =
      mkP S Q s W (σ0.setv r v) pX pW pU pN ci sy a a' ok fl sg wv := by
  have h2 := hr 2 (by decide); have h3 := hr 3 (by decide); have h4 := hr 4 (by decide)
  have h5 := hr 5 (by decide); have h6 := hr 6 (by decide); have h7 := hr 7 (by decide)
  have h8 := hr 8 (by decide)
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
    by_cases hj : j = r
    · subst hj; simp [h2, h3, h4, h5, h6, h7, h8]
    · simp only [hj, if_false]
  · rfl

theorem mkP_fwdU (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hp : pU < cap) :
    WExec cap (WM.fwdC (S 1) (Q 7)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW (pU + 1) pN ci sy a a' ok fl sg wv) 5 := by
  have h := wfwdC_spec cap (S 1) (Q 7) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]; exact hp)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl

theorem mkP_fwdN (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hp : pN < cap) :
    WExec cap (WM.fwdC (S 2) (Q 8)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU (pN + 1) ci sy a a' ok fl sg wv) 5 := by
  have h := wfwdC_spec cap (S 2) (Q 8) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]; exact hp)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl

/-- Return the heads of `X`, `WT`, `U`, `NS` by their counters. -/
def rewP (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  .seq (WM.rewind (S 0) (Q 5)) (.seq (WM.rewind (S 3) (Q 6)) (.seq (WM.rewind (S 1) (Q 7)) (WM.rewind (S 2) (Q 8))))

theorem mkP_rew (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hX : pX ≤ cap) (hW : pW ≤ cap) (hU : pU ≤ cap)
    (hN : pN ≤ cap) :
    WExec cap (rewP S Q) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 0 0 0 0 ci sy a a' ok fl sg wv) (5 * (pX + pW + pU + pN) + 7) := by
  have r1 := wrewind_spec cap (S 0) (Q 5) pX (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]) (by simp [mkP, hQ.eq_iff]; exact hX)
  have e1 : ((mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).setv (Q 5) 0).seth (S 0)
      ((mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).sh (S 0) - pX) =
      mkP S Q s W σ0 0 pW pU pN ci sy a a' ok fl sg wv := by
    apply WState.eq
    · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl
  rw [e1] at r1
  have r2 := wrewind_spec cap (S 3) (Q 6) pW (mkP S Q s W σ0 0 pW pU pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]) (by simp [mkP, hQ.eq_iff]; exact hW)
  have e2 : ((mkP S Q s W σ0 0 pW pU pN ci sy a a' ok fl sg wv).setv (Q 6) 0).seth (S 3)
      ((mkP S Q s W σ0 0 pW pU pN ci sy a a' ok fl sg wv).sh (S 3) - pW) =
      mkP S Q s W σ0 0 0 pU pN ci sy a a' ok fl sg wv := by
    apply WState.eq
    · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl
  rw [e2] at r2
  have r3 := wrewind_spec cap (S 1) (Q 7) pU (mkP S Q s W σ0 0 0 pU pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]) (by simp [mkP, hQ.eq_iff]; exact hU)
  have e3 : ((mkP S Q s W σ0 0 0 pU pN ci sy a a' ok fl sg wv).setv (Q 7) 0).seth (S 1)
      ((mkP S Q s W σ0 0 0 pU pN ci sy a a' ok fl sg wv).sh (S 1) - pU) =
      mkP S Q s W σ0 0 0 0 pN ci sy a a' ok fl sg wv := by
    apply WState.eq
    · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl
  rw [e3] at r3
  have r4 := wrewind_spec cap (S 2) (Q 8) pN (mkP S Q s W σ0 0 0 0 pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]) (by simp [mkP, hQ.eq_iff]; exact hN)
  have e4 : ((mkP S Q s W σ0 0 0 0 pN ci sy a a' ok fl sg wv).setv (Q 8) 0).seth (S 2)
      ((mkP S Q s W σ0 0 0 0 pN ci sy a a' ok fl sg wv).sh (S 2) - pN) =
      mkP S Q s W σ0 0 0 0 0 ci sy a a' ok fl sg wv := by
    apply WState.eq
    · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp_all [hS.eq_iff]
    · rfl
    · funext j; simp only [mkP, WState.setv_val, WState.seth_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl
  rw [e4] at r4
  unfold rewP
  exact WExec.mono (WExec.seq r1 (WExec.seq r2 (WExec.seq r3 r4))) (by omega)

end Trans

section Ops
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include hS hQ h0C h0Y h0A h0A' h0V h0F h0R

theorem mkP_numC (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    NumOn (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (S 4) s ci :=
  ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, h0C]⟩

theorem mkP_numY (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    NumOn (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (S 5) s sy :=
  ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, h0Y]⟩

theorem mkP_numA (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    NumOn (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (S 6) W a :=
  ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, h0A]⟩

theorem mkP_numA' (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    NumOn (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (S 7) W a' :=
  ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, h0A']⟩

theorem mkP_numV (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    NumOn (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (S 8) W wv :=
  ⟨by simp [mkP, hS.eq_iff], by simp [mkP, hS.eq_iff, h0V]⟩

theorem mkP_F (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).val (Q 0) = 0 := by simp [mkP, hQ.eq_iff, h0F]

theorem mkP_R (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).val (Q 1) = 0 := by simp [mkP, hQ.eq_iff, h0R]

/-- `CI := ci + 1`. -/
theorem mkP_incC (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hc : ci + 1 < 2 ^ s) (hcap : 2 * s + 1 ≤ cap) :
    WExec cap (incB (S 4) (S 5) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN (ci + 1) sy a a' ok fl sg wv) (41 * s + 7) := by
  have h := incB_spec cap s (hS.ne (by decide)) (hQ.ne (by decide)) _ ci sy
    (mkP_numC hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_numY hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv) hc hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `FL := [the word CI equals the segment of U at U's head]`. -/
theorem mkP_eqFlip (pX pW pN ci sy a a' ok sg wv : ℕ) (preU seg restU : List Bool) (hseg : seg.length = s)
    (hU : σ0.st (S 1) = preU ++ frameP seg ++ restU) (hcap : 2 * s + 1 ≤ cap) :
    WExec cap (eqAtF (S 4) (S 1) (Q 0) (Q 1) (Q 3))
      (mkP S Q s W σ0 pX pW preU.length pN ci sy a a' ok 0 sg wv)
      (mkP S Q s W σ0 pX pW preU.length pN ci sy a a' ok (decide (binary s ci = seg)).toNat sg wv)
      (s * 41 + 14) := by
  have h := eqAtF_spec cap (A := S 4) (B := S 1) (F := Q 0) (R := Q 1) (G := Q 3) (hS.ne (by decide))
    (hQ.ne (by decide)) (hQ.ne (by decide)) (mkP S Q s W σ0 pX pW preU.length pN ci sy a a' ok 0 sg wv) (binary s ci) seg preU restU
    (by simp [hseg]) (by simp [mkP, hS.eq_iff, frame_eq_frameP]) (by simp [mkP, hS.eq_iff, h0C])
    (by simp [mkP, hS.eq_iff, hU]) (by simp [mkP, hS.eq_iff])
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (by simp [mkP, hQ.eq_iff]) (by simp; omega)
  rw [binary_length] at h
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl

/-- Read the weight record at `WT`'s head: `SG := sign`, `WV := |w|`. -/
theorem mkP_rdW (pX pU pN ci sy a a' ok fl wv : ℕ) (preW : List Bool) (sgn : Bool) (m : ℕ) (postW : List Bool)
    (hT : σ0.st (S 3) = preW ++ (sgn :: frame (binary W m)) ++ postW) (hcap : preW.length + 2 * W + 2 ≤ cap) :
    WExec cap (rdW (S 3) (S 8) (Q 6) (Q 4) (Q 0) (Q 1))
      (mkP S Q s W σ0 pX preW.length pU pN ci sy a a' ok fl 0 wv)
      (mkP S Q s W σ0 pX (preW.length + 2 * W + 2) pU pN ci sy a a' ok fl sgn.toNat m) (54 * W + 23) := by
  have h := rdW_spec cap W (T := S 3) (V := S 8) (C := Q 6) (SG := Q 4) (F := Q 0) (R := Q 1)
    (hS.ne (by decide)) (hQ.ne (by decide)) (hQ.ne (by decide)) (hQ.ne (by decide))
    (hQ.ne (by decide)) (hQ.ne (by decide)) (hQ.ne (by decide))
    (mkP S Q s W σ0 pX preW.length pU pN ci sy a a' ok fl 0 wv) wv m sgn preW postW
    (mkP_numV hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (by simp [mkP, hS.eq_iff, hT]) (by simp [mkP, hS.eq_iff]) (by simp [mkP, hQ.eq_iff])
    (by simp [mkP, hQ.eq_iff])
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · funext j; simp only [mkP, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · funext j; simp only [mkP, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · funext j; simp only [mkP, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl

/-- `SY := SY xor CI`. -/
theorem mkP_xorY (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hcap : 2 * s + 1 ≤ cap) :
    WExec cap (xorB (S 5) (S 4) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci (sy ^^^ ci) a a' ok fl sg wv) (41 * s + 3) := by
  have h := xorB_spec cap s (hS.ne (by decide)) (hQ.ne (by decide)) _ sy ci
    (mkP_numY hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_numC hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `AC := AC + sv sgn m`. -/
theorem mkP_accA (pX pW pU pN ci sy a a' ok fl : ℕ) (sgn : Bool) (m : ℕ) (h1 : 0 ≤ (a : ℤ) + sv sgn m)
    (h2 : (a : ℤ) + sv sgn m < 2 ^ W) (ha : a < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (accW (S 6) (S 8) (Q 4) (Q 0) (Q 1))
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sgn.toNat m)
      (mkP S Q s W σ0 pX pW pU pN ci sy ((a : ℤ) + sv sgn m).toNat a' ok fl sgn.toNat m)
      (41 * W + 10) := by
  have h := accR_spec cap W (SG := Q 4) (hS.ne (by decide)) (hQ.ne (by decide))
    (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sgn.toNat m) a m sgn
    (mkP_numA hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_numV hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (by simp [mkP, hQ.eq_iff])
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) h1 h2 ha hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `AC' := AC' + sv sgn m`. -/
theorem mkP_accA' (pX pW pU pN ci sy a a' ok fl : ℕ) (sgn : Bool) (m : ℕ) (h1 : 0 ≤ (a' : ℤ) + sv sgn m)
    (h2 : (a' : ℤ) + sv sgn m < 2 ^ W) (ha : a' < 2 ^ W) (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1))
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sgn.toNat m)
      (mkP S Q s W σ0 pX pW pU pN ci sy a ((a' : ℤ) + sv sgn m).toNat ok fl sgn.toNat m)
      (41 * W + 10) := by
  have h := accR_spec cap W (SG := Q 4) (hS.ne (by decide)) (hQ.ne (by decide))
    (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sgn.toNat m) a' m sgn
    (mkP_numA' hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_numV hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (by simp [mkP, hQ.eq_iff])
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _) h1 h2 ha hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `FL := [the syndrome word equals the segment of NS at NS's head]`. -/
theorem mkP_eqSyn (pX pW pU ci sy a a' ok sg wv : ℕ) (preN seg restN : List Bool) (hseg : seg.length = s)
    (hN : σ0.st (S 2) = preN ++ frameP seg ++ restN) (hcap : 2 * s + 1 ≤ cap) :
    WExec cap (eqAtF (S 5) (S 2) (Q 0) (Q 1) (Q 3))
      (mkP S Q s W σ0 pX pW pU preN.length ci sy a a' ok 0 sg wv)
      (mkP S Q s W σ0 pX pW pU preN.length ci sy a a' ok (decide (binary s sy = seg)).toNat sg wv)
      (s * 41 + 14) := by
  have h := eqAtF_spec cap (A := S 5) (B := S 2) (F := Q 0) (R := Q 1) (G := Q 3) (hS.ne (by decide))
    (hQ.ne (by decide)) (hQ.ne (by decide)) (mkP S Q s W σ0 pX pW pU preN.length ci sy a a' ok 0 sg wv) (binary s sy)
    seg preN restN
    (by simp [hseg]) (by simp [mkP, hS.eq_iff, frame_eq_frameP]) (by simp [mkP, hS.eq_iff, h0Y])
    (by simp [mkP, hS.eq_iff, hN]) (by simp [mkP, hS.eq_iff])
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R _ _ _ _ _ _ _ _ _ _ _ _)
    (by simp [mkP, hQ.eq_iff]) (by simp; omega)
  rw [binary_length] at h
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl

/-- `OK := OK ∧ FL`, `FL := 0`. -/
theorem mkP_okAnd (pX pW pU pN ci sy a a' ok sg wv : ℕ) (e : Bool) (hok : ok ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (.ifr (Q 3) (.dec (Q 3)) (clrF (Q 2))) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok e.toNat sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' (if e then ok else 0) 0 sg wv) 3 := by
  cases e
  · have h := clrF_spec cap (Q 2) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 sg wv) (by simp [mkP, hQ.eq_iff]; exact hok)
      hcap
    have e1 : (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 sg wv).setv (Q 2) 0 =
        mkP S Q s W σ0 pX pW pU pN ci sy a a' 0 0 sg wv := by
      apply WState.eq
      · rfl
      · rfl
      · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
        split_ifs <;> simp_all [hQ.eq_iff]
      · rfl
    rw [e1] at h
    simp only [Bool.toNat_false, Bool.false_eq_true, if_false]
    exact WExec.mono (WExec.ifrF (by simp [mkP, hQ.eq_iff]) h) (by omega)
  · have h := WExec.dec (cap := cap) (Q 3) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 1 sg wv)
      (by simp [mkP, hQ.eq_iff]; omega)
    have e1 : (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 1 sg wv).setv (Q 3)
        ((mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 1 sg wv).val (Q 3) - 1) =
        mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 sg wv := by
      apply WState.eq
      · rfl
      · rfl
      · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
        split_ifs <;> simp_all [hQ.eq_iff]
      · rfl
    rw [e1] at h
    simp only [Bool.toNat_true, if_true]
    exact WExec.mono (WExec.ifrT (by simp [mkP, hQ.eq_iff]) h) (by omega)

/-- `SY := 0`. -/
theorem mkP_zeroY (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hcap : 2 * s + 1 ≤ cap) :
    WExec cap (zeroB (S 5) (S 4) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci 0 a a' ok fl sg wv) (41 * s + 3) := by
  have h := zeroB_spec cap s (hS.ne (by decide)) (hQ.ne (by decide)) _ sy ci
    (mkP_numY hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_numC hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `CI := 0`. -/
theorem mkP_zeroC (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hcap : 2 * s + 1 ≤ cap) :
    WExec cap (zeroB (S 4) (S 5) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN 0 sy a a' ok fl sg wv) (41 * s + 3) := by
  have h := zeroB_spec cap s (hS.ne (by decide)) (hQ.ne (by decide)) _ ci sy
    (mkP_numC hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_numY hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `AC := init` from the stream `S 9`. -/
theorem mkP_initA (init : ℕ) (hI : NumOn σ0 (S 9) W init) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (copyB (S 6) (S 9) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci sy init a' ok fl sg wv) (41 * W + 3) := by
  have h := copyB_spec cap W (A := S 6) (B := S 9) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide)) _ a init
    (mkP_numA hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    ⟨by simp [mkP, hS.eq_iff, hI.1], by simp [mkP, hS.eq_iff, hI.2]⟩
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `AC' := init` from the stream `S 9`. -/
theorem mkP_initA' (init : ℕ) (hI : NumOn σ0 (S 9) W init) (pX pW pU pN ci sy a a' ok fl sg wv : ℕ)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (copyB (S 7) (S 9) (Q 0) (Q 1)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci sy a init ok fl sg wv) (41 * W + 3) := by
  have h := copyB_spec cap W (A := S 7) (B := S 9) (F := Q 0) (R := Q 1) (hS.ne (by decide)) (hQ.ne (by decide)) _ a' init
    (mkP_numA' hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    ⟨by simp [mkP, hS.eq_iff, hI.1], by simp [mkP, hS.eq_iff, hI.2]⟩
    (mkP_F hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv)
    (mkP_R hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sg wv) hcap
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · funext j; simp only [mkP, WState.sets_st, Function.update_apply]
    split_ifs <;> simp_all [hS.eq_iff]
  · rfl
  · rfl

/-- `OK := ok + 1`. -/
theorem mkP_incOK (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hok : ok < cap) :
    WExec cap (.inc (Q 2)) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' (ok + 1) fl sg wv) 3 := by
  have h := WExec.inc (cap := cap) (Q 2) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
    (by simp [mkP, hQ.eq_iff]; exact hok)
  refine WExec.cast cap h ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
    split_ifs <;> simp_all [hQ.eq_iff]
  · rfl

/-- **The null point**: if `OK = 0`, `AC, AC' := init`; else `OK := 0`. -/
theorem mkP_null (init : ℕ) (hI : NumOn σ0 (S 9) W init) (pX pW pU pN ci sy a a' wv : ℕ) (okb : Bool)
    (hcap : 2 * W + 1 ≤ cap) :
    WExec cap (.ifr (Q 2) (.dec (Q 2)) (.seq (copyB (S 6) (S 9) (Q 0) (Q 1)) (copyB (S 7) (S 9) (Q 0) (Q 1))))
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' okb.toNat 0 0 wv)
      (mkP S Q s W σ0 pX pW pU pN ci sy (if okb then a else init) (if okb then a' else init) 0 0 0 wv) (82 * W + 10) := by
  cases okb
  · have y1 := mkP_initA hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R init hI pX pW pU pN ci sy a a' 0 0 0 wv hcap
    have y2 := mkP_initA' hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R init hI pX pW pU pN ci sy init a' 0 0 0 wv hcap
    simp only [Bool.toNat_false, Bool.false_eq_true, if_false]
    exact WExec.mono (WExec.ifrF (by simp [mkP, hQ.eq_iff]) (WExec.seq y1 y2)) (by omega)
  · have y := WExec.dec (cap := cap) (Q 2) (mkP S Q s W σ0 pX pW pU pN ci sy a a' 1 0 0 wv)
      (by simp [mkP, hQ.eq_iff]; omega)
    simp only [Bool.toNat_true, if_true]
    refine WExec.mono (WExec.ifrT (by simp [mkP, hQ.eq_iff]) (WExec.cast cap y ?_ le_rfl)) (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl

/-- Clear `FL` and `SG`. -/
theorem mkP_clr (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) (hfl : fl ≤ 1) (hsg : sg ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (.seq (clrF (Q 3)) (clrF (Q 4))) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv)
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 0 wv) 5 := by
  have h1 := clrF_spec cap (Q 3) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (by simp [mkP, hQ.eq_iff]; exact hfl)
    hcap
  have e1 : (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv).setv (Q 3) 0 = mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 sg wv := by
    apply WState.eq
    · rfl
    · rfl
    · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl
  rw [e1] at h1
  have h2 := clrF_spec cap (Q 4) (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 sg wv) (by simp [mkP, hQ.eq_iff]; exact hsg)
    hcap
  have e2 : (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 sg wv).setv (Q 4) 0 = mkP S Q s W σ0 pX pW pU pN ci sy a a' ok 0 0 wv := by
    apply WState.eq
    · rfl
    · rfl
    · funext j; simp only [mkP, WState.setv_val, Function.update_apply]
      split_ifs <;> simp_all [hQ.eq_iff]
    · rfl
  rw [e2] at h2
  exact WExec.seq h1 h2

end Ops

/-- **One block position.** -/
def posB (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  .seq (incB (S 4) (S 5) (Q 0) (Q 1)) (.seq (eqAtF (S 4) (S 1) (Q 0) (Q 1) (Q 3)) (.seq (WM.fwdC (S 0) (Q 5))
    (.seq (rdW (S 3) (S 8) (Q 6) (Q 4) (Q 0) (Q 1))
    (.seq (.ifs (S 0) (.seq (xorB (S 5) (S 4) (Q 0) (Q 1)) (accW (S 6) (S 8) (Q 4) (Q 0) (Q 1))) .skip)
    (.seq (.ifs (S 0) (.ifr (Q 3) .skip (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1)))
      (.ifr (Q 3) (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1)) .skip))
    (.seq (.seq (clrF (Q 3)) (clrF (Q 4))) (WM.fwdC (S 0) (Q 5))))))))

/-- **One free position**: no count, no flip, no syndrome. -/
def posF (S : Fin 12 → Fin (ns + 1)) (Q : Fin 20 → Fin nr) : WM ns nr :=
  .seq (WM.fwdC (S 0) (Q 5)) (.seq (rdW (S 3) (S 8) (Q 6) (Q 4) (Q 0) (Q 1))
    (.seq (.ifs (S 0) (.seq (accW (S 6) (S 8) (Q 4) (Q 0) (Q 1)) (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1))) .skip)
    (.seq (.seq (clrF (Q 3)) (clrF (Q 4))) (WM.fwdC (S 0) (Q 5)))))

section Pos
variable {S : Fin 12 → Fin (ns + 1)} (hS : Function.Injective S) {Q : Fin 20 → Fin nr} (hQ : Function.Injective Q)
variable (cap s W : ℕ) (σ0 : WState ns nr)
variable (h0C : σ0.sh (S 4) = 0) (h0Y : σ0.sh (S 5) = 0) (h0A : σ0.sh (S 6) = 0) (h0A' : σ0.sh (S 7) = 0)
  (h0V : σ0.sh (S 8) = 0) (h0F : σ0.val (Q 0) = 0) (h0R : σ0.val (Q 1) = 0)
include hS hQ h0C h0Y h0A h0A' h0V h0F h0R

theorem mkP_bitX (pX pW pU pN ci sy a a' ok fl sg wv : ℕ) :
    wbit (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sg wv) (S 0) = readTapeBit (σ0.st (S 0)) pX := by
  simp [wbit, mkP, hS.eq_iff]

/-- The plain update of a block position: the syndrome and the plain sum. -/
theorem mkP_br1 (pX pW pU pN ci sy a a' ok fl : ℕ) (sgn : Bool) (m : ℕ) (bit : Bool)
    (hbit : readTapeBit (σ0.st (S 0)) pX = bit)
    (h1 : bit = true → 0 ≤ (a : ℤ) + sv sgn m ∧ (a : ℤ) + sv sgn m < 2 ^ W)
    (ha : a < 2 ^ W) (hcap : 2 * s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap) :
    WExec cap (.ifs (S 0) (.seq (xorB (S 5) (S 4) (Q 0) (Q 1)) (accW (S 6) (S 8) (Q 4) (Q 0) (Q 1))) .skip)
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl sgn.toNat m)
      (mkP S Q s W σ0 pX pW pU pN ci (if bit then sy ^^^ ci else sy) (if bit then ((a : ℤ) + sv sgn m).toNat else a)
        a' ok fl sgn.toNat m) (82 * W + 41 * s + 16) := by
  have hb := mkP_bitX hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sgn.toNat m
  rw [hbit] at hb
  cases bit
  · simp only [Bool.false_eq_true, if_false]
    exact WExec.mono (WExec.ifsF hb (WExec.skip _)) (by omega)
  · simp only [if_true]
    obtain ⟨ha1, ha2⟩ := h1 rfl
    have x1 := mkP_xorY hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl sgn.toNat m hcap
    have x2 := mkP_accA hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci (sy ^^^ ci) a a' ok fl sgn m
      ha1 ha2 ha hcapW
    exact WExec.mono (WExec.ifsT hb (WExec.seq x1 x2)) (by omega)

/-- The flipped update of a block position. -/
theorem mkP_br2 (pX pW pU pN ci sy a a' ok : ℕ) (fl : Bool) (sgn : Bool) (m : ℕ) (bit : Bool)
    (hbit : readTapeBit (σ0.st (S 0)) pX = bit)
    (h1 : xor bit fl = true → 0 ≤ (a' : ℤ) + sv sgn m ∧ (a' : ℤ) + sv sgn m < 2 ^ W)
    (ha : a' < 2 ^ W) (hcapW : 2 * W + 1 ≤ cap) :
    WExec cap (.ifs (S 0) (.ifr (Q 3) .skip (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1)))
        (.ifr (Q 3) (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1)) .skip))
      (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl.toNat sgn.toNat m)
      (mkP S Q s W σ0 pX pW pU pN ci sy a (if xor bit fl then ((a' : ℤ) + sv sgn m).toNat else a') ok fl.toNat
        sgn.toNat m) (41 * W + 12) := by
  have hb := mkP_bitX hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok fl.toNat sgn.toNat m
  rw [hbit] at hb
  have hfl : (mkP S Q s W σ0 pX pW pU pN ci sy a a' ok fl.toNat sgn.toNat m).val (Q 3) = fl.toNat := by
    simp [mkP, hQ.eq_iff]
  cases bit <;> cases fl
  · simp only [Bool.xor_false, Bool.false_eq_true, if_false]
    exact WExec.mono (WExec.ifsF hb (WExec.ifrF (by rw [hfl]; rfl) (WExec.skip _))) (by omega)
  · simp only [Bool.false_xor, if_true]
    obtain ⟨a1, a2⟩ := h1 rfl
    have x := mkP_accA' hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok 1 sgn m a1 a2 ha hcapW
    exact WExec.mono (WExec.ifsF hb (WExec.ifrT (by rw [hfl]; decide) x)) (by omega)
  · simp only [Bool.xor_false, if_true]
    obtain ⟨a1, a2⟩ := h1 rfl
    have x := mkP_accA' hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX pW pU pN ci sy a a' ok 0 sgn m a1 a2 ha hcapW
    exact WExec.mono (WExec.ifsT hb (WExec.ifrF (by rw [hfl]; rfl) x)) (by omega)
  · simp only [Bool.xor_self, Bool.false_eq_true, if_false]
    exact WExec.mono (WExec.ifsT hb (WExec.ifrT (by rw [hfl]; decide) (WExec.skip _))) (by omega)

/-- **One block position** (machine position `p`, the head of `X` at its marker `pX`): `CI := ci + 1`; the flag of the
block's code against `ci + 1`; the record `(sgn, m)` read; if the bit is set, `SY ^= ci + 1` and `AC += sv sgn m`; if the
bit xor the flag is set, `AC' += sv sgn m`. -/
theorem posB_spec (pX pN ci sy a a' ok wv : ℕ) (preU seg restU preW postW : List Bool) (sgn : Bool) (m : ℕ)
    (bit : Bool) (hseg : seg.length = s) (hU : σ0.st (S 1) = preU ++ frameP seg ++ restU)
    (hT : σ0.st (S 3) = preW ++ (sgn :: frame (binary W m)) ++ postW)
    (hbit : readTapeBit (σ0.st (S 0)) (pX + 1) = bit) (hc : ci + 1 < 2 ^ s)
    (h1 : bit = true → 0 ≤ (a : ℤ) + sv sgn m ∧ (a : ℤ) + sv sgn m < 2 ^ W)
    (h2 : xor bit (decide (binary s (ci + 1) = seg)) = true → 0 ≤ (a' : ℤ) + sv sgn m ∧ (a' : ℤ) + sv sgn m < 2 ^ W)
    (ha : a < 2 ^ W) (ha' : a' < 2 ^ W) (hcap : 2 * s + 1 ≤ cap) (hcapW : 2 * W + 1 ≤ cap)
    (hcapT : preW.length + 2 * W + 2 ≤ cap) (hcapX : pX + 2 ≤ cap) :
    WExec cap (posB S Q) (mkP S Q s W σ0 pX preW.length preU.length pN ci sy a a' ok 0 0 wv)
      (mkP S Q s W σ0 (pX + 2) (preW.length + 2 * W + 2) preU.length pN (ci + 1)
        (if bit then sy ^^^ (ci + 1) else sy) (if bit then ((a : ℤ) + sv sgn m).toNat else a)
        (if xor bit (decide (binary s (ci + 1) = seg)) then ((a' : ℤ) + sv sgn m).toNat else a') ok 0 0 m)
      (180 * W + 125 * s + 110) := by
  set fl := decide (binary s (ci + 1) = seg) with hfl
  have x1 := mkP_incC hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX preW.length preU.length pN ci sy a a' ok 0 0 wv
    hc hcap
  have x2 := mkP_eqFlip hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R pX preW.length pN (ci + 1) sy a a' ok 0 wv
    preU seg restU hseg hU hcap
  rw [← hfl] at x2
  have x3 := mkP_fwdX hS hQ cap s W σ0 pX preW.length preU.length pN (ci + 1) sy a a' ok fl.toNat 0 wv (by omega)
  have x4 := mkP_rdW hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) preU.length pN (ci + 1) sy a a' ok
    fl.toNat wv preW sgn m postW hT hcapT
  have x5 := mkP_br1 hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) preU.length pN
    (ci + 1) sy a a' ok fl.toNat sgn m bit hbit h1 ha hcap hcapW
  have x6 := mkP_br2 hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) preU.length pN
    (ci + 1) (if bit then sy ^^^ (ci + 1) else sy) (if bit then ((a : ℤ) + sv sgn m).toNat else a) a' ok fl sgn m bit
    hbit h2 ha' hcapW
  have x7 := mkP_clr hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) preU.length pN
    (ci + 1) (if bit then sy ^^^ (ci + 1) else sy) (if bit then ((a : ℤ) + sv sgn m).toNat else a)
    (if xor bit fl then ((a' : ℤ) + sv sgn m).toNat else a') ok fl.toNat sgn.toNat m
    (by cases fl <;> simp) (by cases sgn <;> simp) (by omega)
  have x8 := mkP_fwdX hS hQ cap s W σ0 (pX + 1) (preW.length + 2 * W + 2) preU.length pN (ci + 1)
    (if bit then sy ^^^ (ci + 1) else sy) (if bit then ((a : ℤ) + sv sgn m).toNat else a)
    (if xor bit fl then ((a' : ℤ) + sv sgn m).toNat else a') ok 0 0 m (by omega)
  unfold posB
  exact WExec.mono (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 (WExec.seq x5 (WExec.seq x6
    (WExec.seq x7 x8))))))) (by omega)

/-- **One free position**: the record `(sgn, m)` read; if the bit is set, both sums gain `sv sgn m`. -/
theorem posF_spec (pX pU pN ci sy a a' ok wv : ℕ) (preW postW : List Bool) (sgn : Bool) (m : ℕ) (bit : Bool)
    (hT : σ0.st (S 3) = preW ++ (sgn :: frame (binary W m)) ++ postW)
    (hbit : readTapeBit (σ0.st (S 0)) (pX + 1) = bit)
    (h1 : bit = true → 0 ≤ (a : ℤ) + sv sgn m ∧ (a : ℤ) + sv sgn m < 2 ^ W)
    (h2 : bit = true → 0 ≤ (a' : ℤ) + sv sgn m ∧ (a' : ℤ) + sv sgn m < 2 ^ W)
    (ha : a < 2 ^ W) (ha' : a' < 2 ^ W) (hcapW : 2 * W + 1 ≤ cap)
    (hcapT : preW.length + 2 * W + 2 ≤ cap) (hcapX : pX + 2 ≤ cap) :
    WExec cap (posF S Q) (mkP S Q s W σ0 pX preW.length pU pN ci sy a a' ok 0 0 wv)
      (mkP S Q s W σ0 (pX + 2) (preW.length + 2 * W + 2) pU pN ci sy
        (if bit then ((a : ℤ) + sv sgn m).toNat else a) (if bit then ((a' : ℤ) + sv sgn m).toNat else a') ok 0 0 m)
      (140 * W + 70) := by
  have x1 := mkP_fwdX hS hQ cap s W σ0 pX preW.length pU pN ci sy a a' ok 0 0 wv (by omega)
  have x2 := mkP_rdW hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) pU pN ci sy a a' ok 0 wv preW sgn m postW
    hT hcapT
  have hb := mkP_bitX hS hQ s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) pU pN ci sy a a' ok
    0 sgn.toNat m
  rw [hbit] at hb
  have x3 : WExec cap (.ifs (S 0) (.seq (accW (S 6) (S 8) (Q 4) (Q 0) (Q 1)) (accW (S 7) (S 8) (Q 4) (Q 0) (Q 1))) .skip)
      (mkP S Q s W σ0 (pX + 1) (preW.length + 2 * W + 2) pU pN ci sy a a' ok 0 sgn.toNat m)
      (mkP S Q s W σ0 (pX + 1) (preW.length + 2 * W + 2) pU pN ci sy
        (if bit then ((a : ℤ) + sv sgn m).toNat else a) (if bit then ((a' : ℤ) + sv sgn m).toNat else a') ok 0
        sgn.toNat m) (82 * W + 22) := by
    cases bit
    · simp only [Bool.false_eq_true, if_false]
      exact WExec.mono (WExec.ifsF hb (WExec.skip _)) (by omega)
    · simp only [if_true]
      obtain ⟨a1, a2⟩ := h1 rfl
      obtain ⟨b1, b2⟩ := h2 rfl
      have y1 := mkP_accA hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) pU pN ci sy
        a a' ok 0 sgn m a1 a2 ha hcapW
      have y2 := mkP_accA' hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) pU pN ci
        sy ((a : ℤ) + sv sgn m).toNat a' ok 0 sgn m b1 b2 ha' hcapW
      exact WExec.mono (WExec.ifsT hb (WExec.seq y1 y2)) (by omega)
  have x4 := mkP_clr hS hQ cap s W σ0 h0C h0Y h0A h0A' h0V h0F h0R (pX + 1) (preW.length + 2 * W + 2) pU pN ci sy
    (if bit then ((a : ℤ) + sv sgn m).toNat else a) (if bit then ((a' : ℤ) + sv sgn m).toNat else a') ok 0 sgn.toNat m
    (by omega) (by cases sgn <;> simp) (by omega)
  have x5 := mkP_fwdX hS hQ cap s W σ0 (pX + 1) (preW.length + 2 * W + 2) pU pN ci sy
    (if bit then ((a : ℤ) + sv sgn m).toNat else a) (if bit then ((a' : ℤ) + sv sgn m).toNat else a') ok 0 0 m
    (by omega)
  unfold posF
  exact WExec.mono (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 x5)))) (by omega)

end Pos

end NearCubicWires.WireExponent3_5.SelectionMachine.Point
