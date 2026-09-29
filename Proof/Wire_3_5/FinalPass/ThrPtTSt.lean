import Proof.Wire_3_5.FinalPass.ThrPtTapeL

/-! # S2 (THR per point), part 14: the evaluator's working states (P3:3170-3178)

Between the stages, the evaluator's layout differs from a base state `σB` (the call words, the point, the constants)
only in a few places: the scratch streams `10 … 16`, the heads of the primes `8`, the row word `13` and the reports
`16`, and the working registers (the accumulator `0`, `g`'s index `6`, the prime `7`, the digit `53`, the report
`82`, stage 8's answer `92`, the loop counters `109 … 116`). `TSt` records exactly these; `TSt.w σB t` is the layout
state. The update lemmas (`tw_sets_*`, `tw_setv_*`, `tw_seth_*`) turn the stages' exact results into record updates,
the read lemmas (`tw_st_*`, `tw_val_*`, `tw_sh_*`) give every stage's hypotheses. Paper quantity: none beyond the
machine model (the per-point evaluator's layout). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- The evaluator's working state. -/
structure TSt where
  acc : ℕ
  gi : ℕ
  p : ℕ
  d : ℕ
  r82 : ℕ
  w92 : ℕ
  gRem : ℕ
  prH : ℕ
  dRem : ℕ
  rH : ℕ
  tmp : ℕ
  kS : ℕ
  rS : ℕ
  rwH : ℕ
  hPr : ℕ
  hRw : ℕ
  hRep : ℕ
  pos : List Bool
  neg : List Bool
  x : List Bool
  rw : List Bool
  z : List Bool
  ss : List Bool
  rep : List Bool

/-- The working registers: the accumulator, `g`'s index, the prime, the digit, the report, stage 8's answer, the loop
counters. -/
def tReg (t : TSt) (q : Fin 118) (dflt : ℕ) : ℕ :=
  if q = 0 then t.acc else if q = 6 then t.gi else if q = 7 then t.p else if q = 53 then t.d
  else if q = 82 then t.r82 else if q = 92 then t.w92 else if q = 109 then t.gRem else if q = 110 then t.prH
  else if q = 111 then t.dRem else if q = 112 then t.rH else if q = 113 then t.tmp else if q = 114 then t.kS
  else if q = 115 then t.rS else if q = 116 then t.rwH else dflt

/-- The working streams: the scratch `10 … 16`. -/
def tStr (t : TSt) (j : Fin 17) (dflt : List Bool) : List Bool :=
  if j = 10 then t.pos else if j = 11 then t.neg else if j = 12 then t.x else if j = 13 then t.rw
  else if j = 14 then t.z else if j = 15 then t.ss else if j = 16 then t.rep else dflt

/-- The working heads: the primes, the row word, the reports. -/
def tHd (t : TSt) (j : Fin 17) (dflt : ℕ) : ℕ :=
  if j = 8 then t.hPr else if j = 13 then t.hRw else if j = 16 then t.hRep else dflt

/-- **The layout at a working state** over the base `σB` (the cell `false`). -/
def TSt.w (σB : WState 16 118) (t : TSt) : WState 16 118 :=
  ⟨fun j => tHd t j (σB.sh j), fun j => tStr t j (σB.st j), fun q => tReg t q (σB.val q), false⟩

theorem tw_eq {σB : WState 16 118} {t t' : TSt} (h : t = t') : t.w σB = t'.w σB := congrArg (TSt.w σB) h

section Lemmas
variable (σB : WState 16 118) (t : TSt)

@[simp] theorem tw_cell : (t.w σB).cell = false := rfl


@[simp] theorem tw_st_pos : (t.w σB).st 10 = t.pos := by simp [TSt.w, tStr]
@[simp] theorem tw_st_neg : (t.w σB).st 11 = t.neg := by simp [TSt.w, tStr]
@[simp] theorem tw_st_x : (t.w σB).st 12 = t.x := by simp [TSt.w, tStr]
@[simp] theorem tw_st_rw : (t.w σB).st 13 = t.rw := by simp [TSt.w, tStr]
@[simp] theorem tw_st_z : (t.w σB).st 14 = t.z := by simp [TSt.w, tStr]
@[simp] theorem tw_st_ss : (t.w σB).st 15 = t.ss := by simp [TSt.w, tStr]
@[simp] theorem tw_st_rep : (t.w σB).st 16 = t.rep := by simp [TSt.w, tStr]
@[simp] theorem tw_sh_hPr : (t.w σB).sh 8 = t.hPr := by simp [TSt.w, tHd]
@[simp] theorem tw_sh_hRw : (t.w σB).sh 13 = t.hRw := by simp [TSt.w, tHd]
@[simp] theorem tw_sh_hRep : (t.w σB).sh 16 = t.hRep := by simp [TSt.w, tHd]
@[simp] theorem tw_val_acc : (t.w σB).val 0 = t.acc := by simp [TSt.w, tReg]
@[simp] theorem tw_val_gi : (t.w σB).val 6 = t.gi := by simp [TSt.w, tReg]
@[simp] theorem tw_val_p : (t.w σB).val 7 = t.p := by simp [TSt.w, tReg]
@[simp] theorem tw_val_d : (t.w σB).val 53 = t.d := by simp [TSt.w, tReg]
@[simp] theorem tw_val_r82 : (t.w σB).val 82 = t.r82 := by simp [TSt.w, tReg]
@[simp] theorem tw_val_w92 : (t.w σB).val 92 = t.w92 := by simp [TSt.w, tReg]
@[simp] theorem tw_val_gRem : (t.w σB).val 109 = t.gRem := by simp [TSt.w, tReg]
@[simp] theorem tw_val_prH : (t.w σB).val 110 = t.prH := by simp [TSt.w, tReg]
@[simp] theorem tw_val_dRem : (t.w σB).val 111 = t.dRem := by simp [TSt.w, tReg]
@[simp] theorem tw_val_rH : (t.w σB).val 112 = t.rH := by simp [TSt.w, tReg]
@[simp] theorem tw_val_tmp : (t.w σB).val 113 = t.tmp := by simp [TSt.w, tReg]
@[simp] theorem tw_val_kS : (t.w σB).val 114 = t.kS := by simp [TSt.w, tReg]
@[simp] theorem tw_val_rS : (t.w σB).val 115 = t.rS := by simp [TSt.w, tReg]
@[simp] theorem tw_val_rwH : (t.w σB).val 116 = t.rwH := by simp [TSt.w, tReg]

theorem tw_sets_pos (l : List Bool) : (t.w σB).sets 10 l = { t with pos := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 10
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_sets_neg (l : List Bool) : (t.w σB).sets 11 l = { t with neg := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 11
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_sets_x (l : List Bool) : (t.w σB).sets 12 l = { t with x := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 12
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_sets_rw (l : List Bool) : (t.w σB).sets 13 l = { t with rw := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 13
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_sets_z (l : List Bool) : (t.w σB).sets 14 l = { t with z := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 14
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_sets_ss (l : List Bool) : (t.w σB).sets 15 l = { t with ss := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 15
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_sets_rep (l : List Bool) : (t.w σB).sets 16 l = { t with rep := l }.w σB := by
  apply WState.eq
  · rfl
  · funext i
    by_cases hi : i = 16
    · subst hi; simp [TSt.w, tStr]
    · simp [TSt.w, tStr, Function.update_of_ne hi, hi]
  · rfl
  · rfl
theorem tw_seth_hPr (v : ℕ) : (t.w σB).seth 8 v = { t with hPr := v }.w σB := by
  apply WState.eq
  · funext i
    by_cases hi : i = 8
    · subst hi; simp [TSt.w, tHd]
    · simp [TSt.w, tHd, Function.update_of_ne hi, hi]
  · rfl
  · rfl
  · rfl
theorem tw_seth_hRw (v : ℕ) : (t.w σB).seth 13 v = { t with hRw := v }.w σB := by
  apply WState.eq
  · funext i
    by_cases hi : i = 13
    · subst hi; simp [TSt.w, tHd]
    · simp [TSt.w, tHd, Function.update_of_ne hi, hi]
  · rfl
  · rfl
  · rfl
theorem tw_seth_hRep (v : ℕ) : (t.w σB).seth 16 v = { t with hRep := v }.w σB := by
  apply WState.eq
  · funext i
    by_cases hi : i = 16
    · subst hi; simp [TSt.w, tHd]
    · simp [TSt.w, tHd, Function.update_of_ne hi, hi]
  · rfl
  · rfl
  · rfl
theorem tw_setv_acc (v : ℕ) : (t.w σB).setv 0 v = { t with acc := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 0
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_gi (v : ℕ) : (t.w σB).setv 6 v = { t with gi := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 6
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_p (v : ℕ) : (t.w σB).setv 7 v = { t with p := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 7
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_d (v : ℕ) : (t.w σB).setv 53 v = { t with d := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 53
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_r82 (v : ℕ) : (t.w σB).setv 82 v = { t with r82 := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 82
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_w92 (v : ℕ) : (t.w σB).setv 92 v = { t with w92 := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 92
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_gRem (v : ℕ) : (t.w σB).setv 109 v = { t with gRem := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 109
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_prH (v : ℕ) : (t.w σB).setv 110 v = { t with prH := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 110
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_dRem (v : ℕ) : (t.w σB).setv 111 v = { t with dRem := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 111
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_rH (v : ℕ) : (t.w σB).setv 112 v = { t with rH := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 112
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_kS (v : ℕ) : (t.w σB).setv 114 v = { t with kS := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 114
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_rS (v : ℕ) : (t.w σB).setv 115 v = { t with rS := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 115
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl
theorem tw_setv_rwH (v : ℕ) : (t.w σB).setv 116 v = { t with rwH := v }.w σB := by
  apply WState.eq
  · rfl
  · rfl
  · funext q
    by_cases hq : q = 116
    · subst hq; simp [TSt.w, tReg]
    · simp [TSt.w, tReg, Function.update_of_ne hq, hq]
  · rfl

theorem tw_st_other (j : Fin 17) (h : j.val < 10) : (t.w σB).st j = σB.st j := by
  simp only [TSt.w, tStr]
  split_ifs <;> simp_all

theorem tw_sh_other (j : Fin 17) (h8 : j.val ≠ 8) (h13 : j.val ≠ 13) (h16 : j.val ≠ 16) : (t.w σB).sh j = σB.sh j := by
  simp only [TSt.w, tHd]
  split_ifs <;> simp_all

theorem tw_val_other (q : Fin 118) (h0 : q.val ≠ 0) (h6 : q.val ≠ 6) (h7 : q.val ≠ 7) (h53 : q.val ≠ 53) (h82 : q.val ≠ 82) (h92 : q.val ≠ 92) (h109 : q.val ≠ 109) (h110 : q.val ≠ 110) (h111 : q.val ≠ 111) (h112 : q.val ≠ 112) (h113 : q.val ≠ 113) (h114 : q.val ≠ 114) (h115 : q.val ≠ 115) (h116 : q.val ≠ 116) :
    (t.w σB).val q = σB.val q := by
  have n0 : q ≠ 0 := fun e => h0 (by rw [e]; rfl)
  have n6 : q ≠ 6 := fun e => h6 (by rw [e]; rfl)
  have n7 : q ≠ 7 := fun e => h7 (by rw [e]; rfl)
  have n53 : q ≠ 53 := fun e => h53 (by rw [e]; rfl)
  have n82 : q ≠ 82 := fun e => h82 (by rw [e]; rfl)
  have n92 : q ≠ 92 := fun e => h92 (by rw [e]; rfl)
  have n109 : q ≠ 109 := fun e => h109 (by rw [e]; rfl)
  have n110 : q ≠ 110 := fun e => h110 (by rw [e]; rfl)
  have n111 : q ≠ 111 := fun e => h111 (by rw [e]; rfl)
  have n112 : q ≠ 112 := fun e => h112 (by rw [e]; rfl)
  have n113 : q ≠ 113 := fun e => h113 (by rw [e]; rfl)
  have n114 : q ≠ 114 := fun e => h114 (by rw [e]; rfl)
  have n115 : q ≠ 115 := fun e => h115 (by rw [e]; rfl)
  have n116 : q ≠ 116 := fun e => h116 (by rw [e]; rfl)
  simp only [TSt.w, tReg, if_neg n0, if_neg n6, if_neg n7, if_neg n53, if_neg n82, if_neg n92, if_neg n109, if_neg n110, if_neg n111, if_neg n112, if_neg n113, if_neg n114, if_neg n115, if_neg n116]

end Lemmas

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
