import Proof.Wire_3_5.UnionMachine.FrontAtomLoop
import Proof.Wire_3_5.UnionMachine.FrontSize
import Proof.Wire_3_5.UnionMachine.FrontTemplate

/-! # C6 front, U1b: the atom stage at the description envelope (P3:3670, 3083-3094)

A copy of the atom stage (`FrontAtomStage`) whose decoder policy `L` is a SEPARATE input `1^L` (tape `xs 13`, copied
to the policy tape `1699` by the setup's fifth sum) instead of the capacity `P`. At `L = (q+1)^{descDeg}` the loop's
verdict is `0` exactly when every guessed atom decodes AND has at most `(q+1)^{descDeg}` description bits
(`FrontDescLoop.passedM_desc`): "It rejects malformed descriptions, oversized atoms" (P3:3670) and the atom test
`AtomsOkG` in one pass.

Tapes: as M15 (`lp` loop, `dpS` power workspace, `xs` 16 more), with `xs 13` the policy `1^L`.
Main statement: **`atoms_stage`**. Paper quantity: the rejection of malformed or oversized guessed atoms. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomStageL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLayout NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomRound NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLoop

abbrev DT : ℕ := RepairSource.ProjectionNormalization.DimensionPolynomial.tapes 26
abbrev SX : ℕ := DT + 16
abbrev ST : ℕ := AT + SX

def lp (y : Fin AT) : Fin ST := Fin.castAdd SX y
def dpS (i : Fin DT) : Fin ST := Fin.natAdd AT (Fin.castAdd 16 i)
def xs (k : Fin 16) : Fin ST := Fin.natAdd AT (Fin.natAdd DT k)

theorem lp_val (y : Fin AT) : (lp y).val = y.val := rfl
theorem xs_val (k : Fin 16) : (xs k).val = 1714 + (DT + k.val) := rfl
theorem sm_val (k : Fin 11) : (sm k).val = 1703 + k.val := rfl

theorem lp_inj : Function.Injective lp := fun a b h => by simpa [lp] using h
theorem dpS_inj : Function.Injective dpS := fun a b h => by simpa [dpS] using h

/-- The decoder's capacity at a witness of `nw` bits. -/
@[irreducible] def capP (nw : ℕ) : ℕ := 1000000000000000000000000000000 * (nw + 1) ^ 26

/-- The stage's input: the rest `frame r` on the loop's rest tape, `1^{|w|}`, `1^q`, `1^E`, `1^{nf}`. -/
def sIn (r : List Bool) (nw q E nf L : ℕ) (i : Fin ST) : List Bool :=
  if i = lp (sm 0) then frame r else if i = xs 0 then List.replicate nw true
  else if i = xs 1 then List.replicate q true else if i = xs 2 then List.replicate E true
  else if i = xs 3 then List.replicate nf true else if i = xs 13 then List.replicate L true else []

/-! ## The setup's machines -/

/-- The power's result tape. -/
def vS : Fin DT := ⟨55, by decide⟩
/-- The power's input tape. -/
def d0 : Fin DT := ⟨0, by decide⟩

theorem vS_eq : CloseoutRowsEstimator.DriverPower.valueSlot 26 = vS := Fin.ext (by decide)

def s1 : Fin 4 → Fin ST := ![xs 0, xs 5, dpS d0, xs 4]
def s3 : Fin 4 → Fin ST := ![dpS vS, xs 5, lp (dm 1694), lp (sm 10)]
def s4 : Fin 4 → Fin ST := ![dpS vS, xs 5, lp (dm 1698), xs 6]
def s5 : Fin 4 → Fin ST := ![xs 13, xs 5, lp (dm 1699), xs 7]
def s6 : Fin 4 → Fin ST := ![dpS vS, lp (dm 1694), lp (sm 8), lp (sm 9)]

theorem s1_inj : Function.Injective s1 := by decide
theorem s3_inj : Function.Injective s3 := by decide
theorem s4_inj : Function.Injective s4 := by decide
theorem s5_inj : Function.Injective s5 := by decide
theorem s6_inj : Function.Injective s6 := by decide

/-- The registers the fill blanks: the loop's `PG PT K J BAD`, the template's `PQ PT`, the count's `PE`. -/
def tgtS (i : Fin ST) : Bool :=
  decide (i = lp (sm 2)) || decide (i = lp (sm 3)) || decide (i = lp (sm 4)) || decide (i = lp (sm 6)) ||
    decide (i = lp (sm 7)) || decide (i = xs 9) || decide (i = xs 10) || decide (i = xs 12)

/-- The setup's ready part: the capacity and its copies, the ruler, the registers, the cells. -/
noncomputable def setupM :=
  Composition.machine (RecoveryFocus.machine s1 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine dpS (CloseoutRowsEstimator.DriverPower.machine 26 1000000000000000000000000000000))
  (Composition.machine (RecoveryFocus.machine s3 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine s4 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine s5 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine s6 ClockUnarySum.machine)
  (Composition.machine (FrontFill.fillP (xs 3) (xs 8) tgtS).compile
  (Composition.machine (FrontKit.cellP (lp (sm 1))).compile
  (Composition.machine (FrontKit.cellP (lp (sm 5))).compile (FrontKit.cellP (xs 11)).compile))))))))

/-! ## The named tapes' positions -/

theorem DT_eq : DT = 66 := rfl

@[simp] theorem v_lp (y : Fin AT) : (lp y).val = y.val := rfl
@[simp] theorem v_dm (i : Fin 1703) : (dm i).val = i.val := rfl
@[simp] theorem v_sm (k : Fin 11) : (sm k).val = 1703 + k.val := rfl
@[simp] theorem v_xs (k : Fin 16) : (xs k).val = 1780 + k.val := by
  show 1714 + (DT + k.val) = _; rw [DT_eq]; omega
@[simp] theorem v_dpS (i : Fin DT) : (dpS i).val = 1714 + i.val := rfl
@[simp] theorem v_vS : vS.val = 55 := rfl
@[simp] theorem v_d0 : d0.val = 0 := rfl

/-- Distinct positions, distinct tapes. -/
theorem ne_of_v {a b : Fin ST} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-! ## The setup's banks, stage by stage -/

theorem lp_ne_xs (y : Fin AT) (k : Fin 16) : lp y ≠ xs k := by
  intro e; have h1 := congrArg Fin.val e; rw [v_lp, v_xs] at h1; have : y.val < 1714 := y.isLt; omega
theorem xs_ne_lp (y : Fin AT) (k : Fin 16) : xs k ≠ lp y := fun e => lp_ne_xs y k e.symm
theorem lp_ne (y z : Fin AT) (h : y ≠ z) : lp y ≠ lp z := fun e => h (lp_inj e)
theorem dm_ne (i j : Fin 1703) (h : i ≠ j) : dm i ≠ dm j := fun e => h (dm_inj e)
theorem sm_ne (i j : Fin 11) (h : i ≠ j) : sm i ≠ sm j := fun e => h (sm_inj e)
theorem sm_ne_dm (k : Fin 11) (i : Fin 1703) : sm k ≠ dm i := fun e => dm_ne_sm i k e.symm
theorem xs_ne (i j : Fin 16) (h : i ≠ j) : xs i ≠ xs j := by
  intro e; have h1 := congrArg Fin.val e; rw [v_xs, v_xs] at h1; exact h (Fin.ext (by omega))
theorem xs_inj {i j : Fin 16} (h : xs i = xs j) : i = j := by
  have h1 := congrArg Fin.val h; rw [v_xs, v_xs] at h1; exact Fin.ext (by omega)
theorem dpS_ne_lp (i : Fin DT) (y : Fin AT) : dpS i ≠ lp y := by
  intro e; have h1 := congrArg Fin.val e; rw [v_dpS, v_lp] at h1; have : y.val < 1714 := y.isLt; omega
theorem dpS_ne_xs (i : Fin DT) (k : Fin 16) : dpS i ≠ xs k := by
  intro e; have h1 := congrArg Fin.val e; rw [v_dpS, v_xs] at h1; have : i.val < 66 := i.isLt; omega

section Setup
variable (r : List Bool) (nw q E nf L : ℕ)

/-- After the copy of `1^{|w|}` onto the power's input. -/
noncomputable def B1 : Fin ST → List Bool :=
  Function.update (Function.update (sIn r nw q E nf L) (dpS d0) (List.replicate nw true)) (xs 4) (List.replicate (nw + 2) false)
/-- After the power. -/
noncomputable def B2 (dout : Fin DT → List Bool) : Fin ST → List Bool := install dpS (B1 r nw q E nf L) dout
/-- After the copies of `1^P` and the ruler `1^{2P}`. -/
noncomputable def B3 (dout : Fin DT → List Bool) : Fin ST → List Bool :=
  Function.update (Function.update (B2 r nw q E nf L dout) (lp (dm 1694)) (List.replicate (capP nw + 0) true)) (lp (sm 10))
    (List.replicate (capP nw + 0 + 2) false)
noncomputable def B4 (dout : Fin DT → List Bool) : Fin ST → List Bool :=
  Function.update (Function.update (B3 r nw q E nf L dout) (lp (dm 1698)) (List.replicate (capP nw + 0) true)) (xs 6)
    (List.replicate (capP nw + 0 + 2) false)
noncomputable def B5 (dout : Fin DT → List Bool) : Fin ST → List Bool :=
  Function.update (Function.update (B4 r nw q E nf L dout) (lp (dm 1699)) (List.replicate (L + 0) true)) (xs 7)
    (List.replicate (L + 0 + 2) false)
noncomputable def B6 (dout : Fin DT → List Bool) : Fin ST → List Bool :=
  Function.update (Function.update (B5 r nw q E nf L dout) (lp (sm 8)) (List.replicate (capP nw + capP nw) true)) (lp (sm 9))
    (List.replicate (capP nw + capP nw + 2) false)

/-- Closes a tape (in)equality of the stage's layout. -/
macro "tv" : tactic => `(tactic| (simp only [Fin.ext_iff, v_lp, v_dm, v_sm, v_xs, v_dpS, v_vS, v_d0, s1, s3, s4, s5, s6,
  Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue] <;> decide))

theorem step1 : ClockJoin.ReadyRun (RecoveryFocus.machine s1 ClockUnarySum.machine) (2 * (nw + 0) + 6)
    (sIn r nw q E nf L) (B1 r nw q E nf L) := by
  have g := (ClockUnarySum.sum_ready nw 0).focus s1 s1_inj (sIn r nw q E nf L) (by
    intro j; fin_cases j <;> simp [s1, sIn, Fin.ext_iff])
  convert g using 1
  refine (install_eq_of s1 s1_inj _ _ _ ?_ ?_).symm
  · intro j; fin_cases j
    · show B1 r nw q E nf L (xs 0) = _
      simp [B1, Function.update_apply, sIn, Fin.ext_iff]
    · show B1 r nw q E nf L (xs 5) = _
      simp [B1, Function.update_apply, sIn, Fin.ext_iff]
    · show B1 r nw q E nf L (dpS d0) = _
      simp [B1, Function.update_apply, Fin.ext_iff]
    · show B1 r nw q E nf L (xs 4) = _
      simp [B1, Function.update_apply]
  · intro y hy
    have h2 : y ≠ dpS d0 := fun h => hy 2 h.symm
    have h3 : y ≠ xs 4 := fun h => hy 3 h.symm
    simp [B1, Function.update_apply, h2, h3]

/-- **One unary sum at four slots**: the sum on the third, its scratch on the fourth, the summands kept. -/
theorem sum_step {B : Fin ST → List Bool} (sl : Fin 4 → Fin ST) (hsl : Function.Injective sl) (a b : ℕ)
    (h0 : B (sl 0) = List.replicate a true) (h1 : B (sl 1) = List.replicate b true) (h2 : B (sl 2) = [])
    (h3 : B (sl 3) = []) :
    ClockJoin.ReadyRun (RecoveryFocus.machine sl ClockUnarySum.machine) (2 * (a + b) + 6) B
      (Function.update (Function.update B (sl 2) (List.replicate (a + b) true)) (sl 3) (List.replicate (a + b + 2) false)) := by
  have g := (ClockUnarySum.sum_ready a b).focus sl hsl B (by
    intro j; fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  convert g using 1
  have n02 : sl 0 ≠ sl 2 := fun h => absurd (hsl h) (by decide)
  have n03 : sl 0 ≠ sl 3 := fun h => absurd (hsl h) (by decide)
  have n12 : sl 1 ≠ sl 2 := fun h => absurd (hsl h) (by decide)
  have n13 : sl 1 ≠ sl 3 := fun h => absurd (hsl h) (by decide)
  have n23 : sl 2 ≠ sl 3 := fun h => absurd (hsl h) (by decide)
  refine (install_eq_of sl hsl _ _ _ ?_ ?_).symm
  · intro j; fin_cases j
    · show Function.update (Function.update B (sl 2) _) (sl 3) _ (sl 0) = _
      rw [Function.update_of_ne n03, Function.update_of_ne n02, h0]; rfl
    · show Function.update (Function.update B (sl 2) _) (sl 3) _ (sl 1) = _
      rw [Function.update_of_ne n13, Function.update_of_ne n12, h1]; rfl
    · show Function.update (Function.update B (sl 2) _) (sl 3) _ (sl 2) = _
      rw [Function.update_of_ne n23, Function.update_self]; rfl
    · show Function.update (Function.update B (sl 2) _) (sl 3) _ (sl 3) = _
      rw [Function.update_self]; rfl
  · intro y hy
    rw [Function.update_of_ne (fun h => hy 3 h.symm), Function.update_of_ne (fun h => hy 2 h.symm)]

theorem B2_dpS (dout : Fin DT → List Bool) (i : Fin DT) : B2 r nw q E nf L dout (dpS i) = dout i := by
  rw [B2, install_slot _ dpS_inj]

theorem B2_nd (dout : Fin DT → List Bool) (y : Fin ST) (hy : ∀ i, dpS i ≠ y) :
    B2 r nw q E nf L dout y = B1 r nw q E nf L y := by
  rw [B2, install_other _ _ _ _ hy]

/-- A tape of the loop's or the extra tapes is off the power's workspace. -/
theorem off_lp (y : Fin AT) : ∀ i, dpS i ≠ lp y := by
  intro i h; have h1 := congrArg Fin.val h; rw [v_dpS, v_lp] at h1
  have : y.val < 1714 := y.isLt
  omega
theorem off_xs (k : Fin 16) : ∀ i, dpS i ≠ xs k := by
  intro i h; have h1 := congrArg Fin.val h; rw [v_dpS, v_xs] at h1
  have : i.val < 66 := i.isLt
  omega

/-- Distinct concrete tapes, by their positions. -/
macro "dt" : tactic => `(tactic| (apply ne_of_v; simp))

theorem sIn_lp (y : Fin AT) : sIn r nw q E nf L (lp y) = if y = sm 0 then frame r else [] := by
  unfold sIn
  by_cases h : y = sm 0
  · subst h; simp
  · rw [if_neg (fun e => h (lp_inj e)), if_neg h]
    have hx : ∀ k : Fin 16, lp y ≠ xs k := by
      intro k e; have h1 := congrArg Fin.val e; rw [v_lp, v_xs] at h1; have : y.val < 1714 := y.isLt; omega
    simp [hx]

theorem sIn_xs5 : sIn r nw q E nf L (xs 5) = [] := by
  unfold sIn; simp [Fin.ext_iff]

theorem B1_lp (y : Fin AT) : B1 r nw q E nf L (lp y) = if y = sm 0 then frame r else [] := by
  have hy : y.val < 1714 := y.isLt
  have e1 : lp y ≠ xs 4 := by intro e; have h1 := congrArg Fin.val e; rw [v_lp, v_xs] at h1; omega
  have e2 : lp y ≠ dpS d0 := by intro e; have h1 := congrArg Fin.val e; rw [v_lp, v_dpS] at h1; omega
  rw [B1, Function.update_of_ne e1, Function.update_of_ne e2, sIn_lp]

theorem B2_lp (dout : Fin DT → List Bool) (y : Fin AT) :
    B2 r nw q E nf L dout (lp y) = if y = sm 0 then frame r else [] := by
  rw [B2_nd _ _ _ _ _ _ _ _ (off_lp y), B1_lp]

theorem B2_xs (dout : Fin DT → List Bool) (k : Fin 16) (h4 : k ≠ 4) :
    B2 r nw q E nf L dout (xs k) = sIn r nw q E nf L (xs k) := by
  have e1 : xs k ≠ xs 4 := by
    intro e; have h1 := congrArg Fin.val e; rw [v_xs, v_xs] at h1
    exact h4 (Fin.ext (by simp at h1; simp; omega))
  have e2 : xs k ≠ dpS d0 := by intro e; have h1 := congrArg Fin.val e; rw [v_xs, v_dpS] at h1; simp at h1; omega
  rw [B2_nd _ _ _ _ _ _ _ _ (off_xs k), B1, Function.update_of_ne e1, Function.update_of_ne e2]

/-- After the fill. -/
noncomputable def B7 (dout : Fin DT → List Bool) : Fin ST → List Bool := fun i =>
  if FrontFill.side (xs 8) tgtS i then List.replicate (2 * nf + 3) false else B6 r nw q E nf L dout i
/-- After the three cells. -/
noncomputable def B10 (dout : Fin DT → List Bool) : Fin ST → List Bool :=
  Function.update (Function.update (Function.update (B7 r nw q E nf L dout) (lp (sm 1)) [false]) (lp (sm 5)) [false])
    (xs 11) [false]

/-- The update targets of the copies and the ruler. -/
def isW (y : Fin ST) : Prop :=
  y = lp (dm 1694) ∨ y = lp (sm 10) ∨ y = lp (dm 1698) ∨ y = xs 6 ∨ y = lp (dm 1699) ∨ y = xs 7 ∨ y = lp (sm 8) ∨
    y = lp (sm 9)

theorem B6_nw (dout : Fin DT → List Bool) (y : Fin ST) (hy : ¬ isW y) : B6 r nw q E nf L dout y = B2 r nw q E nf L dout y := by
  simp only [isW, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hy
  rw [B6, Function.update_of_ne h8, Function.update_of_ne h7, B5, Function.update_of_ne h6, Function.update_of_ne h5,
    B4, Function.update_of_ne h4, Function.update_of_ne h3, B3, Function.update_of_ne h2, Function.update_of_ne h1]

theorem B3_nw (dout : Fin DT → List Bool) (y : Fin ST) (h1 : y ≠ lp (dm 1694)) (h2 : y ≠ lp (sm 10)) :
    B3 r nw q E nf L dout y = B2 r nw q E nf L dout y := by
  rw [B3, Function.update_of_ne h2, Function.update_of_ne h1]
theorem B4_nw (dout : Fin DT → List Bool) (y : Fin ST) (h1 : y ≠ lp (dm 1698)) (h2 : y ≠ xs 6) :
    B4 r nw q E nf L dout y = B3 r nw q E nf L dout y := by
  rw [B4, Function.update_of_ne h2, Function.update_of_ne h1]
theorem B5_nw (dout : Fin DT → List Bool) (y : Fin ST) (h1 : y ≠ lp (dm 1699)) (h2 : y ≠ xs 7) :
    B5 r nw q E nf L dout y = B4 r nw q E nf L dout y := by
  rw [B5, Function.update_of_ne h2, Function.update_of_ne h1]

theorem step2 (dout : Fin DT → List Bool)
    (hdr : ClockJoin.ReadyRun (CloseoutRowsEstimator.DriverPower.machine 26 1000000000000000000000000000000)
      (CloseoutRowsEstimator.DriverPower.budget 26 1000000000000000000000000000000 nw)
      (RepairSource.ProjectionNormalization.DimensionPolynomial.input 26 nw) dout) :
    ClockJoin.ReadyRun (RecoveryFocus.machine dpS (CloseoutRowsEstimator.DriverPower.machine 26 1000000000000000000000000000000))
      (CloseoutRowsEstimator.DriverPower.budget 26 1000000000000000000000000000000 nw)
      (B1 r nw q E nf L) (B2 r nw q E nf L dout) := by
  refine hdr.focus dpS dpS_inj (B1 r nw q E nf L) ?_
  intro j
  have e1 : dpS j ≠ xs 4 := by
    intro e; have h1 := congrArg Fin.val e; rw [v_dpS, v_xs] at h1; have : j.val < 66 := j.isLt; simp at h1; omega
  rw [B1, Function.update_of_ne e1]
  by_cases hj : j = d0
  · subst hj; rw [Function.update_self]; simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, d0]
  · rw [Function.update_of_ne (fun e => hj (dpS_inj e))]
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    have hs : sIn r nw q E nf L (dpS j) = [] := by
      have : j.val < 66 := j.isLt
      unfold sIn
      rw [if_neg (ne_of_v (by simp; omega)), if_neg (ne_of_v (by simp; omega)), if_neg (ne_of_v (by simp; omega)),
        if_neg (ne_of_v (by simp; omega)), if_neg (ne_of_v (by simp; omega)), if_neg (ne_of_v (by simp; omega))]
    rw [hs]; simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hj']

theorem step3 (dout : Fin DT → List Bool) (hd : dout vS = List.replicate (capP nw) true) :
    ClockJoin.ReadyRun (RecoveryFocus.machine s3 ClockUnarySum.machine) (2 * (capP nw + 0) + 6)
      (B2 r nw q E nf L dout) (B3 r nw q E nf L dout) :=
  sum_step s3 s3_inj (capP nw) 0 (by show B2 r nw q E nf L dout (dpS vS) = _; rw [B2_dpS, hd])
    (by show B2 r nw q E nf L dout (xs 5) = _; rw [B2_xs _ _ _ _ _ _ _ _ (by decide), sIn_xs5]; rfl)
    (by show B2 r nw q E nf L dout (lp (dm 1694)) = _; rw [B2_lp, if_neg (dm_ne_sm _ _)])
    (by show B2 r nw q E nf L dout (lp (sm 10)) = _; rw [B2_lp, if_neg (fun h => absurd (sm_inj h) (by decide))])

theorem step4 (dout : Fin DT → List Bool) (hd : dout vS = List.replicate (capP nw) true) :
    ClockJoin.ReadyRun (RecoveryFocus.machine s4 ClockUnarySum.machine) (2 * (capP nw + 0) + 6)
      (B3 r nw q E nf L dout) (B4 r nw q E nf L dout) :=
  sum_step s4 s4_inj (capP nw) 0
    (by show B3 r nw q E nf L dout (dpS vS) = _
        rw [B3_nw _ _ _ _ _ _ _ _ (dpS_ne_lp _ _) (dpS_ne_lp _ _), B2_dpS, hd])
    (by show B3 r nw q E nf L dout (xs 5) = _
        rw [B3_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne_lp _ _), B2_xs _ _ _ _ _ _ _ _ (by decide), sIn_xs5]; rfl)
    (by show B3 r nw q E nf L dout (lp (dm 1698)) = _
        rw [B3_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne _ _ (dm_ne_sm _ _)), B2_lp,
          if_neg (dm_ne_sm _ _)])
    (by show B3 r nw q E nf L dout (xs 6) = _
        rw [B3_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne_lp _ _), B2_xs _ _ _ _ _ _ _ _ (by decide)]
        simp [sIn, Fin.ext_iff])

theorem sIn_xs13 : sIn r nw q E nf L (xs 13) = List.replicate L true := by
  unfold sIn
  rw [if_neg (xs_ne_lp _ _), if_neg (xs_ne _ _ (by decide)), if_neg (xs_ne _ _ (by decide)),
    if_neg (xs_ne _ _ (by decide)), if_neg (xs_ne _ _ (by decide)), if_pos rfl]

theorem step5 (dout : Fin DT → List Bool) :
    ClockJoin.ReadyRun (RecoveryFocus.machine s5 ClockUnarySum.machine) (2 * (L + 0) + 6)
      (B4 r nw q E nf L dout) (B5 r nw q E nf L dout) :=
  sum_step s5 s5_inj L 0
    (by show B4 r nw q E nf L dout (xs 13) = _
        rw [B4_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne _ _ (by decide)),
          B3_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne_lp _ _), B2_xs _ _ _ _ _ _ _ _ (by decide), sIn_xs13])
    (by show B4 r nw q E nf L dout (xs 5) = _
        rw [B4_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne _ _ (by decide)),
          B3_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne_lp _ _), B2_xs _ _ _ _ _ _ _ _ (by decide), sIn_xs5]; rfl)
    (by show B4 r nw q E nf L dout (lp (dm 1699)) = _
        rw [B4_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne_xs _ _),
          B3_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne _ _ (dm_ne_sm _ _)), B2_lp,
          if_neg (dm_ne_sm _ _)])
    (by show B4 r nw q E nf L dout (xs 7) = _
        rw [B4_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne _ _ (by decide)),
          B3_nw _ _ _ _ _ _ _ _ (xs_ne_lp _ _) (xs_ne_lp _ _), B2_xs _ _ _ _ _ _ _ _ (by decide)]
        simp [sIn, Fin.ext_iff])

theorem step6 (dout : Fin DT → List Bool) (hd : dout vS = List.replicate (capP nw) true) :
    ClockJoin.ReadyRun (RecoveryFocus.machine s6 ClockUnarySum.machine) (2 * (capP nw + (capP nw + 0)) + 6)
      (B5 r nw q E nf L dout) (B6 r nw q E nf L dout) :=
  sum_step s6 s6_inj (capP nw) (capP nw + 0)
    (by show B5 r nw q E nf L dout (dpS vS) = _
        rw [B5_nw _ _ _ _ _ _ _ _ (dpS_ne_lp _ _) (dpS_ne_xs _ _), B4_nw _ _ _ _ _ _ _ _ (dpS_ne_lp _ _) (dpS_ne_xs _ _),
          B3_nw _ _ _ _ _ _ _ _ (dpS_ne_lp _ _) (dpS_ne_lp _ _), B2_dpS, hd])
    (by show B5 r nw q E nf L dout (lp (dm 1694)) = _
        rw [B5_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne_xs _ _),
          B4_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne_xs _ _), B3,
          Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)), Function.update_self])
    (by show B5 r nw q E nf L dout (lp (sm 8)) = _
        rw [B5_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne_xs _ _),
          B4_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne_xs _ _),
          B3_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne _ _ (sm_ne _ _ (by decide))), B2_lp,
          if_neg (sm_ne _ _ (by decide))])
    (by show B5 r nw q E nf L dout (lp (sm 9)) = _
        rw [B5_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne_xs _ _),
          B4_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne_xs _ _),
          B3_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne _ _ (sm_ne _ _ (by decide))), B2_lp,
          if_neg (sm_ne _ _ (by decide))])

theorem not_isW_lp_sm (k : Fin 11) (h8 : k ≠ 8) (h9 : k ≠ 9) (h10 : k ≠ 10) : ¬ isW (lp (sm k)) := by
  simp only [isW, not_or]
  refine ⟨lp_ne _ _ (sm_ne_dm _ _), lp_ne _ _ (sm_ne _ _ h10), lp_ne _ _ (sm_ne_dm _ _), lp_ne_xs _ _,
    lp_ne _ _ (sm_ne_dm _ _), lp_ne_xs _ _, lp_ne _ _ (sm_ne _ _ h8), lp_ne _ _ (sm_ne _ _ h9)⟩

theorem not_isW_xs (k : Fin 16) (h6 : k ≠ 6) (h7 : k ≠ 7) : ¬ isW (xs k) := by
  simp only [isW, not_or]
  exact ⟨xs_ne_lp _ _, xs_ne_lp _ _, xs_ne_lp _ _, xs_ne _ _ h6, xs_ne_lp _ _, xs_ne _ _ h7, xs_ne_lp _ _,
    xs_ne_lp _ _⟩

theorem B6_lp_sm (dout : Fin DT → List Bool) (k : Fin 11) (h0 : k ≠ 0) (h8 : k ≠ 8) (h9 : k ≠ 9) (h10 : k ≠ 10) :
    B6 r nw q E nf L dout (lp (sm k)) = [] := by
  rw [B6_nw _ _ _ _ _ _ _ _ (not_isW_lp_sm k h8 h9 h10), B2_lp, if_neg (sm_ne _ _ h0)]

theorem B6_xs (dout : Fin DT → List Bool) (k : Fin 16) (h4 : k ≠ 4) (h6 : k ≠ 6) (h7 : k ≠ 7) :
    B6 r nw q E nf L dout (xs k) = sIn r nw q E nf L (xs k) := by
  rw [B6_nw _ _ _ _ _ _ _ _ (not_isW_xs k h6 h7), B2_xs _ _ _ _ _ _ _ _ h4]

theorem sIn_xs_hi (k : Fin 16) (hk : 4 ≤ k.val) (h13 : k ≠ 13) : sIn r nw q E nf L (xs k) = [] := by
  unfold sIn
  rw [if_neg (xs_ne_lp _ _), if_neg (xs_ne _ _ (fun h => by rw [h] at hk; simp at hk)),
    if_neg (xs_ne _ _ (fun h => by rw [h] at hk; simp at hk)), if_neg (xs_ne _ _ (fun h => by rw [h] at hk; simp at hk)),
    if_neg (xs_ne _ _ (fun h => by rw [h] at hk; simp at hk)), if_neg (xs_ne _ _ h13)]

theorem step7 (dout : Fin DT → List Bool) :
    ClockJoin.ReadyRun (FrontFill.fillP (xs 3) (xs 8) tgtS).compile (11 * nf + 20)
      (B6 r nw q E nf L dout) (B7 r nw q E nf L dout) := by
  refine FrontKit.fill_ready (xs 3) (xs 8) tgtS (B6 r nw q E nf L dout) nf (xs_ne _ _ (by decide)) (by decide)
    (by decide) ?_ ?_
  · rw [B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]; simp [sIn, Fin.ext_iff]
  · intro i hi
    rcases hi with h | h
    · simp only [tgtS, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h <;> subst h
      · exact B6_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      · exact B6_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      · exact B6_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      · exact B6_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      · exact B6_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)
      · rw [B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide), sIn_xs_hi _ _ _ _ _ _ _ (by decide) (by decide)]
      · rw [B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide), sIn_xs_hi _ _ _ _ _ _ _ (by decide) (by decide)]
      · rw [B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide), sIn_xs_hi _ _ _ _ _ _ _ (by decide) (by decide)]
    · rw [h, B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide), sIn_xs_hi _ _ _ _ _ _ _ (by decide) (by decide)]

theorem side_lp_sm (k : Fin 11) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4) (h6 : k ≠ 6) (h7 : k ≠ 7) :
    ¬ FrontFill.side (xs 8) tgtS (lp (sm k)) := by
  rintro (h | h)
  · simp only [tgtS, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact h2 (sm_inj (lp_inj h))
    · exact h3 (sm_inj (lp_inj h))
    · exact h4 (sm_inj (lp_inj h))
    · exact h6 (sm_inj (lp_inj h))
    · exact h7 (sm_inj (lp_inj h))
    · exact lp_ne_xs _ _ h
    · exact lp_ne_xs _ _ h
    · exact lp_ne_xs _ _ h
  · exact lp_ne_xs _ _ h

theorem B7_lp_sm (dout : Fin DT → List Bool) (k : Fin 11) (h0 : k ≠ 0) (h2 : k ≠ 2) (h3 : k ≠ 3) (h4 : k ≠ 4)
    (h6 : k ≠ 6) (h7 : k ≠ 7) (h8 : k ≠ 8) (h9 : k ≠ 9) (h10 : k ≠ 10) : B7 r nw q E nf L dout (lp (sm k)) = [] := by
  rw [B7, if_neg (side_lp_sm k h2 h3 h4 h6 h7), B6_lp_sm _ _ _ _ _ _ _ _ h0 h8 h9 h10]

theorem B7_xs11 (dout : Fin DT → List Bool) : B7 r nw q E nf L dout (xs 11) = [] := by
  have hs : ¬ FrontFill.side (xs 8) tgtS (xs 11) := by
    rintro (h | h)
    · revert h; decide
    · exact xs_ne _ _ (by decide) h
  rw [B7, if_neg hs, B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide), sIn_xs_hi _ _ _ _ _ _ _ (by decide) (by decide)]

theorem capP_pos (nw : ℕ) : 1 ≤ capP nw := by
  unfold capP
  have : 0 < 1000000000000000000000000000000 * (nw + 1) ^ 26 := by positivity
  omega

theorem capP_eq (nw : ℕ) : 1000000000000000000000000000000 * (nw + 1) ^ 26 = capP nw := by unfold capP; rfl

/-- The setup's ready part's step bound. -/
noncomputable def setupCost (nw nf L : ℕ) : ℕ :=
  (2 * (nw + 0) + 6) + 1 + (CloseoutRowsEstimator.DriverPower.budget 26 1000000000000000000000000000000 nw + 1 +
    ((2 * (capP nw + 0) + 6) + 1 + ((2 * (capP nw + 0) + 6) + 1 + ((2 * (L + 0) + 6) + 1 +
    ((2 * (capP nw + (capP nw + 0)) + 6) + 1 + ((11 * nf + 20) + 1 + (1 + 1 + (1 + 1 + 1))))))))

/-- **The setup's ready part.** -/
theorem setup_ready : ∃ dout : Fin DT → List Bool, dout d0 = List.replicate nw true ∧
    dout vS = List.replicate (capP nw) true ∧
    ClockJoin.ReadyRun setupM (setupCost nw nf L) (sIn r nw q E nf L) (B10 r nw q E nf L dout) := by
  obtain ⟨dout, hdr, hd0, hd55⟩ := CloseoutRowsEstimator.DriverPower.ready 26 1000000000000000000000000000000 nw
  have hd : dout vS = List.replicate (capP nw) true := by rw [← capP_eq, ← vS_eq]; exact hd55
  refine ⟨dout, hd0, hd, ?_⟩
  have g8 := FrontKit.cell_ready (lp (sm 1)) (B7 r nw q E nf L dout)
    (B7_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  have g9 := FrontKit.cell_ready (lp (sm 5)) (Function.update (B7 r nw q E nf L dout) (lp (sm 1)) [false]) (by
    rw [Function.update_of_ne (lp_ne _ _ (sm_ne _ _ (by decide)))]
    exact B7_lp_sm _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  have g10 := FrontKit.cell_ready (xs 11)
    (Function.update (Function.update (B7 r nw q E nf L dout) (lp (sm 1)) [false]) (lp (sm 5)) [false]) (by
    rw [Function.update_of_ne (xs_ne_lp _ _), Function.update_of_ne (xs_ne_lp _ _)]
    exact B7_xs11 _ _ _ _ _ _ _)
  exact ClockJoin.join _ _ _ _ _ _ _ (step1 r nw q E nf L)
    (ClockJoin.join _ _ _ _ _ _ _ (step2 r nw q E nf L dout hdr)
    (ClockJoin.join _ _ _ _ _ _ _ (step3 r nw q E nf L dout hd)
    (ClockJoin.join _ _ _ _ _ _ _ (step4 r nw q E nf L dout hd)
    (ClockJoin.join _ _ _ _ _ _ _ (step5 r nw q E nf L dout)
    (ClockJoin.join _ _ _ _ _ _ _ (step6 r nw q E nf L dout hd)
    (ClockJoin.join _ _ _ _ _ _ _ (step7 r nw q E nf L dout)
    (ClockJoin.join _ _ _ _ _ _ _ g8 (ClockJoin.join _ _ _ _ _ _ _ g9 g10))))))))

/-! ## The count and the loop's condition -/

/-- `J := E` from `1^E`, the loop's condition `E ≠ 0` into the cell. -/
def cntP : WM 0 2 :=
  .seq (.whs (0 : Fin 1) (.seq (WM.fwdC (0 : Fin 1) (1 : Fin 2)) (.inc (0 : Fin 2))))
    (.seq (WM.rewind (0 : Fin 1) (1 : Fin 2)) (.ifr (0 : Fin 2) (.setc true) (.setc false)))

def cst (E j : ℕ) (J : ℕ) (c : Bool) : WState 0 2 := ⟨![j], ![List.replicate E true], ![J, j], c⟩

theorem cnt_loop (cap E : ℕ) (hE : E + 1 ≤ cap) (c : Bool) : ∀ j, j ≤ E →
    WExec cap (.whs (0 : Fin 1) (.seq (WM.fwdC (0 : Fin 1) (1 : Fin 2)) (.inc (0 : Fin 2)))) (cst E j j c) (cst E E E c)
      (11 * (E - j) + 1) := by
  intro j
  induction h : E - j generalizing j with
  | zero =>
    intro hj
    have : j = E := by omega
    subst this
    exact WExec.whsF (by simp [wbit, cst, readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_replicate])
  | succ m ih =>
    intro hj
    have hlt : j < E := by omega
    have s1 : WExec cap (WM.fwdC (0 : Fin 1) (1 : Fin 2)) (cst E j j c) ⟨![j + 1], ![List.replicate E true], ![j, j + 1], c⟩ 5 := by
      refine WExec.cast cap (wfwdC_spec cap (0 : Fin 1) (1 : Fin 2) _ (by simp [cst]; omega)) ?_ le_rfl
      refine WState.eq ?_ ?_ ?_ ?_ <;>
        first | rfl | (funext i; fin_cases i <;> simp [cst, WState.seth, WState.setv, Function.update_apply])
    have s2 : WExec cap (.inc (0 : Fin 2)) ⟨![j + 1], ![List.replicate E true], ![j, j + 1], c⟩ (cst E (j + 1) (j + 1) c) 3 := by
      refine WExec.cast cap (WExec.inc (cap := cap) (0 : Fin 2) _ (by simp; omega)) ?_ le_rfl
      refine WState.eq ?_ ?_ ?_ ?_ <;>
        first | rfl | (funext i; fin_cases i <;> simp [cst, WState.setv, Function.update_apply])
    have s3 := ih (j + 1) (by omega) (by omega)
    refine WExec.mono (WExec.whsT (by simp [wbit, cst, readTapeBit, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, hlt]) (s1.seq s2) s3) (by omega)

theorem cnt_spec (cap E : ℕ) (hE : E + 1 ≤ cap) (c : Bool) :
    WExec cap cntP (cst E 0 0 c) ⟨![0], ![List.replicate E true], ![E, 0], decide (E ≠ 0)⟩ (20 * E + 20) := by
  have s1 := cnt_loop cap E hE c 0 (by omega)
  have s2 : WExec cap (WM.rewind (0 : Fin 1) (1 : Fin 2)) (cst E E E c) ⟨![0], ![List.replicate E true], ![E, 0], c⟩
      (5 * E + 1) := by
    refine WExec.cast cap (wrewind_spec cap (0 : Fin 1) (1 : Fin 2) E _ rfl (by simp [cst]; omega)) ?_ le_rfl
    refine WState.eq ?_ ?_ ?_ ?_ <;>
      first | rfl | (funext i; fin_cases i <;> simp [cst, WState.seth, WState.setv, Function.update_apply])
  have s3 : WExec cap (.ifr (0 : Fin 2) (.setc true) (.setc false)) ⟨![0], ![List.replicate E true], ![E, 0], c⟩
      ⟨![0], ![List.replicate E true], ![E, 0], decide (E ≠ 0)⟩ 2 := by
    by_cases h : E = 0
    · subst h
      exact WExec.ifrF (by simp) (WExec.cast cap (WExec.setc false _) (by simp [WState.setc]) le_rfl)
    · exact WExec.ifrT (by simpa using h) (WExec.cast cap (WExec.setc true _) (by simp [WState.setc, h]) le_rfl)
  exact WExec.mono (s1.seq (s2.seq s3)) (by omega)

/-! ## The whole stage -/

def tmap : Fin 5 → Fin ST := ![xs 1, xs 11, lp (dm 1674), xs 9, xs 10]
def jmap : Fin 4 → Fin ST := ![xs 2, lp (sm 5), lp (sm 6), xs 12]
theorem tmap_inj : Function.Injective tmap := by decide
theorem jmap_inj : Function.Injective jmap := by decide

/-- **The atom stage** of mode `m`: the setup, the template, the count, the loop. -/
noncomputable def stageM (m : Mode) :=
  Composition.machine setupM (Composition.machine (RecoveryFocus.machine tmap FrontTemplate.tmplP.toProg.compile)
    (Composition.machine (RecoveryFocus.machine jmap cntP.toProg.compile)
      (RecoveryFocus.machine lp (StreamController.machine (FrontAtomLoop.roundM m) (sm 5)))))

theorem B6_dm (dout : Fin DT → List Bool) :
    B6 r nw q E nf L dout (lp (dm 1694)) = List.replicate (capP nw + 0) true ∧
    B6 r nw q E nf L dout (lp (dm 1698)) = List.replicate (capP nw + 0) true ∧
    B6 r nw q E nf L dout (lp (dm 1699)) = List.replicate (L + 0) true := by
  have a1 : lp (dm 1694) ≠ lp (sm 8) := lp_ne _ _ (dm_ne_sm _ _)
  have a2 : lp (dm 1694) ≠ lp (sm 9) := lp_ne _ _ (dm_ne_sm _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [B6, Function.update_of_ne a2, Function.update_of_ne a1,
      B5_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne_xs _ _),
      B4_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne_xs _ _), B3,
      Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)), Function.update_self]
  · rw [B6, Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)), Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)),
      B5_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (dm_ne _ _ (by decide))) (lp_ne_xs _ _), B4,
      Function.update_of_ne (lp_ne_xs _ _), Function.update_self]
  · rw [B6, Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)), Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)), B5,
      Function.update_of_ne (lp_ne_xs _ _), Function.update_self]

theorem side_lp_dm (i : Fin 1703) : ¬ FrontFill.side (xs 8) tgtS (lp (dm i)) := by
  rintro (h | h)
  · simp only [tgtS, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h <;>
      first | exact dm_ne_sm _ _ (lp_inj h) | exact lp_ne_xs _ _ h
  · exact lp_ne_xs _ _ h

/-- The setup's decoder bank. -/
theorem B10_dm (dout : Fin DT → List Bool) (i : Fin 1703) :
    B10 r nw q E nf L dout (lp (dm i)) =
      if i = 1694 ∨ i = 1698 then List.replicate (capP nw + 0) true
      else if i = 1699 then List.replicate (L + 0) true else [] := by
  rw [B10, Function.update_of_ne (lp_ne_xs _ _), Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)),
    Function.update_of_ne (lp_ne _ _ (dm_ne_sm _ _)), B7, if_neg (side_lp_dm i)]
  obtain ⟨b1, b2, b3⟩ := B6_dm r nw q E nf L dout
  by_cases h1 : i = 1694
  · subst h1; rw [b1]; simp
  by_cases h2 : i = 1698
  · subst h2; rw [b2]; simp
  by_cases h3 : i = 1699
  · subst h3; rw [b3]; simp
  rw [if_neg (by tauto), if_neg h3]
  have hw : ¬ isW (lp (dm i)) := by
    simp only [isW, not_or]
    exact ⟨lp_ne _ _ (dm_ne _ _ h1), lp_ne _ _ (dm_ne_sm _ _), lp_ne _ _ (dm_ne _ _ h2), lp_ne_xs _ _,
      lp_ne _ _ (dm_ne _ _ h3), lp_ne_xs _ _, lp_ne _ _ (dm_ne_sm _ _), lp_ne _ _ (dm_ne_sm _ _)⟩
  rw [B6_nw _ _ _ _ _ _ _ _ hw, B2_lp, if_neg (dm_ne_sm _ _)]

theorem B10_xs_in (dout : Fin DT → List Bool) :
    B10 r nw q E nf L dout (xs 1) = List.replicate q true ∧ B10 r nw q E nf L dout (xs 2) = List.replicate E true ∧
    B10 r nw q E nf L dout (xs 11) = [false] ∧
    B10 r nw q E nf L dout (xs 9) = regTape (2 * nf + 2) 0 ∧ B10 r nw q E nf L dout (xs 10) = regTape (2 * nf + 2) 0 ∧
    B10 r nw q E nf L dout (xs 12) = regTape (2 * nf + 2) 0 := by
  have hside : ∀ k : Fin 16, k = 9 ∨ k = 10 ∨ k = 12 → FrontFill.side (xs 8) tgtS (xs k) := by
    intro k hk; left; rcases hk with rfl | rfl | rfl <;> decide
  have hns : ∀ k : Fin 16, k ≠ 8 → k ≠ 9 → k ≠ 10 → k ≠ 12 → ¬ FrontFill.side (xs 8) tgtS (xs k) := by
    intro k h8 h9 h10 h12 hs
    rcases hs with h | h
    · simp only [tgtS, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
      · exact xs_ne_lp _ _ h
      · exact xs_ne_lp _ _ h
      · exact xs_ne_lp _ _ h
      · exact xs_ne_lp _ _ h
      · exact xs_ne_lp _ _ h
      · exact h9 (xs_inj h)
      · exact h10 (xs_inj h)
      · exact h12 (xs_inj h)
    · exact h8 (xs_inj h)
  have up : ∀ k : Fin 16, k ≠ 11 → B10 r nw q E nf L dout (xs k) = B7 r nw q E nf L dout (xs k) := by
    intro k hk
    rw [B10, Function.update_of_ne (xs_ne _ _ hk), Function.update_of_ne (xs_ne_lp _ _),
      Function.update_of_ne (xs_ne_lp _ _)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [up _ (by decide), B7, if_neg (hns _ (by decide) (by decide) (by decide) (by decide)),
      B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [sIn, Fin.ext_iff]
  · rw [up _ (by decide), B7, if_neg (hns _ (by decide) (by decide) (by decide) (by decide)),
      B6_xs _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [sIn, Fin.ext_iff]
  · rw [B10, Function.update_self]
  · rw [up _ (by decide), B7, if_pos (hside _ (by decide)), regTape_zero]
  · rw [up _ (by decide), B7, if_pos (hside _ (by decide)), regTape_zero]
  · rw [up _ (by decide), B7, if_pos (hside _ (by decide)), regTape_zero]

/-- The loop's own tapes after the setup. -/
theorem B10_sm (dout : Fin DT → List Bool) :
    B10 r nw q E nf L dout (lp (sm 0)) = frame r ∧ B10 r nw q E nf L dout (lp (sm 1)) = [false] ∧
    B10 r nw q E nf L dout (lp (sm 2)) = regTape (2 * nf + 2) 0 ∧ B10 r nw q E nf L dout (lp (sm 3)) = regTape (2 * nf + 2) 0 ∧
    B10 r nw q E nf L dout (lp (sm 4)) = regTape (2 * nf + 2) 0 ∧ B10 r nw q E nf L dout (lp (sm 5)) = [false] ∧
    B10 r nw q E nf L dout (lp (sm 6)) = regTape (2 * nf + 2) 0 ∧ B10 r nw q E nf L dout (lp (sm 7)) = regTape (2 * nf + 2) 0 ∧
    B10 r nw q E nf L dout (lp (sm 8)) = List.replicate (capP nw + capP nw) true ∧
    B10 r nw q E nf L dout (lp (sm 9)) = List.replicate (capP nw + capP nw + 2) false ∧
    B10 r nw q E nf L dout (lp (sm 10)) = List.replicate (capP nw + 0 + 2) false := by
  have up : ∀ k : Fin 11, k ≠ 1 → k ≠ 5 → B10 r nw q E nf L dout (lp (sm k)) = B7 r nw q E nf L dout (lp (sm k)) := by
    intro k h1 h5
    rw [B10, Function.update_of_ne (lp_ne_xs _ _), Function.update_of_ne (lp_ne _ _ (sm_ne _ _ h5)),
      Function.update_of_ne (lp_ne _ _ (sm_ne _ _ h1))]
  have sd : ∀ k : Fin 11, k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 7 → FrontFill.side (xs 8) tgtS (lp (sm k)) := by
    intro k hk; left; rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
  have b7s : ∀ k : Fin 11, k ≠ 2 → k ≠ 3 → k ≠ 4 → k ≠ 6 → k ≠ 7 →
      B7 r nw q E nf L dout (lp (sm k)) = B6 r nw q E nf L dout (lp (sm k)) := by
    intro k h2 h3 h4 h6 h7; rw [B7, if_neg (side_lp_sm k h2 h3 h4 h6 h7)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [up _ (by decide) (by decide), b7s _ (by decide) (by decide) (by decide) (by decide) (by decide),
      B6_nw _ _ _ _ _ _ _ _ (not_isW_lp_sm _ (by decide) (by decide) (by decide)), B2_lp, if_pos rfl]
  · rw [B10, Function.update_of_ne (lp_ne_xs _ _), Function.update_of_ne (lp_ne _ _ (sm_ne _ _ (by decide))),
      Function.update_self]
  · rw [up _ (by decide) (by decide), B7, if_pos (sd _ (by decide)), regTape_zero]
  · rw [up _ (by decide) (by decide), B7, if_pos (sd _ (by decide)), regTape_zero]
  · rw [up _ (by decide) (by decide), B7, if_pos (sd _ (by decide)), regTape_zero]
  · rw [B10, Function.update_of_ne (lp_ne_xs _ _), Function.update_self]
  · rw [up _ (by decide) (by decide), B7, if_pos (sd _ (by decide)), regTape_zero]
  · rw [up _ (by decide) (by decide), B7, if_pos (sd _ (by decide)), regTape_zero]
  · rw [up _ (by decide) (by decide), b7s _ (by decide) (by decide) (by decide) (by decide) (by decide), B6,
      Function.update_of_ne (lp_ne _ _ (sm_ne _ _ (by decide))), Function.update_self]
  · rw [up _ (by decide) (by decide), b7s _ (by decide) (by decide) (by decide) (by decide) (by decide), B6,
      Function.update_self]
  · rw [up _ (by decide) (by decide), b7s _ (by decide) (by decide) (by decide) (by decide) (by decide), B6,
      Function.update_of_ne (lp_ne _ _ (sm_ne _ _ (by decide))), Function.update_of_ne (lp_ne _ _ (sm_ne _ _ (by decide))),
      B5_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne_xs _ _), B4_nw _ _ _ _ _ _ _ _ (lp_ne _ _ (sm_ne_dm _ _)) (lp_ne_xs _ _),
      B3, Function.update_self]

section Idx
variable (r' : List Bool) (P H cap pg J bad : ℕ) (cond : Bool) (q' W L : ℕ) (one out : List Bool)
  (pv : Fin 1703 → List Bool)
theorem smA_0 : smA r' P H cap pg J bad cond 0 = frame r' := rfl
theorem smA_1 : smA r' P H cap pg J bad cond 1 = [false] := rfl
theorem smA_2 : smA r' P H cap pg J bad cond 2 = regTape cap pg := rfl
theorem smA_3 : smA r' P H cap pg J bad cond 3 = regTape cap 0 := rfl
theorem smA_4 : smA r' P H cap pg J bad cond 4 = regTape cap 0 := rfl
theorem smA_7 : smA r' P H cap pg J bad cond 7 = regTape cap bad := rfl
theorem smA_8 : smA r' P H cap pg J bad cond 8 = List.replicate H true := rfl
theorem smA_9 : smA r' P H cap pg J bad cond 9 = List.replicate (H + 2) false := rfl
theorem smA_10 : smA r' P H cap pg J bad cond 10 = List.replicate (P + 2) false := rfl
end Idx

theorem tm_off_jm : ∀ j : Fin 4, ∀ k : Fin 5, tmap k ≠ jmap j := by
  intro j k
  fin_cases j <;> fin_cases k
  all_goals first
    | exact xs_ne _ _ (by decide)
    | exact xs_ne_lp _ _
    | exact lp_ne_xs _ _
    | exact lp_ne _ _ (dm_ne_sm _ _)

/-- **The atom stage**: from the rest `frame r` on the loop's rest tape and `1^{|w|}`, `1^q`, `1^E`, `1^{nf}`, the
stage's verdict register (the loop's `BAD`, tape `lp (sm 7)`) holds `verdictOf …`: `0` exactly when every one of the
`E` entries' atoms passes the Theorem 2.5 repository's decoder at arity `q`. -/
theorem atoms_stage (m : Mode) (hE : 1 ≤ E) (pos : ℕ → ℕ) (pay : ℕ → List Bool) (hpos0 : pos 0 = 0)
    (hent : ∀ j, j < E → ∃ b x rest, r.drop (pos j) =
      FrontEntriesRef.gridWord b x ++ (List.replicate (pay j).length true ++ false :: pay j) ++ rest)
    (hk : ∀ j, j < E → 1 ≤ (pay j).length) (hpos : ∀ j, j < E → pos (j + 1) = pos j + 2 * (pay j).length + 5)
    (hP : ∀ j, j < E → 2 * (pay j).length + 1 ≤ capP nw)
    (hC : ∀ j, j < E → CloseoutRowsCircuitCapacity.capacity (pay j).length ≤ capP nw)
    (hcap : ∀ j, j < E → 2 * (pos j + 2 * (pay j).length + 5) + 2 ≤ 2 * nf + 2)
    (hq : q + 3 ≤ 2 * nf + 2) (hEc : E + 1 ≤ 2 * nf + 2)
    (Kc Kd : ℕ) (hKc : ∀ j, j < E → 70 * ((pay j).length + 2) ≤ Kc)
    (hKd : ∀ j, j < E → CloseoutRowsCircuitWholeBudget.budget (capP nw) (pay j).length ≤ Kd) :
    ∃ H' A', Step (stageM m) (setupCost nw nf L + 1 + (40 * (q + 2) + 1 + ((20 * E + 20) + 1 +
        (roundsOf q (capP nw) L m E pay * (roundCost (capP nw) (capP nw + capP nw) Kc Kd + 2) + 1))))
        (fun _ => 0) (sIn r nw q E nf L) H' A' ∧
      A' (lp (sm 7)) = regTape (2 * nf + 2) (verdictOf q (capP nw) L m E pay) ∧
      H' (lp (sm 7)) = verdictOf q (capP nw) L m E pay := by
  set cap := 2 * nf + 2 with hcapd
  obtain ⟨dout, -, -, gs⟩ := setup_ready r nw q E nf L
  have s1 := step_of_ready gs
  obtain ⟨x1, x2, x11, x9, x10, x12⟩ := B10_xs_in r nw q E nf L dout
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩ := B10_sm r nw q E nf L dout
  -- the template
  have ht := (WExec.exec cap (FrontTemplate.tmpl_spec cap q false hq)).step
  have s2 := Step.dockAt ht tmap tmap_inj (fun _ => 0) (B10 r nw q E nf L dout) (by intro j; fin_cases j <;> rfl)
    (by
      intro j; fin_cases j
      · exact x1
      · exact x11
      · show B10 r nw q E nf L dout (lp (dm 1674)) = []
        rw [B10_dm, if_neg (by decide), if_neg (by decide)]
      · exact x9
      · exact x10)
  -- the count
  have hc := (WExec.exec cap (cnt_spec cap E hEc false)).step
  have tm_off := tm_off_jm
  set tf : WState 1 2 := ⟨![0, 1], ![List.replicate q true, UnaryTemplate.tape q], ![0, 1], false⟩ with htf
  set H11 := dockH tmap (fun _ => 0) (wenc cap tf).H with hH11
  set B11 := install tmap (B10 r nw q E nf L dout) (wenc cap tf).A with hB11
  have s3 := Step.dockAt hc jmap jmap_inj H11 B11
    (by intro j; rw [hH11, dockH_other _ _ _ _ (fun k => tm_off j k)]; fin_cases j <;> rfl)
    (by
      intro j; rw [hB11, install_other _ _ _ _ (fun k => tm_off j k)]; fin_cases j
      · exact x2
      · exact m5
      · exact m6
      · exact x12)
  -- the loop
  obtain ⟨Hn, An, hl, hv7, hh7⟩ := atoms_loop r (capP nw) (capP nw + capP nw) q (capP nw) L cap m E hE pos pay
    hent hk hpos hP hC (by have := capP_pos nw; omega) hcap (by omega) (by omega) Kc Kd hKc hKd [] (fun _ => [])
    (by simp) (by simp)
  set jf : WState 0 2 := ⟨![0], ![List.replicate E true], ![E, 0], decide (E ≠ 0)⟩ with hjf
  set H12 := dockH jmap H11 (wenc cap jf).H with hH12
  set B12 := install jmap B11 (wenc cap jf).A with hB12
  have jm_dm : ∀ (i : Fin 1703) (j : Fin 4), jmap j ≠ lp (dm i) := by
    intro i j; fin_cases j
    · exact xs_ne_lp _ _
    · exact lp_ne _ _ (sm_ne_dm _ _)
    · exact lp_ne _ _ (sm_ne_dm _ _)
    · exact xs_ne_lp _ _
  have tm_dm : ∀ (i : Fin 1703) (k : Fin 5), i ≠ 1674 → tmap k ≠ lp (dm i) := by
    intro i k hi; fin_cases k
    · exact xs_ne_lp _ _
    · exact xs_ne_lp _ _
    · exact lp_ne _ _ (dm_ne _ _ (Ne.symm hi))
    · exact xs_ne_lp _ _
    · exact xs_ne_lp _ _
  have tm_sm : ∀ (k : Fin 11) (j : Fin 5), tmap j ≠ lp (sm k) := by
    intro k j; fin_cases j
    · exact xs_ne_lp _ _
    · exact xs_ne_lp _ _
    · exact lp_ne _ _ (dm_ne_sm _ _)
    · exact xs_ne_lp _ _
    · exact xs_ne_lp _ _
  have hA12 : ∀ y : Fin AT, B12 (lp y) =
      bankA r (capP nw) (capP nw + capP nw) q (capP nw) L cap [] [] (fun _ => []) (2 * pos 0) E 0 true y := by
    intro y
    rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [hB12, install_other _ _ _ _ (fun j => jm_dm i j), hB11, bankA_dm]
      by_cases h74 : i = 1674
      · subst h74
        rw [show lp (dm 1674) = tmap 2 from rfl, install_slot _ tmap_inj]
        simp [decA]; rfl
      · rw [install_other _ _ _ _ (fun k => tm_dm i k h74), B10_dm]
        unfold decA
        have h74' : i.val ≠ 1674 := fun h => h74 (Fin.ext h)
        by_cases h1 : i.val = 1
        · have : i = 1 := Fin.ext h1
          subst this; simp
        by_cases h88 : i.val = 1688
        · have : i = 1688 := Fin.ext h88
          subst this; simp
        by_cases h94 : i.val = 1694
        · have : i = 1694 := Fin.ext h94
          subst this; simp
        by_cases h98 : i.val = 1698
        · have : i = 1698 := Fin.ext h98
          subst this; simp
        by_cases h99 : i.val = 1699
        · have : i = 1699 := Fin.ext h99
          subst this; simp
        have hn : ¬ (i = 1694 ∨ i = 1698) := by
          rintro (h | h)
          · exact h94 (by rw [h]; rfl)
          · exact h98 (by rw [h]; rfl)
        have hn9 : i ≠ 1699 := fun h => h99 (by rw [h]; rfl)
        rw [if_neg hn, if_neg hn9]
        simp [h1, h74', h88, h94, h98, h99]
    · rw [bankA_sm]
      by_cases h5 : k = 5
      · subst h5
        rw [hB12, show lp (sm 5) = jmap 1 from rfl, install_slot _ jmap_inj]
        show (wenc cap jf).A cTape = _
        rw [FrontKit.wenc_cell]
        simp only [hjf, smA]
        have hE0 : E ≠ 0 := by omega
        simp [hE0]
      by_cases h6 : k = 6
      · subst h6
        rw [hB12, show lp (sm 6) = jmap 2 from rfl, install_slot _ jmap_inj]
        show (wenc cap jf).A (rTape (0 : Fin 2)) = _
        rw [wenc_A_r]
        simp [smA, hjf]
      have hj : ∀ j : Fin 4, jmap j ≠ lp (sm k) := by
        intro j; fin_cases j
        · exact xs_ne_lp _ _
        · exact lp_ne _ _ (sm_ne _ _ (Ne.symm h5))
        · exact lp_ne _ _ (sm_ne _ _ (Ne.symm h6))
        · exact xs_ne_lp _ _
      rw [hB12, install_other _ _ _ _ hj, hB11, install_other _ _ _ _ (tm_sm k)]
      fin_cases k
      · show B10 r nw q E nf L dout (lp (sm 0)) = smA _ _ _ _ _ _ _ _ 0; rw [m0, smA_0]
      · show B10 r nw q E nf L dout (lp (sm 1)) = smA _ _ _ _ _ _ _ _ 1; rw [m1, smA_1]
      · show B10 r nw q E nf L dout (lp (sm 2)) = smA _ _ _ _ _ _ _ _ 2; rw [m2, smA_2, hpos0]
      · show B10 r nw q E nf L dout (lp (sm 3)) = smA _ _ _ _ _ _ _ _ 3; rw [m3, smA_3]
      · show B10 r nw q E nf L dout (lp (sm 4)) = smA _ _ _ _ _ _ _ _ 4; rw [m4, smA_4]
      · exact absurd rfl h5
      · exact absurd rfl h6
      · show B10 r nw q E nf L dout (lp (sm 7)) = smA _ _ _ _ _ _ _ _ 7; rw [m7, smA_7]
      · show B10 r nw q E nf L dout (lp (sm 8)) = smA _ _ _ _ _ _ _ _ 8; rw [m8, smA_8]
      · show B10 r nw q E nf L dout (lp (sm 9)) = smA _ _ _ _ _ _ _ _ 9; rw [m9, smA_9]
      · show B10 r nw q E nf L dout (lp (sm 10)) = smA _ _ _ _ _ _ _ _ 10; rw [m10, smA_10, Nat.add_zero]

  have hH12 : ∀ y : Fin AT, H12 (lp y) = bankH (CloseoutRowsCircuitColdEntry.heads []) (2 * pos 0) E 0 y := by
    intro y
    rcases at_cases y with ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [hH12, dockH_other _ _ _ _ (fun j => jm_dm i j), hH11, bankH_dm]
      by_cases h74 : i = 1674
      · subst h74
        rw [show lp (dm 1674) = tmap 2 from rfl, dockH_slot _ tmap_inj]
        rfl
      · rw [dockH_other _ _ _ _ (fun k => tm_dm i k h74)]
        have h74' : i.val ≠ 1674 := fun h => h74 (Fin.ext h)
        simp only [CloseoutRowsCircuitColdEntry.heads, CloseoutRowsCircuit.heads, Fin.ext_iff]
        split_ifs <;> simp_all
    · rw [bankH_sm]
      by_cases h5 : k = 5
      · subst h5
        rw [hH12, show lp (sm 5) = jmap 1 from rfl, dockH_slot _ jmap_inj]; rfl
      by_cases h6 : k = 6
      · subst h6
        rw [hH12, show lp (sm 6) = jmap 2 from rfl, dockH_slot _ jmap_inj]; rfl
      have hj : ∀ j : Fin 4, jmap j ≠ lp (sm k) := by
        intro j; fin_cases j
        · exact xs_ne_lp _ _
        · exact lp_ne _ _ (sm_ne _ _ (Ne.symm h5))
        · exact lp_ne _ _ (sm_ne _ _ (Ne.symm h6))
        · exact xs_ne_lp _ _
      rw [hH12, dockH_other _ _ _ _ hj, hH11, dockH_other _ _ _ _ (tm_sm k)]
      fin_cases k <;> first | (exact absurd rfl h5) | (exact absurd rfl h6) | (simp [smH, hpos0])
  have s4 := Step.dockAt hl lp lp_inj H12 B12 hH12 hA12
  refine ⟨_, _, Step.seq s1 (Step.seq s2 (Step.seq s3 s4)), ?_, ?_⟩
  · rw [install_slot _ lp_inj, hv7]
  · rw [dockH_slot _ lp_inj, hh7]

/-- The capacity covers every atom of a shorter code: `20·(nbl + 4)`, the Theorem 2.5 repository's capacity, and the frame. -/
theorem capP_covers (nw : ℕ) (p : List Bool) (hp : p.length + 1 ≤ nw) :
    20 * (natBitLength (RepairOrdinary.RadixSemantics.value p) + 4) ≤ capP nw ∧
    CloseoutRowsCircuitCapacity.capacity p.length ≤ capP nw ∧ 2 * p.length + 1 ≤ capP nw := by
  have hnb : natBitLength (RepairOrdinary.RadixSemantics.value p) ≤ p.length + 1 := by
    by_cases hne : p = []
    · subst hne; simp [RepairOrdinary.RadixSemantics.value, natBitLength]
    · have := FrontSize.nbl_value_le p hne; omega
  have hpow : nw + 1 ≤ (nw + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have hc : capP nw = 1000000000000000000000000000000 * (nw + 1) ^ 26 := by unfold capP; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; nlinarith
  · rw [hc]; unfold CloseoutRowsCircuitCapacity.capacity
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  · rw [hc]; nlinarith

end Setup


end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomStageL
