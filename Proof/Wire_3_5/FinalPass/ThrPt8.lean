import Proof.Wire_3_5.FinalPass.TermThrEval

/-! # S2 (THR per point), part 2: stage 8 of a THR row with the answer in a register (P3:2587-2630, 3170-3178)

A word program cannot branch on the result cell, so the THR row's factor `thrTermOk` must land in a register.
`thr8I` is stage 8's THR program `thr8` (`Term`, verified) with the zero test's cell write replaced by an increment of
the digit-weight register `W` (zero at that point and untouched afterwards): **`zeroTI_spec`**, **`thr8I_spec`**:
`W = [thrTermOk p r₀ X as ws t⁺ t⁻]`, every other register `0`, every head back, the cell unchanged.
Paper quantity: the reported modular row `R̂_{g,p}(c, u, v)` (row:thr-reported, `thrRhat_eq_termOk`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Term

variable (inp : Fin 3 → List Bool) (cap : ℕ) (h0 h1 h2 : ℕ)

/-- The zero test into `W`: `W += [R = 0]`, then `R`, `Q` cleared. -/
def zeroTI : HProg := .seq (.ifr qR .skip (.inc qW)) (.seq (RM.clear qR) (RM.clear qQ))

theorem zeroTI_spec (x y z t s u f1 f2 f3 : ℕ) (c : Bool) (p r : ℕ) (hr : r < p) (hp : p ≤ cap) :
    RExec inp cap zeroTI (S9 h0 h1 h2 x y z r (p - r) 0 t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x y z 0 0 (decide (r = 0)).toNat t s u f1 f2 f3 c) (3 * p + 8) := by
  have d1 : RExec inp cap (.ifr qR .skip (.inc qW)) (S9 h0 h1 h2 x y z r (p - r) 0 t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x y z r (p - r) (decide (r = 0)).toNat t s u f1 f2 f3 c) 4 := by
    by_cases h : r = 0
    · have e := RExec.inc (inp := inp) (cap := cap) qW (S9 h0 h1 h2 x y z r (p - r) 0 t s u f1 f2 f3 c)
        (by show 0 < cap; omega)
      rw [S9_setv_W] at e
      exact RExec.cast inp cap (RExec.ifrF (by show r = 0; exact h) e) (by simp [h]) (by omega)
    · exact RExec.cast inp cap (RExec.ifrT (by show r ≠ 0; exact h) (RExec.skip _)) (by simp [h]) (by omega)
  have d2 := clear_spec inp cap qR r (S9 h0 h1 h2 x y z r (p - r) (decide (r = 0)).toNat t s u f1 f2 f3 c) rfl
    (by show r ≤ cap; omega)
  rw [S9_setv_R] at d2
  have d3 := clear_spec inp cap qQ (p - r) (S9 h0 h1 h2 x y z 0 (p - r) (decide (r = 0)).toNat t s u f1 f2 f3 c) rfl
    (by show p - r ≤ cap; omega)
  rw [S9_setv_Q] at d3
  exact RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 d3)) rfl (by omega)

/-- **Stage 8 of a THR row, the answer in `W`.** -/
def thr8I : HProg :=
  .seq initT (.seq cornerL (.seq digL (.seq zeroTI (.seq (RM.rewind 0 qX) (.seq (RM.rewind 1 qY) (RM.rewind 2 qZ))))))

/-- `thr8I`'s step bound. -/
def costTI (p r0 L : ℕ) (as ws tp tm : List ℕ) : ℕ := costT p r0 L as ws tp tm + 2

/-- **`thr8I`'s run**: as `thr8_spec`, with `W = [thrTermOk p r₀ X as ws t⁺ t⁻]` and the cell unchanged. -/
theorem thr8I_spec (X : List Bool) (as ws tp tm : List ℕ) (L p r0 : ℕ) (c : Bool) (rest0 rest1 rest2 : List Bool)
    (hl : X.length = 4 * L) (has : as.length = L) (h1l : ws.length = tp.length) (h2l : ws.length = tm.length)
    (hr0 : r0 < p) (hX : (inp 0).drop h0 = frameP X ++ false :: rest0)
    (hT : (inp 1).drop h1 = rowWord p r0 as ws ++ rest1) (hR : (inp 2).drop h2 = repWord tp tm ++ rest2)
    (hcap : capT p r0 L as ws tp tm ≤ cap) :
    RExec inp cap thr8I (S9 h0 h1 h2 0 0 0 0 0 0 0 0 0 0 0 0 c)
      (S9 h0 h1 h2 0 0 0 0 0 (thrTermOk p r0 X as ws tp tm).toNat 0 0 0 0 0 0 c) (costTI p r0 L as ws tp tm) := by
  unfold capT at hcap
  have hp : p ≤ cap := by omega
  have hT1 : (inp 1).drop h1 = ListEval.unary p ++ ListEval.unary r0 ++
      (as.flatMap ListEval.unary ++ (digWord ws ++ false :: rest1)) := by
    rw [hT]; simp [rowWord, List.append_assoc]
  have d1 := initT_spec inp cap h0 h1 h2 _ p r0 c hr0 hT1 (by omega)
  have hT2 : (inp 1).drop (h1 + (p + r0 + 2)) = as.flatMap ListEval.unary ++ (digWord ws ++ false :: rest1) := by
    rw [← List.drop_drop, hT1]
    apply List.drop_left'
    simp only [ListEval.unary, List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega
  have hX0 : (inp 0).drop (h0 + 0) = frameP X ++ false :: rest0 := by simpa using hX
  obtain ⟨r1, hr1, e1, d2⟩ := cornerL_spec inp cap h0 h1 h2 rest0 (digWord ws ++ false :: rest1) p 0 0 0 0 0 c hp L X as 0
    (p + r0 + 2) r0 hl has hX0 hT2 hr0 (by omega) (by omega)
  have hT3 : (inp 1).drop (h1 + (p + r0 + 2 + as.sum + L)) = digWord ws ++ false :: rest1 := by
    rw [show h1 + (p + r0 + 2 + as.sum + L) = h1 + (p + r0 + 2) + (as.flatMap ListEval.unary).length by
      rw [flatMap_unary_length, has]; ring]
    exact ListEval.drop_add_of_append hT2
  have hR0 : (inp 2).drop (h2 + 0) = repWord tp tm ++ rest2 := by simpa using hR
  obtain ⟨r2, hr2, e2, d3⟩ := digL_spec inp cap h0 h1 h2 rest1 rest2 p (0 + 8 * L) c hp ws tp tm
    (p + r0 + 2 + as.sum + L) 0 r1 h1l h2l hT3 hR0 hr1 (by omega) (by omega)
  have d4 := zeroTI_spec inp cap h0 h1 h2 (0 + 8 * L) (p + r0 + 2 + as.sum + L + ws.sum + 2 * ws.length)
    (0 + tp.sum + tm.sum + 2 * tp.length) 0 0 0 0 0 0 c p r2 hr2 hp
  have d5 := rewind_spec inp cap 0 qX (0 + 8 * L) (S9 h0 h1 h2 (0 + 8 * L) (p + r0 + 2 + as.sum + L + ws.sum +
    2 * ws.length) (0 + tp.sum + tm.sum + 2 * tp.length) 0 0 (decide (r2 = 0)).toNat 0 0 0 0 0 0 c) rfl
    (by show 0 + 8 * L ≤ cap; omega)
  rw [S9_rew0] at d5
  have d6 := rewind_spec inp cap 1 qY (p + r0 + 2 + as.sum + L + ws.sum + 2 * ws.length) (S9 h0 h1 h2 0 (p + r0 + 2 +
    as.sum + L + ws.sum + 2 * ws.length) (0 + tp.sum + tm.sum + 2 * tp.length) 0 0 (decide (r2 = 0)).toNat 0 0 0 0 0 0
    c) rfl (by show p + r0 + 2 + as.sum + L + ws.sum + 2 * ws.length ≤ cap; omega)
  rw [S9_rew1] at d6
  have d7 := rewind_spec inp cap 2 qZ (0 + tp.sum + tm.sum + 2 * tp.length) (S9 h0 h1 h2 0 0
    (0 + tp.sum + tm.sum + 2 * tp.length) 0 0 (decide (r2 = 0)).toNat 0 0 0 0 0 0 c) rfl
    (by show 0 + tp.sum + tm.sum + 2 * tp.length ≤ cap; omega)
  rw [S9_rew2] at d7
  have hres : decide (r2 = 0) = thrTermOk p r0 X as ws tp tm := by
    haveI : NeZero p := ⟨by omega⟩
    unfold thrTermOk
    rw [← e1, ← e2]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_iff]
    rw [ZMod.natCast_eq_zero_iff]
    constructor
    · rintro rfl; exact dvd_zero p
    · intro h; exact Nat.eq_zero_of_dvd_of_lt h hr2
  rw [hres] at d7 d6 d5 d4
  unfold costTI costT
  exact RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 (RExec.seq d3 (RExec.seq d4 (RExec.seq d5 (RExec.seq d6
    d7)))))) (by s9_args) (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
