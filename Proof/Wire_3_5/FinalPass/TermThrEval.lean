import Proof.Wire_3_5.FinalPass.TermThrRef
import Proof.Wire_3_5.FinalPass.TermEval

/-! # Final pass, stage 8 (THR): the reported modular row at one point (P3:2587-2630, 3170-3178)

The per-point evaluator of one THR row `(g,p)` (`thrTermOk`, `Proof.Wire_3_5.FinalPass.TermThrRef`): a register program
`thr8` over three read-only streams, the framed occurrences' corner word `frame X` (stream 0, from any `h₀`), the row's
word `rowWord p r₀ as ws` (stream 1, from any `h₁`: `1^p 0`, `1^{r₀} 0`, one unary coefficient `1^{a_i} 0` per
occurrence, then `1 1^{w_d} 0` per digit and a final `0`), and the reports word `repWord t⁺ t⁻` (stream 2, from any
`h₂`: `1^{t_d^+} 0 1^{t_d^−} 0` per digit). A counter `R` modulo `p` (with `Q = p − R`) accumulates
1. `r₀`;
2. per occurrence `i`, `a_i` times `#1 + #2 − #3` of its corners (flags `F₁, F₂, F₃`);
3. per digit `d`, `w_d` times `t_d^+ − t_d^−`;
and the cell becomes `[R = 0]`. Every register ends at `0`, every head returns (loop-safe).
**`thr8_spec`**: the cell becomes `thrTermOk p r₀ X as ws t⁺ t⁻`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Term
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout -/

scoped notation "qR" => (0 : Fin 12)
scoped notation "qQ" => (1 : Fin 12)
scoped notation "qW" => (2 : Fin 12)
scoped notation "qT" => (3 : Fin 12)
scoped notation "qS" => (4 : Fin 12)
scoped notation "qU" => (5 : Fin 12)
scoped notation "qA" => (6 : Fin 12)
scoped notation "qB" => (7 : Fin 12)
scoped notation "qC" => (8 : Fin 12)
scoped notation "qX" => (9 : Fin 12)
scoped notation "qY" => (10 : Fin 12)
scoped notation "qZ" => (11 : Fin 12)

abbrev HProg := RM 2 12

/-- The state at a phase boundary: stream origins `h₀, h₁, h₂` and offsets `x, y, z` (also held by the counters `X, Y,
Z`), the counter `r` and its complement `q`, the digit weight `w`, the reports `t, s`, the scratch `u`, the corner flags
`f₁, f₂, f₃`, the cell. -/
def S9 (h0 h1 h2 x y z r q w t s u f1 f2 f3 : ℕ) (c : Bool) : RState 2 12 :=
  ⟨![h0 + x, h1 + y, h2 + z], ![r, q, w, t, s, u, f1, f2, f3, x, y, z], c⟩

/-- Close an equality of phase states. -/
syntax "s9_eq" : tactic
macro_rules
  | `(tactic| s9_eq) => `(tactic| (refine RState.eq ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [S9]; done) | (simp [S9] <;> omega))
        | rfl
        | (simp; done)))

/-- Close an equality of phase states argument by argument. -/
macro "s9_args" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (simp; done) | (simp <;> omega)))

section Upd
variable (h0 h1 h2 x y z r q w t s u f1 f2 f3 : ℕ) (c : Bool)

@[simp] theorem S9_val_R : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qR = r := rfl
@[simp] theorem S9_val_Q : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qQ = q := rfl
@[simp] theorem S9_val_W : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qW = w := rfl
@[simp] theorem S9_val_T : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qT = t := rfl
@[simp] theorem S9_val_S : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qS = s := rfl
@[simp] theorem S9_val_U : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qU = u := rfl
@[simp] theorem S9_val_A : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qA = f1 := rfl
@[simp] theorem S9_val_B : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qB = f2 := rfl
@[simp] theorem S9_val_C : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qC = f3 := rfl
@[simp] theorem S9_val_X : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qX = x := rfl
@[simp] theorem S9_val_Y : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qY = y := rfl
@[simp] theorem S9_val_Z : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qZ = z := rfl

theorem S9_setv_R (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qR v =
    S9 h0 h1 h2 x y z v q w t s u f1 f2 f3 c := by s9_eq
theorem S9_setv_Q (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qQ v =
    S9 h0 h1 h2 x y z r v w t s u f1 f2 f3 c := by s9_eq
theorem S9_setv_W (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qW v =
    S9 h0 h1 h2 x y z r q v t s u f1 f2 f3 c := by s9_eq
theorem S9_setv_T (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qT v =
    S9 h0 h1 h2 x y z r q w v s u f1 f2 f3 c := by s9_eq
theorem S9_setv_S (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qS v =
    S9 h0 h1 h2 x y z r q w t v u f1 f2 f3 c := by s9_eq
theorem S9_setv_U (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qU v =
    S9 h0 h1 h2 x y z r q w t s v f1 f2 f3 c := by s9_eq
theorem S9_setv_A (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qA v =
    S9 h0 h1 h2 x y z r q w t s u v f2 f3 c := by s9_eq
theorem S9_setv_B (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qB v =
    S9 h0 h1 h2 x y z r q w t s u f1 v f3 c := by s9_eq
theorem S9_setv_C (v : ℕ) : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qC v =
    S9 h0 h1 h2 x y z r q w t s u f1 f2 v c := by s9_eq

theorem S9_fwd0 : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).seth 0 ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 0 + 1)).setv
    qX ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qX + 1) = S9 h0 h1 h2 (x + 1) y z r q w t s u f1 f2 f3 c := by
  s9_eq
theorem S9_fwd1 : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).seth 1 ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 1 + 1)).setv
    qY ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).val qY + 1) = S9 h0 h1 h2 x (y + 1) z r q w t s u f1 f2 f3 c := by
  s9_eq

theorem S9_rew0 : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qX 0).seth 0
    ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 0 - x) = S9 h0 h1 h2 0 y z r q w t s u f1 f2 f3 c := by
  s9_eq
theorem S9_rew1 : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qY 0).seth 1
    ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 1 - y) = S9 h0 h1 h2 x 0 z r q w t s u f1 f2 f3 c := by
  s9_eq
theorem S9_rew2 : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).setv qZ 0).seth 2
    ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 2 - z) = S9 h0 h1 h2 x y 0 r q w t s u f1 f2 f3 c := by
  s9_eq

@[simp] theorem S9_sh0 : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 0 = h0 + x := rfl
@[simp] theorem S9_sh1 : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 1 = h1 + y := rfl
@[simp] theorem S9_sh2 : (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).sh 2 = h2 + z := rfl

theorem S9_mv1 (v : ℕ) : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).seth 1 (h1 + v)).setv qY v =
    S9 h0 h1 h2 x v z r q w t s u f1 f2 f3 c := by
  s9_eq
theorem S9_mv2 (v : ℕ) : ((S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c).seth 2 (h2 + v)).setv qZ v =
    S9 h0 h1 h2 x y v r q w t s u f1 f2 f3 c := by
  s9_eq

end Upd

variable (inp : Fin 3 → List Bool) (cap : ℕ) (h0 h1 h2 : ℕ)

theorem fwd0_spec (x y z r q w t s u f1 f2 f3 : ℕ) (c : Bool) (hx : x < cap) :
    RExec inp cap (RM.fwdC 0 qX) (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
      (S9 h0 h1 h2 (x + 1) y z r q w t s u f1 f2 f3 c) 5 := by
  have h := fwdC_spec inp cap 0 qX (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c) hx
  rwa [S9_fwd0] at h

theorem fwd1_spec (x y z r q w t s u f1 f2 f3 : ℕ) (c : Bool) (hy : y < cap) :
    RExec inp cap (RM.fwdC 1 qY) (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x (y + 1) z r q w t s u f1 f2 f3 c) 5 := by
  have h := fwdC_spec inp cap 1 qY (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c) hy
  rwa [S9_fwd1] at h

/-! ## The counter modulo `p` -/

/-- `R := R + 1 (mod p)`. -/
def incM : HProg := .seq (.dec qQ) (.seq (.inc qR) (.ifr qQ .skip (RM.move qR qQ)))

/-- `R := R − 1 (mod p)`. -/
def decM : HProg := .ifr qR (.seq (.dec qR) (.inc qQ)) (.seq (RM.move qQ qR) (.seq (.dec qR) (.inc qQ)))

theorem incM_spec (p x y z w t s u f1 f2 f3 : ℕ) (c : Bool) (r : ℕ) (hr : r < p) (hp : p ≤ cap) :
    ∃ r', r' < p ∧ (r' : ZMod p) = r + 1 ∧
      RExec inp cap incM (S9 h0 h1 h2 x y z r (p - r) w t s u f1 f2 f3 c)
        (S9 h0 h1 h2 x y z r' (p - r') w t s u f1 f2 f3 c) (7 * p + 10) := by
  have d1 := RExec.dec (inp := inp) (cap := cap) qQ (S9 h0 h1 h2 x y z r (p - r) w t s u f1 f2 f3 c)
    (by show p - r ≤ cap; omega)
  rw [S9_val_Q, S9_setv_Q] at d1
  have d2 := RExec.inc (inp := inp) (cap := cap) qR (S9 h0 h1 h2 x y z r (p - r - 1) w t s u f1 f2 f3 c)
    (by show r < cap; omega)
  rw [S9_val_R, S9_setv_R] at d2
  by_cases hw : r + 1 < p
  · refine ⟨r + 1, hw, by push_cast; rfl, ?_⟩
    exact RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 (RExec.ifrT (by show p - r - 1 ≠ 0; omega)
      (RExec.skip _)))) (by s9_args) (by omega)
  · have hpr : r + 1 = p := by omega
    have d3 := move_spec inp cap qR qQ (by decide) (r + 1) (S9 h0 h1 h2 x y z (r + 1) (p - r - 1) w t s u f1 f2 f3 c)
      rfl (by show r + 1 ≤ cap; omega) (by show p - r - 1 + (r + 1) ≤ cap; omega)
    rw [S9_val_Q, S9_val_R, S9_setv_R, S9_setv_Q] at d3
    refine ⟨0, by omega, ?_, ?_⟩
    · rw [← Nat.cast_one, ← Nat.cast_add, hpr, ZMod.natCast_self, Nat.cast_zero]
    · exact RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 (RExec.ifrF (by show p - r - 1 = 0; omega) d3)))
        (by s9_args) (by omega)

theorem decM_spec (p x y z w t s u f1 f2 f3 : ℕ) (c : Bool) (r : ℕ) (hr : r < p) (hp : p ≤ cap) :
    ∃ r', r' < p ∧ (r' : ZMod p) = r - 1 ∧
      RExec inp cap decM (S9 h0 h1 h2 x y z r (p - r) w t s u f1 f2 f3 c)
        (S9 h0 h1 h2 x y z r' (p - r') w t s u f1 f2 f3 c) (7 * p + 10) := by
  rcases r with _ | r
  · have d1 := move_spec inp cap qQ qR (by decide) (p - 0) (S9 h0 h1 h2 x y z 0 (p - 0) w t s u f1 f2 f3 c) rfl
      (by show p - 0 ≤ cap; omega) (by show 0 + (p - 0) ≤ cap; omega)
    rw [S9_val_R, S9_val_Q, S9_setv_Q, S9_setv_R, Nat.zero_add, Nat.sub_zero] at d1
    have d2 := RExec.dec (inp := inp) (cap := cap) qR (S9 h0 h1 h2 x y z p 0 w t s u f1 f2 f3 c) (by show p ≤ cap; omega)
    rw [S9_val_R, S9_setv_R] at d2
    have d3 := RExec.inc (inp := inp) (cap := cap) qQ (S9 h0 h1 h2 x y z (p - 1) 0 w t s u f1 f2 f3 c)
      (by show 0 < cap; omega)
    rw [S9_val_Q, S9_setv_Q] at d3
    refine ⟨p - 1, by omega, ?_, ?_⟩
    · rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_zero, Nat.cast_one]
    · exact RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.seq d1 (RExec.seq d2 d3))) (by s9_args) (by omega)
  · have d1 := RExec.dec (inp := inp) (cap := cap) qR (S9 h0 h1 h2 x y z (r + 1) (p - (r + 1)) w t s u f1 f2 f3 c)
      (by show r + 1 ≤ cap; omega)
    rw [S9_val_R, S9_setv_R, Nat.add_sub_cancel] at d1
    have d2 := RExec.inc (inp := inp) (cap := cap) qQ (S9 h0 h1 h2 x y z r (p - (r + 1)) w t s u f1 f2 f3 c)
      (by show p - (r + 1) < cap; omega)
    rw [S9_val_Q, S9_setv_Q] at d2
    refine ⟨r, by omega, by push_cast; ring, ?_⟩
    exact RExec.cast inp cap (RExec.ifrT (by show r + 1 ≠ 0; omega) (RExec.seq d1 d2)) (by s9_args) (by omega)

/-! ## Reading unary fields -/

theorem unary_reads {l rest : List Bool} {p n : ℕ} (h : l.drop p = List.replicate n true ++ false :: rest) :
    (∀ k < n, readTapeBit l (p + k) = true) ∧ readTapeBit l (p + n) = false := by
  constructor
  · intro k hk
    rw [ListEval.readTapeBit_drop, h]
    unfold readTapeBit
    rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [hk]
  · rw [ListEval.readTapeBit_drop, h]
    unfold readTapeBit
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

theorem readQ_spec (x y z r q w t s u f1 f2 f3 n : ℕ) (c : Bool) (rest : List Bool)
    (h : (inp 1).drop (h1 + y) = List.replicate n true ++ false :: rest) (hy : y + n + 1 ≤ cap) (hq : q + n ≤ cap) :
    RExec inp cap (RM.readU 1 qY qQ) (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x (y + n + 1) z r (q + n) w t s u f1 f2 f3 c) (11 * n + 7) := by
  have hr := unary_reads h
  have d := readU_spec inp cap 1 qY qQ (by decide) n (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c) hr.1 hr.2 hy hq
  rw [S9_sh1, S9_val_Y, S9_val_Q, show h1 + y + n + 1 = h1 + (y + n + 1) by ring, S9_mv1, S9_setv_Q] at d
  exact d

theorem readW_spec (x y z r q w t s u f1 f2 f3 n : ℕ) (c : Bool) (rest : List Bool)
    (h : (inp 1).drop (h1 + y) = List.replicate n true ++ false :: rest) (hy : y + n + 1 ≤ cap) (hw : w + n ≤ cap) :
    RExec inp cap (RM.readU 1 qY qW) (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x (y + n + 1) z r q (w + n) t s u f1 f2 f3 c) (11 * n + 7) := by
  have hr := unary_reads h
  have d := readU_spec inp cap 1 qY qW (by decide) n (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c) hr.1 hr.2 hy hw
  rw [S9_sh1, S9_val_Y, S9_val_W, show h1 + y + n + 1 = h1 + (y + n + 1) by ring, S9_mv1, S9_setv_W] at d
  exact d

theorem readT_spec (x y z r q w t s u f1 f2 f3 n : ℕ) (c : Bool) (rest : List Bool)
    (h : (inp 2).drop (h2 + z) = List.replicate n true ++ false :: rest) (hz : z + n + 1 ≤ cap) (ht : t + n ≤ cap) :
    RExec inp cap (RM.readU 2 qZ qT) (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x y (z + n + 1) r q w (t + n) s u f1 f2 f3 c) (11 * n + 7) := by
  have hr := unary_reads h
  have d := readU_spec inp cap 2 qZ qT (by decide) n (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c) hr.1 hr.2 hz ht
  rw [S9_sh2, S9_val_Z, S9_val_T, show h2 + z + n + 1 = h2 + (z + n + 1) by ring, S9_mv2, S9_setv_T] at d
  exact d

theorem readS_spec (x y z r q w t s u f1 f2 f3 n : ℕ) (c : Bool) (rest : List Bool)
    (h : (inp 2).drop (h2 + z) = List.replicate n true ++ false :: rest) (hz : z + n + 1 ≤ cap) (hs : s + n ≤ cap) :
    RExec inp cap (RM.readU 2 qZ qS) (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
      (S9 h0 h1 h2 x y (z + n + 1) r q w t (s + n) u f1 f2 f3 c) (11 * n + 7) := by
  have hr := unary_reads h
  have d := readU_spec inp cap 2 qZ qS (by decide) n (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c) hr.1 hr.2 hz hs
  rw [S9_sh2, S9_val_Z, S9_val_S, show h2 + z + n + 1 = h2 + (z + n + 1) by ring, S9_mv2, S9_setv_S] at d
  exact d

/-! ## Phase 1: `R := r₀`, `Q := p − r₀` -/

/-- Read `1^{r₀} 0` into `R`, taking the units from `Q`. -/
def r0L : HProg := .whs 1 (.seq (RM.fwdC 1 qY) (.seq (.inc qR) (.dec qQ)))

theorem r0L_spec (rest : List Bool) (x z w t s u f1 f2 f3 : ℕ) (c : Bool) :
    ∀ (k y r q : ℕ), (inp 1).drop (h1 + y) = List.replicate k true ++ false :: rest → k ≤ q → q ≤ cap →
      y + k ≤ cap → r + k ≤ cap →
      RExec inp cap r0L (S9 h0 h1 h2 x y z r q w t s u f1 f2 f3 c)
        (S9 h0 h1 h2 x (y + k) z (r + k) (q - k) w t s u f1 f2 f3 c) (13 * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro y r q h _ _ _ _
    have hr : readTapeBit (inp 1) (h1 + y) = false := ListEval.read_of_cons (by simpa using h)
    exact RExec.cast inp cap (RExec.whsF hr) (by s9_args) le_rfl
  | succ k ih =>
    intro y r q h hk hq hy hr
    have h0' : (inp 1).drop (h1 + y) = true :: (List.replicate k true ++ false :: rest) := by
      simpa [List.replicate_succ] using h
    have hb : readTapeBit (inp 1) (h1 + y) = true := ListEval.read_of_cons h0'
    have h1' : (inp 1).drop (h1 + (y + 1)) = List.replicate k true ++ false :: rest := by
      rw [← Nat.add_assoc]; exact ListEval.drop_succ_of_cons h0'
    have d1 := fwd1_spec inp cap h0 h1 h2 x y z r q w t s u f1 f2 f3 c (by omega)
    have d2 := RExec.inc (inp := inp) (cap := cap) qR (S9 h0 h1 h2 x (y + 1) z r q w t s u f1 f2 f3 c)
      (by show r < cap; omega)
    rw [S9_val_R, S9_setv_R] at d2
    have d3 := RExec.dec (inp := inp) (cap := cap) qQ (S9 h0 h1 h2 x (y + 1) z (r + 1) q w t s u f1 f2 f3 c)
      (by show q ≤ cap; omega)
    rw [S9_val_Q, S9_setv_Q] at d3
    have ih' := ih (y + 1) (r + 1) (q - 1) h1' (by omega) (by omega) (by omega) (by omega)
    exact RExec.cast inp cap (RExec.whsT hb (RExec.seq d1 (RExec.seq d2 d3)) ih') (by s9_args) (by omega)

/-- Phase 1: `Q := p`, then `R := r₀`, `Q := p − r₀`. -/
def initT : HProg := .seq (RM.readU 1 qY qQ) (.seq r0L (RM.fwdC 1 qY))

theorem initT_spec (rest : List Bool) (p r0 : ℕ) (c : Bool) (hr0 : r0 < p)
    (h : (inp 1).drop h1 = ListEval.unary p ++ ListEval.unary r0 ++ rest) (hcap : p + r0 + 2 ≤ cap) :
    RExec inp cap initT (S9 h0 h1 h2 0 0 0 0 0 0 0 0 0 0 0 0 c)
      (S9 h0 h1 h2 0 (p + r0 + 2) 0 r0 (p - r0) 0 0 0 0 0 0 0 c) (11 * p + 13 * r0 + 16) := by
  have hp : (inp 1).drop (h1 + 0) = List.replicate p true ++ false :: (ListEval.unary r0 ++ rest) := by
    simpa [ListEval.unary] using h
  have d1 := readQ_spec inp cap h0 h1 h2 0 0 0 0 0 0 0 0 0 0 0 0 p c _ hp (by omega) (by omega)
  have hr : (inp 1).drop (h1 + (0 + p + 1)) = List.replicate r0 true ++ false :: rest := by
    have := ListEval.drop_add_of_append hp
    simp only [List.length_replicate] at this
    have := ListEval.drop_succ_of_cons this
    rw [show h1 + (0 + p + 1) = h1 + 0 + p + 1 by ring, this]
    simp [ListEval.unary]
  have d2 := r0L_spec inp cap h0 h1 h2 rest 0 0 0 0 0 0 0 0 0 c r0 (0 + p + 1) 0 (0 + p) hr (by omega) (by omega)
    (by omega) (by omega)
  have d3 := fwd1_spec inp cap h0 h1 h2 0 (0 + p + 1 + r0) 0 (0 + r0) (0 + p - r0) 0 0 0 0 0 0 0 c (by omega)
  exact RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 d3)) (by s9_args) (by omega)

/-! ## The zero test -/

/-! ## Phase 2: the occurrences' corners -/

theorem setA_spec (x y z r q w t s u : ℕ) (c b : Bool) (hb : readTapeBit (inp 0) (h0 + x) = b) (hcap : 1 ≤ cap) :
    RExec inp cap (.ifs 0 (.inc qA) .skip) (S9 h0 h1 h2 x y z r q w t s u 0 0 0 c)
      (S9 h0 h1 h2 x y z r q w t s u b.toNat 0 0 c) 4 := by
  cases b
  · exact RExec.cast inp cap (RExec.ifsF hb (RExec.skip _)) rfl (by omega)
  · have d := RExec.inc (inp := inp) (cap := cap) qA (S9 h0 h1 h2 x y z r q w t s u 0 0 0 c) (by show 0 < cap; omega)
    rw [S9_val_A, S9_setv_A] at d
    exact RExec.ifsT hb d

theorem setB_spec (x y z r q w t s u f1 : ℕ) (c b : Bool) (hb : readTapeBit (inp 0) (h0 + x) = b) (hcap : 1 ≤ cap) :
    RExec inp cap (.ifs 0 (.inc qB) .skip) (S9 h0 h1 h2 x y z r q w t s u f1 0 0 c)
      (S9 h0 h1 h2 x y z r q w t s u f1 b.toNat 0 c) 4 := by
  cases b
  · exact RExec.cast inp cap (RExec.ifsF hb (RExec.skip _)) rfl (by omega)
  · have d := RExec.inc (inp := inp) (cap := cap) qB (S9 h0 h1 h2 x y z r q w t s u f1 0 0 c) (by show 0 < cap; omega)
    rw [S9_val_B, S9_setv_B] at d
    exact RExec.ifsT hb d

theorem setC_spec (x y z r q w t s u f1 f2 : ℕ) (c b : Bool) (hb : readTapeBit (inp 0) (h0 + x) = b)
    (hcap : 1 ≤ cap) :
    RExec inp cap (.ifs 0 (.inc qC) .skip) (S9 h0 h1 h2 x y z r q w t s u f1 f2 0 c)
      (S9 h0 h1 h2 x y z r q w t s u f1 f2 b.toNat c) 4 := by
  cases b
  · exact RExec.cast inp cap (RExec.ifsF hb (RExec.skip _)) rfl (by omega)
  · have d := RExec.inc (inp := inp) (cap := cap) qC (S9 h0 h1 h2 x y z r q w t s u f1 f2 0 c) (by show 0 < cap; omega)
    rw [S9_val_C, S9_setv_C] at d
    exact RExec.ifsT hb d

/-- One unit of a coefficient: `R += F₁ + F₂ − F₃ (mod p)`. -/
def unitT : HProg := .seq (.ifr qA incM .skip) (.seq (.ifr qB incM .skip) (.ifr qC decM .skip))

theorem unitT_spec (p x y z w t s u : ℕ) (c b1 b2 b3 : Bool) (r : ℕ) (hr : r < p) (hp : p ≤ cap) :
    ∃ r', r' < p ∧ (r' : ZMod p) = r + ((b1.toNat : ZMod p) + b2.toNat - b3.toNat) ∧
      RExec inp cap unitT (S9 h0 h1 h2 x y z r (p - r) w t s u b1.toNat b2.toNat b3.toNat c)
        (S9 h0 h1 h2 x y z r' (p - r') w t s u b1.toNat b2.toNat b3.toNat c) (21 * p + 35) := by
  obtain ⟨r1, hr1, e1, d1⟩ : ∃ r1, r1 < p ∧ (r1 : ZMod p) = r + b1.toNat ∧
      RExec inp cap (.ifr qA incM .skip) (S9 h0 h1 h2 x y z r (p - r) w t s u b1.toNat b2.toNat b3.toNat c)
        (S9 h0 h1 h2 x y z r1 (p - r1) w t s u b1.toNat b2.toNat b3.toNat c) (7 * p + 11) := by
    cases b1
    · exact ⟨r, hr, by simp, RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) rfl (by omega)⟩
    · obtain ⟨r', h1, h2, h3⟩ := incM_spec inp cap h0 h1 h2 p x y z w t s u 1 b2.toNat b3.toNat c r hr hp
      exact ⟨r', h1, by simp [h2], RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) h3⟩
  obtain ⟨r2, hr2, e2, d2⟩ : ∃ r2, r2 < p ∧ (r2 : ZMod p) = r1 + b2.toNat ∧
      RExec inp cap (.ifr qB incM .skip) (S9 h0 h1 h2 x y z r1 (p - r1) w t s u b1.toNat b2.toNat b3.toNat c)
        (S9 h0 h1 h2 x y z r2 (p - r2) w t s u b1.toNat b2.toNat b3.toNat c) (7 * p + 11) := by
    cases b2
    · exact ⟨r1, hr1, by simp, RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) rfl (by omega)⟩
    · obtain ⟨r', h1, h2, h3⟩ := incM_spec inp cap h0 h1 h2 p x y z w t s u b1.toNat 1 b3.toNat c r1 hr1 hp
      exact ⟨r', h1, by simp [h2], RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) h3⟩
  obtain ⟨r3, hr3, e3, d3⟩ : ∃ r3, r3 < p ∧ (r3 : ZMod p) = r2 - b3.toNat ∧
      RExec inp cap (.ifr qC decM .skip) (S9 h0 h1 h2 x y z r2 (p - r2) w t s u b1.toNat b2.toNat b3.toNat c)
        (S9 h0 h1 h2 x y z r3 (p - r3) w t s u b1.toNat b2.toNat b3.toNat c) (7 * p + 11) := by
    cases b3
    · exact ⟨r2, hr2, by simp, RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) rfl (by omega)⟩
    · obtain ⟨r', h1, h2, h3⟩ := decM_spec inp cap h0 h1 h2 p x y z w t s u b1.toNat b2.toNat 1 c r2 hr2 hp
      exact ⟨r', h1, by simp [h2], RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) h3⟩
  refine ⟨r3, hr3, ?_, RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 d3)) rfl (by omega)⟩
  rw [e3, e2, e1]
  ring

/-- The units of one coefficient `1^a 0`. -/
def coefL : HProg := .whs 1 (.seq (RM.fwdC 1 qY) unitT)

theorem coefL_spec (rest : List Bool) (p x z w t s u : ℕ) (c b1 b2 b3 : Bool) (hp : p ≤ cap) :
    ∀ (a y r : ℕ), (inp 1).drop (h1 + y) = List.replicate a true ++ false :: rest → r < p → y + a ≤ cap →
      ∃ r', r' < p ∧ (r' : ZMod p) = r + (a : ZMod p) * ((b1.toNat : ZMod p) + b2.toNat - b3.toNat) ∧
        RExec inp cap coefL (S9 h0 h1 h2 x y z r (p - r) w t s u b1.toNat b2.toNat b3.toNat c)
          (S9 h0 h1 h2 x (y + a) z r' (p - r') w t s u b1.toNat b2.toNat b3.toNat c) ((21 * p + 43) * a + 1) := by
  intro a
  induction a with
  | zero =>
    intro y r h hr _
    have hb : readTapeBit (inp 1) (h1 + y) = false := ListEval.read_of_cons (by simpa using h)
    exact ⟨r, hr, by simp, RExec.cast inp cap (RExec.whsF hb) (by s9_args) (by omega)⟩
  | succ a ih =>
    intro y r h hr hy
    have h0' : (inp 1).drop (h1 + y) = true :: (List.replicate a true ++ false :: rest) := by
      simpa [List.replicate_succ] using h
    have hb : readTapeBit (inp 1) (h1 + y) = true := ListEval.read_of_cons h0'
    have h1' : (inp 1).drop (h1 + (y + 1)) = List.replicate a true ++ false :: rest := by
      rw [← Nat.add_assoc]; exact ListEval.drop_succ_of_cons h0'
    have d1 := fwd1_spec inp cap h0 h1 h2 x y z r (p - r) w t s u b1.toNat b2.toNat b3.toNat c (by omega)
    obtain ⟨r1, hr1, e1, d2⟩ := unitT_spec inp cap h0 h1 h2 p x (y + 1) z w t s u c b1 b2 b3 r hr hp
    obtain ⟨r2, hr2, e2, d3⟩ := ih (y + 1) r1 h1' hr1 (by omega)
    refine ⟨r2, hr2, ?_, ?_⟩
    · rw [e2, e1]; push_cast; ring
    · exact RExec.cast inp cap (RExec.whsT hb (RExec.seq d1 d2) d3) (by s9_args) (by nlinarith)

/-- Lower a corner flag. -/
def clrA : HProg := .ifr qA (.dec qA) .skip
def clrB : HProg := .ifr qB (.dec qB) .skip
def clrC : HProg := .ifr qC (.dec qC) .skip

theorem clrABC_spec (x y z r q w t s u : ℕ) (c b1 b2 b3 : Bool) (hcap : 1 ≤ cap) :
    RExec inp cap (.seq clrA (.seq clrB clrC)) (S9 h0 h1 h2 x y z r q w t s u b1.toNat b2.toNat b3.toNat c)
      (S9 h0 h1 h2 x y z r q w t s u 0 0 0 c) 8 := by
  have dA : RExec inp cap clrA (S9 h0 h1 h2 x y z r q w t s u b1.toNat b2.toNat b3.toNat c)
      (S9 h0 h1 h2 x y z r q w t s u 0 b2.toNat b3.toNat c) 2 := by
    cases b1
    · exact RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) rfl (by omega)
    · have d := RExec.dec (inp := inp) (cap := cap) qA (S9 h0 h1 h2 x y z r q w t s u (true).toNat b2.toNat b3.toNat c)
        (by show 1 ≤ cap; omega)
      rw [S9_val_A, S9_setv_A] at d
      exact RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) d
  have dB : RExec inp cap clrB (S9 h0 h1 h2 x y z r q w t s u 0 b2.toNat b3.toNat c)
      (S9 h0 h1 h2 x y z r q w t s u 0 0 b3.toNat c) 2 := by
    cases b2
    · exact RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) rfl (by omega)
    · have d := RExec.dec (inp := inp) (cap := cap) qB (S9 h0 h1 h2 x y z r q w t s u 0 (true).toNat b3.toNat c)
        (by show 1 ≤ cap; omega)
      rw [S9_val_B, S9_setv_B] at d
      exact RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) d
  have dC : RExec inp cap clrC (S9 h0 h1 h2 x y z r q w t s u 0 0 b3.toNat c)
      (S9 h0 h1 h2 x y z r q w t s u 0 0 0 c) 2 := by
    cases b3
    · exact RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) rfl (by omega)
    · have d := RExec.dec (inp := inp) (cap := cap) qC (S9 h0 h1 h2 x y z r q w t s u 0 0 (true).toNat c)
        (by show 1 ≤ cap; omega)
      rw [S9_val_C, S9_setv_C] at d
      exact RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) d
  exact RExec.cast inp cap (RExec.seq dA (RExec.seq dB dC)) rfl (by omega)

/-- One occurrence: read its corners `#1, #2, #3` into the flags, add its coefficient's units, lower the flags. -/
def grpT : HProg :=
  .seq (RM.fwdC 0 qX) (.seq (RM.fwdC 0 qX) (.seq (RM.fwdC 0 qX) (.seq (.ifs 0 (.inc qA) .skip) (.seq (RM.fwdC 0 qX)
    (.seq (RM.fwdC 0 qX) (.seq (.ifs 0 (.inc qB) .skip) (.seq (RM.fwdC 0 qX) (.seq (RM.fwdC 0 qX)
    (.seq (.ifs 0 (.inc qC) .skip) (.seq (RM.fwdC 0 qX) (.seq coefL (.seq (RM.fwdC 1 qY)
    (.seq clrA (.seq clrB clrC))))))))))))))

theorem grpT_spec (restX restT : List Bool) (p x y z w t s u a : ℕ) (c b0 b1 b2 b3 : Bool) (r : ℕ)
    (hX : (inp 0).drop (h0 + x) = true :: b0 :: true :: b1 :: true :: b2 :: true :: b3 :: restX)
    (hT : (inp 1).drop (h1 + y) = List.replicate a true ++ false :: restT) (hr : r < p) (hp : p ≤ cap)
    (hx : x + 8 ≤ cap) (hy : y + a + 1 ≤ cap) :
    ∃ r', r' < p ∧ (r' : ZMod p) = r + (a : ZMod p) * ((b1.toNat : ZMod p) + b2.toNat - b3.toNat) ∧
      RExec inp cap grpT (S9 h0 h1 h2 x y z r (p - r) w t s u 0 0 0 c)
        (S9 h0 h1 h2 (x + 8) (y + a + 1) z r' (p - r') w t s u 0 0 0 c) ((21 * p + 43) * a + 90) := by
  have hc1 : 1 ≤ cap := by omega
  have r3 : readTapeBit (inp 0) (h0 + (x + 1 + 1 + 1)) = b1 := by
    rw [show h0 + (x + 1 + 1 + 1) = h0 + x + 3 by omega]; exact read_at _ _ 3 _ hX
  have r5 : readTapeBit (inp 0) (h0 + (x + 1 + 1 + 1 + 1 + 1)) = b2 := by
    rw [show h0 + (x + 1 + 1 + 1 + 1 + 1) = h0 + x + 5 by omega]; exact read_at _ _ 5 _ hX
  have r7 : readTapeBit (inp 0) (h0 + (x + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = b3 := by
    rw [show h0 + (x + 1 + 1 + 1 + 1 + 1 + 1 + 1) = h0 + x + 7 by omega]; exact read_at _ _ 7 _ hX
  have s1 := fwd0_spec inp cap h0 h1 h2 x y z r (p - r) w t s u 0 0 0 c (by omega)
  have s2 := fwd0_spec inp cap h0 h1 h2 (x + 1) y z r (p - r) w t s u 0 0 0 c (by omega)
  have s3 := fwd0_spec inp cap h0 h1 h2 (x + 1 + 1) y z r (p - r) w t s u 0 0 0 c (by omega)
  have s4 := setA_spec inp cap h0 h1 h2 (x + 1 + 1 + 1) y z r (p - r) w t s u c b1 r3 hc1
  have s5 := fwd0_spec inp cap h0 h1 h2 (x + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat 0 0 c (by omega)
  have s6 := fwd0_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat 0 0 c (by omega)
  have s7 := setB_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat c b2 r5 hc1
  have s8 := fwd0_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat b2.toNat 0 c
    (by omega)
  have s9 := fwd0_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat b2.toNat 0 c
    (by omega)
  have s10 := setC_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat b2.toNat c b3
    r7 hc1
  have s11 := fwd0_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1) y z r (p - r) w t s u b1.toNat b2.toNat
    b3.toNat c (by omega)
  obtain ⟨r', hr', e', s12⟩ := coefL_spec inp cap h0 h1 h2 restT p (x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) z w t s u c b1 b2 b3
    hp a y r hT hr (by omega)
  have hT' : (inp 1).drop (h1 + (y + a)) = false :: restT := by
    rw [← Nat.add_assoc]
    have := ListEval.drop_add_of_append hT
    simpa using this
  have s13 := fwd1_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (y + a) z r' (p - r') w t s u b1.toNat
    b2.toNat b3.toNat c (by omega)
  have s14 := clrABC_spec inp cap h0 h1 h2 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (y + a + 1) z r' (p - r') w t s u c b1 b2
    b3 hc1
  refine ⟨r', hr', e', ?_⟩
  exact RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 (RExec.seq s6
    (RExec.seq s7 (RExec.seq s8 (RExec.seq s9 (RExec.seq s10 (RExec.seq s11 (RExec.seq s12 (RExec.seq s13
    s14))))))))))))) (by s9_args) (by omega)

/-- All occurrences. -/
def cornerL : HProg := .whs 0 grpT

theorem cornerL_spec (rest0 rest1 : List Bool) (p z w t s u : ℕ) (c : Bool) (hp : p ≤ cap) (L : ℕ) :
    ∀ (X : List Bool) (as : List ℕ) (x y r : ℕ), X.length = 4 * L → as.length = L →
      (inp 0).drop (h0 + x) = frameP X ++ false :: rest0 →
      (inp 1).drop (h1 + y) = as.flatMap ListEval.unary ++ rest1 → r < p →
      x + 8 * L ≤ cap → y + as.sum + L ≤ cap →
      ∃ r', r' < p ∧ (r' : ZMod p) = r + modAB p X as ∧
        RExec inp cap cornerL (S9 h0 h1 h2 x y z r (p - r) w t s u 0 0 0 c)
          (S9 h0 h1 h2 (x + 8 * L) (y + as.sum + L) z r' (p - r') w t s u 0 0 0 c)
          ((21 * p + 43) * as.sum + 92 * L + 1) := by
  induction L with
  | zero =>
    intro X as x y r hl ha hX _ hr _ _
    have e : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ea : as = [] := List.eq_nil_of_length_eq_zero ha
    subst e ea
    have hb : readTapeBit (inp 0) (h0 + x) = false := ListEval.read_of_cons (by simpa using hX)
    exact ⟨r, hr, by simp [modAB], RExec.cast inp cap (RExec.whsF hb) (by s9_args) (by simp)⟩
  | succ L ih =>
    intro X as x y r hl ha hX hT hr hxc hyc
    obtain ⟨b0, b1, b2, b3, X', rfl⟩ : ∃ b0 b1 b2 b3 X', X = b0 :: b1 :: b2 :: b3 :: X' := by
      rcases X with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, X'⟩⟩⟩⟩ <;> simp at hl <;> try omega
      exact ⟨b0, b1, b2, b3, X', rfl⟩
    obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
      rcases as with _ | ⟨a, as'⟩
      · simp at ha
      · exact ⟨a, as', rfl⟩
    simp only [List.length_cons] at hl ha
    simp only [List.sum_cons] at hyc
    rw [frameP_group] at hX
    have hX' : (inp 0).drop (h0 + (x + 8)) = frameP X' ++ false :: rest0 := by
      have := congrArg (List.drop 8) hX
      rw [List.drop_drop] at this
      rw [show h0 + (x + 8) = h0 + x + 8 by omega]
      simpa using this
    have hT0 : (inp 1).drop (h1 + y) = List.replicate a true ++ false :: (as'.flatMap ListEval.unary ++ rest1) := by
      simpa [ListEval.unary] using hT
    have hT' : (inp 1).drop (h1 + (y + a + 1)) = as'.flatMap ListEval.unary ++ rest1 := by
      have := ListEval.drop_add_of_append hT0
      simp only [List.length_replicate] at this
      have := ListEval.drop_succ_of_cons this
      rw [show h1 + (y + a + 1) = h1 + y + a + 1 by ring, this]
    obtain ⟨r1, hr1, e1, d1⟩ := grpT_spec inp cap h0 h1 h2 (frameP X' ++ false :: rest0)
      (as'.flatMap ListEval.unary ++ rest1) p x y z w t s u a c b0 b1 b2 b3 r (by simpa using hX) hT0 hr hp
      (by omega) (by omega)
    obtain ⟨r2, hr2, e2, d2⟩ := ih X' as' (x + 8) (y + a + 1) r1 (by omega) (by omega) hX' hT' hr1 (by omega) (by omega)
    have hb : readTapeBit (inp 0) (h0 + x) = true := ListEval.read_of_cons (by simpa using hX)
    refine ⟨r2, hr2, ?_, ?_⟩
    · rw [e2, e1, modAB]; ring
    · refine RExec.cast inp cap (RExec.whsT hb d1 d2) (by s9_args) ?_
      simp only [List.sum_cons]
      nlinarith

/-! ## Phase 3: the digits -/

/-- `R += T (mod p)` through `U`. -/
def addTL : HProg := .whr qT (.seq (.dec qT) (.seq (.inc qU) incM))
/-- `R −= S (mod p)` through `U`. -/
def addSL : HProg := .whr qS (.seq (.dec qS) (.seq (.inc qU) decM))

theorem addTL_spec (p x y z w s f1 f2 f3 : ℕ) (c : Bool) (hp : p ≤ cap) :
    ∀ (k u r : ℕ), r < p → u + k ≤ cap →
      ∃ r', r' < p ∧ (r' : ZMod p) = r + k ∧
        RExec inp cap addTL (S9 h0 h1 h2 x y z r (p - r) w k s u f1 f2 f3 c)
          (S9 h0 h1 h2 x y z r' (p - r') w 0 s (u + k) f1 f2 f3 c) ((7 * p + 20) * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro u r hr _
    exact ⟨r, hr, by simp, RExec.cast inp cap (RExec.whrF (S9_val_T ..)) (by s9_args) (by omega)⟩
  | succ k ih =>
    intro u r hr hu
    have d1 := RExec.dec (inp := inp) (cap := cap) qT (S9 h0 h1 h2 x y z r (p - r) w (k + 1) s u f1 f2 f3 c)
      (by show k + 1 ≤ cap; omega)
    rw [S9_val_T, S9_setv_T, Nat.add_sub_cancel] at d1
    have d2 := RExec.inc (inp := inp) (cap := cap) qU (S9 h0 h1 h2 x y z r (p - r) w k s u f1 f2 f3 c)
      (by show u < cap; omega)
    rw [S9_val_U, S9_setv_U] at d2
    obtain ⟨r1, hr1, e1, d3⟩ := incM_spec inp cap h0 h1 h2 p x y z w k s (u + 1) f1 f2 f3 c r hr hp
    obtain ⟨r2, hr2, e2, d4⟩ := ih (u + 1) r1 hr1 (by omega)
    refine ⟨r2, hr2, by rw [e2, e1]; push_cast; ring, ?_⟩
    exact RExec.cast inp cap (RExec.whrT (by show k + 1 ≠ 0; omega) (RExec.seq d1 (RExec.seq d2 d3)) d4)
      (by s9_args) (by nlinarith)

theorem addSL_spec (p x y z w t f1 f2 f3 : ℕ) (c : Bool) (hp : p ≤ cap) :
    ∀ (k u r : ℕ), r < p → u + k ≤ cap →
      ∃ r', r' < p ∧ (r' : ZMod p) = r - k ∧
        RExec inp cap addSL (S9 h0 h1 h2 x y z r (p - r) w t k u f1 f2 f3 c)
          (S9 h0 h1 h2 x y z r' (p - r') w t 0 (u + k) f1 f2 f3 c) ((7 * p + 20) * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro u r hr _
    exact ⟨r, hr, by simp, RExec.cast inp cap (RExec.whrF (S9_val_S ..)) (by s9_args) (by omega)⟩
  | succ k ih =>
    intro u r hr hu
    have d1 := RExec.dec (inp := inp) (cap := cap) qS (S9 h0 h1 h2 x y z r (p - r) w t (k + 1) u f1 f2 f3 c)
      (by show k + 1 ≤ cap; omega)
    rw [S9_val_S, S9_setv_S, Nat.add_sub_cancel] at d1
    have d2 := RExec.inc (inp := inp) (cap := cap) qU (S9 h0 h1 h2 x y z r (p - r) w t k u f1 f2 f3 c)
      (by show u < cap; omega)
    rw [S9_val_U, S9_setv_U] at d2
    obtain ⟨r1, hr1, e1, d3⟩ := decM_spec inp cap h0 h1 h2 p x y z w t k (u + 1) f1 f2 f3 c r hr hp
    obtain ⟨r2, hr2, e2, d4⟩ := ih (u + 1) r1 hr1 (by omega)
    refine ⟨r2, hr2, by rw [e2, e1]; push_cast; ring, ?_⟩
    exact RExec.cast inp cap (RExec.whrT (by show k + 1 ≠ 0; omega) (RExec.seq d1 (RExec.seq d2 d3)) d4)
      (by s9_args) (by nlinarith)

/-- `R += W·(T − S) (mod p)`; `T, S` are restored, `W` is consumed. -/
def foldL : HProg :=
  .whr qW (.seq (.dec qW) (.seq (.seq addTL (RM.move qU qT)) (.seq addSL (RM.move qU qS))))

theorem foldL_spec (p x y z t s : ℕ) (c : Bool) (hp : p ≤ cap) (ht : t ≤ cap) (hs : s ≤ cap) :
    ∀ (w r : ℕ), r < p → w ≤ cap →
      ∃ r', r' < p ∧ (r' : ZMod p) = r + (w : ZMod p) * ((t : ZMod p) - s) ∧
        RExec inp cap foldL (S9 h0 h1 h2 x y z r (p - r) w t s 0 0 0 0 c)
          (S9 h0 h1 h2 x y z r' (p - r') 0 t s 0 0 0 0 c) (w * ((t + s) * (7 * p + 27) + 12) + 1) := by
  intro w
  induction w with
  | zero =>
    intro r hr _
    exact ⟨r, hr, by simp, RExec.cast inp cap (RExec.whrF (S9_val_W ..)) (by s9_args) (by omega)⟩
  | succ w ih =>
    intro r hr hw
    have d1 := RExec.dec (inp := inp) (cap := cap) qW (S9 h0 h1 h2 x y z r (p - r) (w + 1) t s 0 0 0 0 c)
      (by show w + 1 ≤ cap; omega)
    rw [S9_val_W, S9_setv_W, Nat.add_sub_cancel] at d1
    obtain ⟨r1, hr1, e1, d2⟩ := addTL_spec inp cap h0 h1 h2 p x y z w s 0 0 0 c hp t 0 r hr (by omega)
    simp only [Nat.zero_add] at d2
    have d3 := move_spec inp cap qU qT (by decide) t (S9 h0 h1 h2 x y z r1 (p - r1) w 0 s t 0 0 0 c) rfl
      (by show t ≤ cap; omega) (by show 0 + t ≤ cap; omega)
    rw [S9_val_T, S9_val_U, S9_setv_U, S9_setv_T, Nat.zero_add] at d3
    obtain ⟨r2, hr2, e2, d4⟩ := addSL_spec inp cap h0 h1 h2 p x y z w t 0 0 0 c hp s 0 r1 hr1 (by omega)
    simp only [Nat.zero_add] at d4
    have d5 := move_spec inp cap qU qS (by decide) s (S9 h0 h1 h2 x y z r2 (p - r2) w t 0 s 0 0 0 c) rfl
      (by show s ≤ cap; omega) (by show 0 + s ≤ cap; omega)
    rw [S9_val_S, S9_val_U, S9_setv_U, S9_setv_S, Nat.zero_add] at d5
    obtain ⟨r3, hr3, e3, d6⟩ := ih r2 hr2 (by omega)
    refine ⟨r3, hr3, by rw [e3, e2, e1]; push_cast; ring, ?_⟩
    refine RExec.cast inp cap (RExec.whrT (by show w + 1 ≠ 0; omega)
      (RExec.seq d1 (RExec.seq (RExec.seq d2 d3) (RExec.seq d4 d5))) d6) (by s9_args) ?_
    nlinarith

/-- One digit `1 1^{w} 0` against `1^{t} 0 1^{s} 0`: `R += w·(t − s) (mod p)`. -/
def digT : HProg :=
  .seq (RM.fwdC 1 qY) (.seq (RM.readU 1 qY qW) (.seq (RM.readU 2 qZ qT) (.seq (RM.readU 2 qZ qS)
    (.seq foldL (.seq (RM.clear qT) (RM.clear qS))))))

theorem digT_spec (restT restR : List Bool) (p x y z w t s : ℕ) (c : Bool) (r : ℕ) (hr : r < p) (hp : p ≤ cap)
    (hT : (inp 1).drop (h1 + y) = true :: (List.replicate w true ++ false :: restT))
    (hR : (inp 2).drop (h2 + z) = List.replicate t true ++ false :: (List.replicate s true ++ false :: restR))
    (hy : y + w + 2 ≤ cap) (hz : z + t + s + 2 ≤ cap) :
    ∃ r', r' < p ∧ (r' : ZMod p) = r + (w : ZMod p) * ((t : ZMod p) - s) ∧
      RExec inp cap digT (S9 h0 h1 h2 x y z r (p - r) 0 0 0 0 0 0 0 c)
        (S9 h0 h1 h2 x (y + w + 2) (z + t + s + 2) r' (p - r') 0 0 0 0 0 0 0 c)
        (w * ((t + s) * (7 * p + 27) + 23) + 14 * (t + s) + 40) := by
  have d1 := fwd1_spec inp cap h0 h1 h2 x y z r (p - r) 0 0 0 0 0 0 0 c (by omega)
  have hT1 : (inp 1).drop (h1 + (y + 1)) = List.replicate w true ++ false :: restT := by
    rw [← Nat.add_assoc]; exact ListEval.drop_succ_of_cons hT
  have d2 := readW_spec inp cap h0 h1 h2 x (y + 1) z r (p - r) 0 0 0 0 0 0 0 w c restT hT1 (by omega) (by omega)
  have d3 := readT_spec inp cap h0 h1 h2 x (y + 1 + w + 1) z r (p - r) (0 + w) 0 0 0 0 0 0 t c _ hR (by omega)
    (by omega)
  have hR1 : (inp 2).drop (h2 + (z + t + 1)) = List.replicate s true ++ false :: restR := by
    have := ListEval.drop_add_of_append hR
    simp only [List.length_replicate] at this
    have := ListEval.drop_succ_of_cons this
    rw [show h2 + (z + t + 1) = h2 + z + t + 1 by ring, this]
  have d4 := readS_spec inp cap h0 h1 h2 x (y + 1 + w + 1) (z + t + 1) r (p - r) (0 + w) (0 + t) 0 0 0 0 0 s c restR
    hR1 (by omega) (by omega)
  simp only [Nat.zero_add] at d2 d3 d4
  obtain ⟨r1, hr1, e1, d5⟩ := foldL_spec inp cap h0 h1 h2 p x (y + 1 + w + 1) (z + t + 1 + s + 1) t s c hp (by omega)
    (by omega) w r hr (by omega)
  have d6 := clear_spec inp cap qT t (S9 h0 h1 h2 x (y + 1 + w + 1) (z + t + 1 + s + 1) r1 (p - r1) 0 t s 0 0 0 0 c) rfl
    (by show t ≤ cap; omega)
  rw [S9_setv_T] at d6
  have d7 := clear_spec inp cap qS s (S9 h0 h1 h2 x (y + 1 + w + 1) (z + t + 1 + s + 1) r1 (p - r1) 0 0 s 0 0 0 0 c) rfl
    (by show s ≤ cap; omega)
  rw [S9_setv_S] at d7
  refine ⟨r1, hr1, e1, ?_⟩
  refine RExec.cast inp cap (RExec.seq d1 (RExec.seq d2 (RExec.seq d3 (RExec.seq d4 (RExec.seq d5 (RExec.seq d6
    d7)))))) (by s9_args) ?_
  nlinarith

/-- The reports word: `1^{t_d^+} 0 1^{t_d^−} 0` per digit. -/
def repWord : List ℕ → List ℕ → List Bool
  | t :: tp, s :: tm => ListEval.unary t ++ ListEval.unary s ++ repWord tp tm
  | _, _ => []

/-- The digit section of the row's word: `1 1^{w_d} 0` per digit. -/
def digWord (ws : List ℕ) : List Bool := ws.flatMap fun w => true :: ListEval.unary w

/-- The step bound of the digit phase. -/
def digCost (p : ℕ) : List ℕ → List ℕ → List ℕ → ℕ
  | w :: ws, t :: tp, s :: tm => w * ((t + s) * (7 * p + 27) + 23) + 14 * (t + s) + 42 + digCost p ws tp tm
  | _, _, _ => 1

/-- All digits. -/
def digL : HProg := .whs 1 digT

theorem digL_spec (rest1 rest2 : List Bool) (p x : ℕ) (c : Bool) (hp : p ≤ cap) :
    ∀ (ws tp tm : List ℕ) (y z r : ℕ), ws.length = tp.length → ws.length = tm.length →
      (inp 1).drop (h1 + y) = digWord ws ++ false :: rest1 → (inp 2).drop (h2 + z) = repWord tp tm ++ rest2 →
      r < p → y + ws.sum + 2 * ws.length ≤ cap → z + tp.sum + tm.sum + 2 * tp.length ≤ cap →
      ∃ r', r' < p ∧ (r' : ZMod p) = r + modDig p ws tp tm ∧
        RExec inp cap digL (S9 h0 h1 h2 x y z r (p - r) 0 0 0 0 0 0 0 c)
          (S9 h0 h1 h2 x (y + ws.sum + 2 * ws.length) (z + tp.sum + tm.sum + 2 * tp.length) r' (p - r')
            0 0 0 0 0 0 0 c) (digCost p ws tp tm) := by
  intro ws
  induction ws with
  | nil =>
    intro tp tm y z r h1l h2l hT _ hr _ _
    have etp : tp = [] := List.eq_nil_of_length_eq_zero (by simpa using h1l.symm)
    have etm : tm = [] := List.eq_nil_of_length_eq_zero (by simpa using h2l.symm)
    subst etp etm
    have hb : readTapeBit (inp 1) (h1 + y) = false := ListEval.read_of_cons (by simpa [digWord] using hT)
    exact ⟨r, hr, by simp [modDig], RExec.cast inp cap (RExec.whsF hb) (by s9_args) (by simp [digCost])⟩
  | cons w ws ih =>
    intro tp tm y z r h1l h2l hT hR hr hy hz
    obtain ⟨t, tp', rfl⟩ : ∃ t tp', tp = t :: tp' := by
      rcases tp with _ | ⟨t, tp'⟩
      · simp at h1l
      · exact ⟨t, tp', rfl⟩
    obtain ⟨s, tm', rfl⟩ : ∃ s tm', tm = s :: tm' := by
      rcases tm with _ | ⟨s, tm'⟩
      · simp at h2l
      · exact ⟨s, tm', rfl⟩
    simp only [List.length_cons, List.sum_cons] at h1l h2l hy hz
    have hT0 : (inp 1).drop (h1 + y) = true :: (List.replicate w true ++ false :: (digWord ws ++ false :: rest1)) := by
      simpa [digWord, ListEval.unary] using hT
    have hR0 : (inp 2).drop (h2 + z) =
        List.replicate t true ++ false :: (List.replicate s true ++ false :: (repWord tp' tm' ++ rest2)) := by
      simpa [repWord, ListEval.unary] using hR
    obtain ⟨r1, hr1, e1, d1⟩ := digT_spec inp cap h0 h1 h2 _ _ p x y z w t s c r hr hp hT0 hR0 (by omega) (by omega)
    have hT' : (inp 1).drop (h1 + (y + w + 2)) = digWord ws ++ false :: rest1 := by
      have := ListEval.drop_succ_of_cons hT0
      have := ListEval.drop_add_of_append this
      simp only [List.length_replicate] at this
      have := ListEval.drop_succ_of_cons this
      rw [show h1 + (y + w + 2) = h1 + y + 1 + w + 1 by ring, this]
    have hR' : (inp 2).drop (h2 + (z + t + s + 2)) = repWord tp' tm' ++ rest2 := by
      have := ListEval.drop_add_of_append hR0
      simp only [List.length_replicate] at this
      have := ListEval.drop_succ_of_cons this
      have := ListEval.drop_add_of_append this
      simp only [List.length_replicate] at this
      have := ListEval.drop_succ_of_cons this
      rw [show h2 + (z + t + s + 2) = h2 + z + t + 1 + s + 1 by ring, this]
    obtain ⟨r2, hr2, e2, d2⟩ := ih tp' tm' (y + w + 2) (z + t + s + 2) r1 (by omega) (by omega) hT' hR' hr1
      (by omega) (by omega)
    have hb : readTapeBit (inp 1) (h1 + y) = true := ListEval.read_of_cons hT0
    refine ⟨r2, hr2, by rw [e2, e1, modDig]; ring, ?_⟩
    refine RExec.cast inp cap (RExec.whsT hb d1 d2) (by s9_args) ?_
    simp only [digCost]
    omega

/-! ## The program -/

/-- The row's word: `1^p 0`, `1^{r₀} 0`, the coefficients `1^{a_i} 0`, the digit section, a final `0`. -/
def rowWord (p r0 : ℕ) (as ws : List ℕ) : List Bool :=
  ListEval.unary p ++ ListEval.unary r0 ++ as.flatMap ListEval.unary ++ digWord ws ++ [false]

theorem flatMap_unary_length : ∀ (as : List ℕ), (as.flatMap ListEval.unary).length = as.sum + as.length
  | [] => rfl
  | a :: as => by
    rw [List.flatMap_cons, List.length_append, flatMap_unary_length as]
    simp only [ListEval.unary, List.length_append, List.length_replicate, List.length_cons, List.length_nil,
      List.sum_cons]
    omega

/-- The register capacity. -/
def capT (p r0 L : ℕ) (as ws tp tm : List ℕ) : ℕ :=
  8 * L + p + r0 + as.sum + L + ws.sum + 2 * ws.length + tp.sum + tm.sum + 2 * tp.length + 4

/-- One step bound. -/
def costT (p r0 L : ℕ) (as ws tp tm : List ℕ) : ℕ :=
  14 * p + 13 * r0 + (21 * p + 43) * as.sum + 132 * L + digCost p ws tp tm +
    5 * (p + r0 + 2 + as.sum + L + ws.sum + 2 * ws.length) + 5 * (tp.sum + tm.sum + 2 * tp.length) + 40

end NearCubicWires.WireExponent3_5.FinalPass.Term
