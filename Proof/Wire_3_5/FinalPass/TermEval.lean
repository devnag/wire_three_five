import Proof.Wire_3_5.FinalPass.TermRef
import Proof.Wire_3_5.FinalPass.ListEvalCyc
import Proof.Wire_3_5.FinalPass.WordMap

/-! # Final pass, stage 8: the circuit's factor of the reported conjunction at one point (P3:2489-2494, 3170-3178)

The per-point evaluator of one symmetric circuit's factor `g(#1 − #3 + #2 + [t⁺] − [t⁻])` (`termOk`,
`WireExponent3_5FinalPassTermRef`): a register program `term8` over two read-only streams, the framed corner word
`frame X` (stream 0, from any head position `h₀`) and the framed top table `frame top` (stream 1, from any `h₁`), with
the lists' reports `t⁺, t⁻` in two registers.

1. `count8`: one pass over the corner groups: `S += #1 + #2`, `N += #3`, `G += #groups`; the stream is rewound.
2. `clamp8` (twice): the report is clamped to `{0,…,G}` (`clampN`, `clampState`) into `K` and moved to `S` resp.
   `N`; `G` is restored after each clamp and cleared at the end.
3. `sgnL`: `N` is subtracted from `S`; the flag `F` records `S < N` (the score is negative).
4. `pick`: a negative score gives `0`; otherwise the table is read at `S` (`0` past its end: `g` extended by zero),
   and the table stream is rewound.

Every register ends at `0` and both heads end where they started (loop-safe); the reports are
consumed. **`term8_spec`**: the cell becomes `termOk X top t⁺ t⁻`, within `cost8`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Term
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout -/

scoped notation "rP" => (0 : Fin 10)
scoped notation "rM" => (1 : Fin 10)
scoped notation "rG" => (2 : Fin 10)
scoped notation "rS" => (3 : Fin 10)
scoped notation "rN" => (4 : Fin 10)
scoped notation "rA" => (5 : Fin 10)
scoped notation "rF" => (6 : Fin 10)
scoped notation "rX" => (7 : Fin 10)
scoped notation "rT" => (8 : Fin 10)
scoped notation "rK" => (9 : Fin 10)

abbrev TProg := RM 1 10

/-- The state at a phase boundary: the stream origins `h₀, h₁` and offsets `x, t` (also held by the counters `X`,
`T`), the reports `p, m`, the group count `g`, the sums `s, n`, the scratch count `a`, the flag `f`, the clamp `k`. -/
def S8 (h0 h1 x t p m g s n a f k : ℕ) (c : Bool) : RState 1 10 :=
  ⟨![h0 + x, h1 + t], ![p, m, g, s, n, a, f, x, t, k], c⟩

/-- Close an equality of phase states. -/
syntax "s8_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| s8_eq) => `(tactic| s8_eq [])
  | `(tactic| s8_eq [$ts,*]) => `(tactic| (refine RState.eq ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [S8, $ts,*]; done) | (simp [S8, $ts,*] <;> omega))
        | rfl
        | (simp [$ts,*]; done)))


/-- Close an equality of phase states argument by argument. -/
macro "s8_args" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (simp; done) | (simp <;> omega)))

section Upd
variable (h0 h1 x t p m g s n a f k : ℕ) (c : Bool)

@[simp] theorem S8_val_P : (S8 h0 h1 x t p m g s n a f k c).val rP = p := rfl
@[simp] theorem S8_val_M : (S8 h0 h1 x t p m g s n a f k c).val rM = m := rfl
@[simp] theorem S8_val_G : (S8 h0 h1 x t p m g s n a f k c).val rG = g := rfl
@[simp] theorem S8_val_S : (S8 h0 h1 x t p m g s n a f k c).val rS = s := rfl
@[simp] theorem S8_val_N : (S8 h0 h1 x t p m g s n a f k c).val rN = n := rfl
@[simp] theorem S8_val_A : (S8 h0 h1 x t p m g s n a f k c).val rA = a := rfl
@[simp] theorem S8_val_F : (S8 h0 h1 x t p m g s n a f k c).val rF = f := rfl
@[simp] theorem S8_val_X : (S8 h0 h1 x t p m g s n a f k c).val rX = x := rfl
@[simp] theorem S8_val_T : (S8 h0 h1 x t p m g s n a f k c).val rT = t := rfl
@[simp] theorem S8_val_K : (S8 h0 h1 x t p m g s n a f k c).val rK = k := rfl

theorem S8_setv_P (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rP w = S8 h0 h1 x t w m g s n a f k c := by
  s8_eq
theorem S8_setv_M (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rM w = S8 h0 h1 x t p w g s n a f k c := by
  s8_eq
theorem S8_setv_G (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rG w = S8 h0 h1 x t p m w s n a f k c := by
  s8_eq
theorem S8_setv_S (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rS w = S8 h0 h1 x t p m g w n a f k c := by
  s8_eq
theorem S8_setv_N (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rN w = S8 h0 h1 x t p m g s w a f k c := by
  s8_eq
theorem S8_setv_A (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rA w = S8 h0 h1 x t p m g s n w f k c := by
  s8_eq
theorem S8_setv_F (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rF w = S8 h0 h1 x t p m g s n a w k c := by
  s8_eq
theorem S8_setv_K (w : ℕ) : (S8 h0 h1 x t p m g s n a f k c).setv rK w = S8 h0 h1 x t p m g s n a f w c := by
  s8_eq

theorem S8_rewX : ((S8 h0 h1 x t p m g s n a f k c).setv rX 0).seth 0 ((S8 h0 h1 x t p m g s n a f k c).sh 0 - x) =
    S8 h0 h1 0 t p m g s n a f k c := by
  s8_eq

theorem S8_rewT : ((S8 h0 h1 x t p m g s n a f k c).setv rT 0).seth 1 ((S8 h0 h1 x t p m g s n a f k c).sh 1 - t) =
    S8 h0 h1 x 0 p m g s n a f k c := by
  s8_eq

end Upd

variable (inp : Fin 2 → List Bool) (cap : ℕ) (h0 h1 : ℕ)

/-! ## Phase 1: the counts -/

theorem fX_spec (x t p m g s n a f k : ℕ) (c : Bool) (hx : x < cap) :
    RExec inp cap (RM.fwdC 0 rX) (S8 h0 h1 x t p m g s n a f k c) (S8 h0 h1 (x + 1) t p m g s n a f k c) 5 :=
  RExec.cast inp cap (fwdC_spec inp cap 0 rX _ hx) (by s8_eq) le_rfl

theorem fT_spec (x t p m g s n a f k : ℕ) (c : Bool) (ht : t < cap) :
    RExec inp cap (RM.fwdC 1 rT) (S8 h0 h1 x t p m g s n a f k c) (S8 h0 h1 x (t + 1) p m g s n a f k c) 5 :=
  RExec.cast inp cap (fwdC_spec inp cap 1 rT _ ht) (by s8_eq) le_rfl

/-- Count the scanned corner into `S`. -/
def cntS : TProg := .ifs 0 (.inc rS) .skip
/-- Count the scanned corner into `N`. -/
def cntN : TProg := .ifs 0 (.inc rN) .skip

theorem cntS_spec (x t p m g s n a f k : ℕ) (c b : Bool) (hb : readTapeBit (inp 0) (h0 + x) = b) (hs : s < cap) :
    RExec inp cap cntS (S8 h0 h1 x t p m g s n a f k c) (S8 h0 h1 x t p m g (s + b.toNat) n a f k c) 4 := by
  cases b
  · exact RExec.cast inp cap (RExec.ifsF hb (RExec.skip _)) (by s8_eq) (by omega)
  · exact RExec.cast inp cap (RExec.ifsT hb (RExec.inc (inp := inp) (cap := cap) rS _ hs)) (by s8_eq) le_rfl

theorem cntN_spec (x t p m g s n a f k : ℕ) (c b : Bool) (hb : readTapeBit (inp 0) (h0 + x) = b) (hn : n < cap) :
    RExec inp cap cntN (S8 h0 h1 x t p m g s n a f k c) (S8 h0 h1 x t p m g s (n + b.toNat) a f k c) 4 := by
  cases b
  · exact RExec.cast inp cap (RExec.ifsF hb (RExec.skip _)) (by s8_eq) (by omega)
  · exact RExec.cast inp cap (RExec.ifsT hb (RExec.inc (inp := inp) (cap := cap) rN _ hn)) (by s8_eq) le_rfl

theorem incG_spec (x t p m g s n a f k : ℕ) (c : Bool) (hg : g < cap) :
    RExec inp cap (.inc rG) (S8 h0 h1 x t p m g s n a f k c) (S8 h0 h1 x t p m (g + 1) s n a f k c) 3 :=
  RExec.cast inp cap (RExec.inc (inp := inp) (cap := cap) rG _ hg) (by s8_eq) le_rfl

/-- One corner group `[1,a,1,b,1,c,1,d]`: `S += b + c`, `N += d`, `G += 1`. -/
def grp8 : TProg :=
  .seq (RM.fwdC 0 rX) (.seq (RM.fwdC 0 rX) (.seq (RM.fwdC 0 rX) (.seq cntS (.seq (RM.fwdC 0 rX) (.seq (RM.fwdC 0 rX)
    (.seq cntS (.seq (RM.fwdC 0 rX) (.seq (RM.fwdC 0 rX) (.seq cntN (.seq (RM.fwdC 0 rX) (.inc rG)))))))))))

theorem read_at (l : List Bool) (p k : ℕ) (w : List Bool) (hw : l.drop p = w) :
    readTapeBit l (p + k) = w.getD k false := by
  rw [ListEval.readTapeBit_drop, hw]; rfl

theorem grp8_spec (x t p m g s n a f k : ℕ) (c b0 b1 b2 b3 : Bool) (rest : List Bool)
    (hX : (inp 0).drop (h0 + x) = true :: b0 :: true :: b1 :: true :: b2 :: true :: b3 :: rest)
    (hx : x + 8 ≤ cap) (hg : g < cap) (hs : s + 2 ≤ cap) (hn : n < cap) :
    RExec inp cap grp8 (S8 h0 h1 x t p m g s n a f k c)
      (S8 h0 h1 (x + 8) t p m (g + 1) (s + b1.toNat + b2.toNat) (n + b3.toNat) a f k c) 69 := by
  have r3 : readTapeBit (inp 0) (h0 + (x + 1 + 1 + 1)) = b1 := by
    rw [show h0 + (x + 1 + 1 + 1) = h0 + x + 3 by omega]; exact read_at _ _ 3 _ hX
  have r5 : readTapeBit (inp 0) (h0 + (x + 1 + 1 + 1 + 1 + 1)) = b2 := by
    rw [show h0 + (x + 1 + 1 + 1 + 1 + 1) = h0 + x + 5 by omega]; exact read_at _ _ 5 _ hX
  have r7 : readTapeBit (inp 0) (h0 + (x + 1 + 1 + 1 + 1 + 1 + 1 + 1)) = b3 := by
    rw [show h0 + (x + 1 + 1 + 1 + 1 + 1 + 1 + 1) = h0 + x + 7 by omega]; exact read_at _ _ 7 _ hX
  have s1 := fX_spec inp cap h0 h1 x t p m g s n a f k c (by omega)
  have s2 := fX_spec inp cap h0 h1 (x + 1) t p m g s n a f k c (by omega)
  have s3 := fX_spec inp cap h0 h1 (x + 1 + 1) t p m g s n a f k c (by omega)
  have s4 := cntS_spec inp cap h0 h1 (x + 1 + 1 + 1) t p m g s n a f k c b1 r3 (by omega)
  have s5 := fX_spec inp cap h0 h1 (x + 1 + 1 + 1) t p m g (s + b1.toNat) n a f k c (by omega)
  have s6 := fX_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1) t p m g (s + b1.toNat) n a f k c (by omega)
  have s7 := cntS_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1 + 1) t p m g (s + b1.toNat) n a f k c b2 r5
    (by cases b1 <;> simp <;> omega)
  have s8 := fX_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1 + 1) t p m g (s + b1.toNat + b2.toNat) n a f k c (by omega)
  have s9 := fX_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1 + 1 + 1) t p m g (s + b1.toNat + b2.toNat) n a f k c
    (by omega)
  have s10 := cntN_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1) t p m g (s + b1.toNat + b2.toNat) n a f k c b3
    r7 hn
  have s11 := fX_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1) t p m g (s + b1.toNat + b2.toNat)
    (n + b3.toNat) a f k c (by omega)
  have s12 := incG_spec inp cap h0 h1 (x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) t p m g (s + b1.toNat + b2.toNat)
    (n + b3.toNat) a f k c hg
  exact RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 (RExec.seq s6
    (RExec.seq s7 (RExec.seq s8 (RExec.seq s9 (RExec.seq s10 (RExec.seq s11 s12)))))))))))
    (by s8_eq) (by omega)

/-- The count loop over the corner groups. -/
def count8 : TProg := .whs 0 grp8

theorem frameP_group (b0 b1 b2 b3 : Bool) (X : List Bool) :
    frameP (b0 :: b1 :: b2 :: b3 :: X) = true :: b0 :: true :: b1 :: true :: b2 :: true :: b3 :: frameP X := by
  simp [frameP]

theorem cnt_group (i : Fin 4) (b0 b1 b2 b3 : Bool) (X : List Bool) :
    cnt i (b0 :: b1 :: b2 :: b3 :: X) = (![b0, b1, b2, b3] i).toNat + cnt i X := by
  rw [cnt]; cases ![b0, b1, b2, b3] i <;> rfl

theorem count8_spec (rest : List Bool) (t p m a f k : ℕ) (c : Bool) (L : ℕ) :
    ∀ (X : List Bool) (x g s n : ℕ), X.length = 4 * L →
      (inp 0).drop (h0 + x) = frameP X ++ false :: rest →
      x + 8 * L ≤ cap → g + L ≤ cap → s + 2 * L ≤ cap → n + L ≤ cap →
      RExec inp cap count8 (S8 h0 h1 x t p m g s n a f k c)
        (S8 h0 h1 (x + 8 * L) t p m (g + L) (s + cnt 1 X + cnt 2 X) (n + cnt 3 X) a f k c) (71 * L + 1) := by
  induction L with
  | zero =>
    intro X x g s n hl hX _ _ _ _
    have e : X = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst e
    have hr : readTapeBit (inp 0) (h0 + x) = false := ListEval.read_of_cons (by simpa using hX)
    exact RExec.cast inp cap (RExec.whsF hr) (by s8_eq [cnt]) le_rfl
  | succ L ih =>
    intro X x g s n hl hX hxc hgc hsc hnc
    obtain ⟨b0, b1, b2, b3, X', rfl⟩ : ∃ b0 b1 b2 b3 X', X = b0 :: b1 :: b2 :: b3 :: X' := by
      rcases X with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, X'⟩⟩⟩⟩ <;> simp at hl <;> try omega
      exact ⟨b0, b1, b2, b3, X', rfl⟩
    simp only [List.length_cons] at hl
    rw [frameP_group] at hX
    have hX' : (inp 0).drop (h0 + (x + 8)) = frameP X' ++ false :: rest := by
      have := congrArg (List.drop 8) hX
      rw [List.drop_drop] at this
      rw [show h0 + (x + 8) = h0 + x + 8 by omega]
      simpa using this
    have s1 := grp8_spec inp cap h0 h1 x t p m g s n a f k c b0 b1 b2 b3 (frameP X' ++ false :: rest) (by simpa using hX)
      (by omega) (by omega) (by omega) (by omega)
    have ih' := ih X' (x + 8) (g + 1) (s + b1.toNat + b2.toNat) (n + b3.toNat) (by omega) hX' (by omega) (by omega)
      (by cases b1 <;> cases b2 <;> simp <;> omega) (by cases b3 <;> simp <;> omega)
    have hr : readTapeBit (inp 0) (h0 + x) = true := ListEval.read_of_cons (by simpa using hX)
    have e1 : x + 8 + 8 * L = x + 8 * (L + 1) := by ring
    have e2 : g + 1 + L = g + (L + 1) := by ring
    have e3 : s + b1.toNat + b2.toNat + cnt 1 X' + cnt 2 X' =
        s + cnt 1 (b0 :: b1 :: b2 :: b3 :: X') + cnt 2 (b0 :: b1 :: b2 :: b3 :: X') := by
      have v1 : (![b0, b1, b2, b3] : Fin 4 → Bool) 1 = b1 := rfl
      have v2 : (![b0, b1, b2, b3] : Fin 4 → Bool) 2 = b2 := rfl
      rw [cnt_group, cnt_group, v1, v2]; ring
    have e4 : n + b3.toNat + cnt 3 X' = n + cnt 3 (b0 :: b1 :: b2 :: b3 :: X') := by
      have v3 : (![b0, b1, b2, b3] : Fin 4 → Bool) 3 = b3 := rfl
      rw [cnt_group, v3]; ring
    rw [e1, e2, e3, e4] at ih'
    exact RExec.mono (RExec.whsT hr s1 ih') (by omega)


/-! ## Phase 2: the clamped reports -/

/-- Count the report down against `G` into `A`; the flag `F` records a report above `G`. -/
def clampL : TProg := .whr rP (.seq (.dec rP) (.ifr rG (.seq (.dec rG) (.inc rA)) (RM.setF rF)))

theorem clampL_spec (x t m s n kk : ℕ) (c : Bool) (hcap : 1 ≤ cap) :
    ∀ (p g a f : ℕ), f ≤ 1 → p ≤ cap → g ≤ cap → a + min p g ≤ cap →
      RExec inp cap clampL (S8 h0 h1 x t p m g s n a f kk c)
        (S8 h0 h1 x t 0 m (g - min p g) s n (a + min p g) (if g < p then 1 else f) kk c) (10 * p + 1) := by
  intro p
  induction p with
  | zero =>
    intro g a f _ _ _ _
    exact RExec.cast inp cap (RExec.whrF (S8_val_P ..)) (by s8_args) le_rfl
  | succ p ih =>
    intro g a f hf hp hg ha
    have d1 := RExec.dec (inp := inp) (cap := cap) rP (S8 h0 h1 x t (p + 1) m g s n a f kk c) hp
    rw [S8_val_P, S8_setv_P, Nat.add_sub_cancel] at d1
    rcases g with _ | g
    · have d2 := setF_spec inp cap rF (S8 h0 h1 x t p m 0 s n a f kk c) hf hcap
      rw [S8_setv_F] at d2
      have ih' := ih 0 a 1 le_rfl (by omega) (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show p + 1 ≠ 0; omega) (RExec.seq d1 (RExec.ifrF (S8_val_G ..) d2)) ih')
        (by s8_args) (by omega)
    · have d2 := RExec.dec (inp := inp) (cap := cap) rG (S8 h0 h1 x t p m (g + 1) s n a f kk c) hg
      rw [S8_val_G, S8_setv_G, Nat.add_sub_cancel] at d2
      have d3 := RExec.inc (inp := inp) (cap := cap) rA (S8 h0 h1 x t p m g s n a f kk c) (by
        show a < cap
        omega)
      rw [S8_val_A, S8_setv_A] at d3
      have ih' := ih g (a + 1) f hf (by omega) (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show p + 1 ≠ 0; omega)
        (RExec.seq d1 (RExec.ifrT (by show g + 1 ≠ 0; omega) (RExec.seq d2 d3))) ih') (by s8_args) (by omega)

/-- Move `A` back into `G`, and into `K` unless the flag is up. -/
def backL : TProg := .whr rA (.seq (.dec rA) (.seq (.inc rG) (.ifr rF .skip (.inc rK))))

theorem backL_spec (x t p m s n : ℕ) (fb c : Bool) :
    ∀ (j g kk : ℕ), g + j ≤ cap → kk + j ≤ cap →
      RExec inp cap backL (S8 h0 h1 x t p m g s n j fb.toNat kk c)
        (S8 h0 h1 x t p m (g + j) s n 0 fb.toNat (kk + if fb then 0 else j) c) (12 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro g kk _ _
    exact RExec.cast inp cap (RExec.whrF (S8_val_A ..)) (by s8_args) le_rfl
  | succ j ih =>
    intro g kk hg hk
    have d1 := RExec.dec (inp := inp) (cap := cap) rA (S8 h0 h1 x t p m g s n (j + 1) fb.toNat kk c)
      (by show j + 1 ≤ cap; omega)
    rw [S8_val_A, S8_setv_A, Nat.add_sub_cancel] at d1
    have d2 := RExec.inc (inp := inp) (cap := cap) rG (S8 h0 h1 x t p m g s n j fb.toNat kk c)
      (by show g < cap; omega)
    rw [S8_val_G, S8_setv_G] at d2
    cases fb
    · have d3 := RExec.inc (inp := inp) (cap := cap) rK (S8 h0 h1 x t p m (g + 1) s n j (false).toNat kk c)
        (by show kk < cap; omega)
      rw [S8_val_K, S8_setv_K] at d3
      have ih' := ih (g + 1) (kk + 1) (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show j + 1 ≠ 0; omega)
        (RExec.seq d1 (RExec.seq d2 (RExec.ifrF (S8_val_F ..) d3))) ih') (by s8_args) (by omega)
    · have ih' := ih (g + 1) kk (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show j + 1 ≠ 0; omega)
        (RExec.seq d1 (RExec.seq d2 (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) (RExec.skip _)))) ih') (by s8_args)
        (by omega)

/-- Lower the flag. -/
def clrF : TProg := .ifr rF (.dec rF) .skip

theorem clrF_spec (x t p m g s n a kk : ℕ) (fb c : Bool) (hcap : 1 ≤ cap) :
    RExec inp cap clrF (S8 h0 h1 x t p m g s n a fb.toNat kk c) (S8 h0 h1 x t p m g s n a 0 kk c) 2 := by
  cases fb
  · exact RExec.cast inp cap (RExec.ifrF (S8_val_F ..) (RExec.skip _)) rfl (by omega)
  · have d := RExec.dec (inp := inp) (cap := cap) rF (S8 h0 h1 x t p m g s n a (true).toNat kk c)
      (by show 1 ≤ cap; omega)
    rw [S8_val_F, S8_setv_F] at d
    exact RExec.cast inp cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) d) rfl le_rfl

/-- **Clamp the report `P` to `{0,…,G}` into `K`** (`clampN`). -/
def clamp8 : TProg := .seq clampL (.seq backL clrF)

theorem clamp8_spec (x t m s n p g : ℕ) (c : Bool) (hcap : 1 ≤ cap) (hp : p ≤ cap) (hg : g + g ≤ cap) :
    RExec inp cap clamp8 (S8 h0 h1 x t p m g s n 0 0 0 c) (S8 h0 h1 x t 0 m g s n 0 0 (clampN g p) c)
      (10 * p + 12 * g + 6) := by
  have hmin : min p g ≤ g := Nat.min_le_right _ _
  have s1 := clampL_spec inp cap h0 h1 x t m s n 0 c hcap p g 0 0 (by omega) hp (by omega) (by omega)
  have ef : (if g < p then 1 else 0) = (decide (g < p)).toNat := by by_cases h : g < p <;> simp [h]
  rw [ef, Nat.zero_add] at s1
  have s2 := backL_spec inp cap h0 h1 x t 0 m s n (decide (g < p)) c (min p g) (g - min p g) 0 (by omega) (by omega)
  have hk : (0 + if decide (g < p) then 0 else min p g) = clampN g p := by
    unfold clampN
    by_cases h : g < p
    · simp [h]
    · have h' : p ≤ g := by omega
      simp [h, h']
  rw [hk, Nat.sub_add_cancel hmin] at s2
  have s3 := clrF_spec inp cap h0 h1 x t 0 m g s n 0 (clampN g p) (decide (g < p)) c hcap
  exact RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 s3)) rfl (by omega)

/-- Both clamped reports: `S += [t⁺]`, `N += [t⁻]`; the reports are consumed, `G` is cleared. -/
def phase2 : TProg :=
  .seq clamp8 (.seq (RM.move rK rS) (.seq (RM.move rM rP) (.seq clamp8 (.seq (RM.move rK rN) (RM.clear rG)))))

theorem phase2_spec (t p m g s n : ℕ) (c : Bool) (hcap : 1 ≤ cap) (hp : p ≤ cap) (hm : m ≤ cap) (hg : g + g ≤ cap)
    (hs : s + g ≤ cap) (hn : n + g ≤ cap) :
    RExec inp cap phase2 (S8 h0 h1 0 t p m g s n 0 0 0 c)
      (S8 h0 h1 0 t 0 0 0 (s + clampN g p) (n + clampN g m) 0 0 0 c) (10 * (p + m) + 7 * m + 41 * g + 30) := by
  have hcp : clampN g p ≤ g := by unfold clampN; split <;> omega
  have hcm : clampN g m ≤ g := by unfold clampN; split <;> omega
  have s1 := clamp8_spec inp cap h0 h1 0 t m s n p g c hcap hp hg
  have s2 := move_spec inp cap rK rS (by decide) (clampN g p) (S8 h0 h1 0 t 0 m g s n 0 0 (clampN g p) c) rfl
    (by show clampN g p ≤ cap; omega) (by show s + clampN g p ≤ cap; omega)
  rw [S8_val_S, S8_val_K, S8_setv_K, S8_setv_S] at s2
  have s3 := move_spec inp cap rM rP (by decide) m (S8 h0 h1 0 t 0 m g (s + clampN g p) n 0 0 0 c) rfl
    (by show m ≤ cap; omega) (by show 0 + m ≤ cap; omega)
  rw [S8_val_P, S8_val_M, S8_setv_M, S8_setv_P, Nat.zero_add] at s3
  have s4 := clamp8_spec inp cap h0 h1 0 t 0 (s + clampN g p) n m g c hcap hm hg
  have s5 := move_spec inp cap rK rN (by decide) (clampN g m) (S8 h0 h1 0 t 0 0 g (s + clampN g p) n 0 0 (clampN g m) c)
    rfl (by show clampN g m ≤ cap; omega) (by show n + clampN g m ≤ cap; omega)
  rw [S8_val_N, S8_val_K, S8_setv_K, S8_setv_N] at s5
  have s6 := clear_spec inp cap rG g (S8 h0 h1 0 t 0 0 g (s + clampN g p) (n + clampN g m) 0 0 0 c) rfl
    (by show g ≤ cap; omega)
  rw [S8_setv_G] at s6
  exact RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 s6))))) rfl
    (by omega)

/-! ## Phase 3: the sign -/

/-- `S −= N`; the flag records `S < N`. -/
def sgnL : TProg := .whr rN (.seq (.dec rN) (.ifr rS (.dec rS) (RM.setF rF)))

theorem sgnL_spec (x t p m g a kk : ℕ) (c : Bool) (hcap : 1 ≤ cap) :
    ∀ (n s f : ℕ), f ≤ 1 → n ≤ cap → s ≤ cap →
      RExec inp cap sgnL (S8 h0 h1 x t p m g s n a f kk c)
        (S8 h0 h1 x t p m g (s - n) 0 a (if s < n then 1 else f) kk c) (9 * n + 1) := by
  intro n
  induction n with
  | zero =>
    intro s f _ _ _
    exact RExec.cast inp cap (RExec.whrF (S8_val_N ..)) (by s8_args) le_rfl
  | succ n ih =>
    intro s f hf hn hs
    have d1 := RExec.dec (inp := inp) (cap := cap) rN (S8 h0 h1 x t p m g s (n + 1) a f kk c) hn
    rw [S8_val_N, S8_setv_N, Nat.add_sub_cancel] at d1
    rcases s with _ | s
    · have d2 := setF_spec inp cap rF (S8 h0 h1 x t p m g 0 n a f kk c) hf hcap
      rw [S8_setv_F] at d2
      have ih' := ih 0 1 le_rfl (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show n + 1 ≠ 0; omega) (RExec.seq d1 (RExec.ifrF (S8_val_S ..) d2)) ih')
        (by s8_args) (by omega)
    · have d2 := RExec.dec (inp := inp) (cap := cap) rS (S8 h0 h1 x t p m g (s + 1) n a f kk c) hs
      rw [S8_val_S, S8_setv_S, Nat.add_sub_cancel] at d2
      have ih' := ih s f hf (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show n + 1 ≠ 0; omega)
        (RExec.seq d1 (RExec.ifrT (by show s + 1 ≠ 0; omega) d2)) ih') (by s8_args) (by omega)

/-! ## Phase 4: the table lookup -/

/-- Advance over `S` table entries (not past the table's end). -/
def idxL : TProg := .whr rS (.seq (.dec rS) (.ifs 1 (.seq (RM.fwdC 1 rT) (RM.fwdC 1 rT)) .skip))

theorem idxL_spec (rest : List Bool) (x p m g n a f kk : ℕ) (c : Bool) :
    ∀ (j : ℕ) (W : List Bool) (t : ℕ), (inp 1).drop (h1 + t) = frameP W ++ false :: rest →
      t + 2 * min j W.length ≤ cap → j ≤ cap →
      RExec inp cap idxL (S8 h0 h1 x t p m g j n a f kk c)
        (S8 h0 h1 x (t + 2 * min j W.length) p m g 0 n a f kk c) (16 * j + 1) := by
  intro j
  induction j with
  | zero =>
    intro W t _ _ _
    exact RExec.cast inp cap (RExec.whrF (S8_val_S ..)) (by s8_args) le_rfl
  | succ j ih =>
    intro W t hW ht hj
    have d1 := RExec.dec (inp := inp) (cap := cap) rS (S8 h0 h1 x t p m g (j + 1) n a f kk c) hj
    rw [S8_val_S, S8_setv_S, Nat.add_sub_cancel] at d1
    rcases W with _ | ⟨w, W⟩
    · have hr : readTapeBit (inp 1) (h1 + t) = false := ListEval.read_of_cons (by simpa using hW)
      have ih' := ih [] t hW (by simp at ht ⊢; omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show j + 1 ≠ 0; omega)
        (RExec.seq d1 (RExec.ifsF hr (RExec.skip _))) ih') (by s8_args) (by omega)
    · have hW0 : (inp 1).drop (h1 + t) = true :: w :: (frameP W ++ false :: rest) := by simpa [frameP] using hW
      have hr : readTapeBit (inp 1) (h1 + t) = true := ListEval.read_of_cons hW0
      have hW2 : (inp 1).drop (h1 + (t + 1 + 1)) = frameP W ++ false :: rest := by
        rw [show h1 + (t + 1 + 1) = h1 + t + 1 + 1 by omega]
        exact ListEval.drop_succ_of_cons (ListEval.drop_succ_of_cons hW0)
      simp only [List.length_cons] at ht
      have f1 := fT_spec inp cap h0 h1 x t p m g j n a f kk c (by omega)
      have f2 := fT_spec inp cap h0 h1 x (t + 1) p m g j n a f kk c (by omega)
      have ih' := ih W (t + 1 + 1) hW2 (by omega) (by omega)
      exact RExec.cast inp cap (RExec.whrT (by show j + 1 ≠ 0; omega)
        (RExec.seq d1 (RExec.ifsT hr (RExec.seq f1 f2))) ih') (by s8_args) (by omega)

theorem frameP_drop (r : List Bool) : ∀ (j : ℕ) (W : List Bool),
    (frameP W ++ r).drop (2 * min j W.length) = frameP (W.drop j) ++ r
  | 0, W => by simp
  | j + 1, [] => by simp [frameP]
  | j + 1, w :: W => by
    have e : 2 * min (j + 1) (w :: W).length = 2 * min j W.length + 2 := by simp; omega
    rw [e, Nat.add_comm, ← List.drop_drop]
    simpa [frameP] using frameP_drop r j W

/-! ## The program -/

theorem groups_of_length : ∀ (L : ℕ) (X : List Bool), X.length = 4 * L → groups X = L := by
  intro L
  induction L with
  | zero => intro X hl; rw [List.eq_nil_of_length_eq_zero (by omega : X.length = 0)]; rfl
  | succ L ih =>
    intro X hl
    rcases X with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, X⟩⟩⟩⟩ <;> simp at hl <;> try omega
    rw [groups, ih X (by omega)]

theorem cnt_le_of_length (i : Fin 4) : ∀ (L : ℕ) (X : List Bool), X.length = 4 * L → cnt i X ≤ L := by
  intro L
  induction L with
  | zero => intro X hl; rw [List.eq_nil_of_length_eq_zero (by omega : X.length = 0)]; simp [cnt]
  | succ L ih =>
    intro X hl
    rcases X with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, X⟩⟩⟩⟩ <;> simp at hl <;> try omega
    rw [cnt_group]
    have h1 := ih X (by omega)
    have h2 : (![b0, b1, b2, b3] i).toNat ≤ 1 := Bool.toNat_le _
    omega

/-- The register capacity. -/
def capOf8 (L w p m : ℕ) : ℕ := 8 * L + 2 * w + p + m + 2

/-- One step bound. -/
def cost8 (L w p m : ℕ) : ℕ := 220 * L + 10 * w + 20 * (p + m) + 60

theorem termOk_of_counts (X W : List Bool) (p m L : ℕ) (hg : groups X = L) :
    termOk X W p m = (!decide (cnt 1 X + cnt 2 X + clampN L p < cnt 3 X + clampN L m) &&
      W.getD (cnt 1 X + cnt 2 X + clampN L p - (cnt 3 X + clampN L m)) false) := by
  unfold termOk
  rw [hg]
  simp only []
  by_cases h : cnt 1 X + cnt 2 X + clampN L p < cnt 3 X + clampN L m
  · have h' : ¬ (0 : ℤ) ≤ (cnt 1 X : ℤ) - cnt 3 X + cnt 2 X + clampN L p - clampN L m := by
      have : ((cnt 1 X + cnt 2 X + clampN L p : ℕ) : ℤ) < ((cnt 3 X + clampN L m : ℕ) : ℤ) := by exact_mod_cast h
      push_cast at this
      linarith
    rw [decide_eq_false h', decide_eq_true h]
    rfl
  · have h' : (0 : ℤ) ≤ (cnt 1 X : ℤ) - cnt 3 X + cnt 2 X + clampN L p - clampN L m := by
      have : ((cnt 3 X + clampN L m : ℕ) : ℤ) ≤ ((cnt 1 X + cnt 2 X + clampN L p : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_of_not_lt h
      push_cast at this
      linarith
    have e : ((cnt 1 X : ℤ) - cnt 3 X + cnt 2 X + clampN L p - clampN L m).toNat =
        cnt 1 X + cnt 2 X + clampN L p - (cnt 3 X + clampN L m) := by
      have hle : cnt 3 X + clampN L m ≤ cnt 1 X + cnt 2 X + clampN L p := Nat.le_of_not_lt h
      have : ((cnt 1 X : ℤ) - cnt 3 X + cnt 2 X + clampN L p - clampN L m) =
          ((cnt 1 X + cnt 2 X + clampN L p - (cnt 3 X + clampN L m) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hle]
        ring
      rw [this, Int.toNat_natCast]
    rw [decide_eq_true h', decide_eq_false h, e]
    rfl

end NearCubicWires.WireExponent3_5.FinalPass.Term
