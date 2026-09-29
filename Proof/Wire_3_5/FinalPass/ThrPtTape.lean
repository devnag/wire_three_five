import Proof.Wire_3_5.FinalPass.ThrPtLift
import Proof.Wire_3_5.FinalPass.WordLib
import Proof.Wire_3_5.FinalPass.ListEvalRef

/-! # S2 (THR per point), part 12: writing and erasing unary words in place (P3:3170-3178)

On a one-stream layout (`USt`: the stream, its head; registers `0` the head counter, `1` a value, `2` a count):
**`eraseU_spec`** (a unary word `1^n 0` at the head overwritten with blanks), **`writeU_spec`** (register `1`'s
value written as `1^n 0` over whatever is there, the register consumed), **`blankR_spec`** (register `2`'s count of
blank cells written). `wtb_app`: writing at the end of a prefix replaces the next cell or appends one. The pieces
are lifted to any layout by `WExec.liftW_upd` (`tapeL`). Paper quantity: none beyond the machine model (the reports'
word `repWord`, the loop-safe scratch of). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem wtb_app : ∀ (A B : List Bool) (b : Bool), writeTapeBit (A ++ B) A.length b = A ++ b :: B.drop 1
  | [], [], b => rfl
  | [], x :: t, b => rfl
  | a :: A, B, b => by
    have := wtb_app A B b
    simp only [List.cons_append, List.length_cons, writeTapeBit, this]

theorem rtb_app (A B : List Bool) : readTapeBit (A ++ B) A.length = B.headD false := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  cases B <;> rfl

/-- The one-stream layout's programs. -/
abbrev UProg := WM 0 3

/-- The one-stream layout's record. -/
structure USt where
  s : List Bool
  h : ℕ
  c : ℕ
  r : ℕ
  k : ℕ
  cell : Bool

/-- The word state of a record. -/
def USt.w (u : USt) : WState 0 3 := ⟨![u.h], ![u.s], ![u.c, u.r, u.k], u.cell⟩

theorem uw_eq {u u' : USt} (h : u = u') : u.w = u'.w := congrArg USt.w h

theorem USt.ext' {u u' : USt} (h1 : u.s = u'.s) (h2 : u.h = u'.h) (h3 : u.c = u'.c) (h4 : u.r = u'.r)
    (h5 : u.k = u'.k) (h6 : u.cell = u'.cell) : u = u' := by
  cases u; cases u'; simp_all

section UStep
variable (cap : ℕ) (u : USt)

theorem u_wr (b : Bool) : WExec cap (.wr 0 b) u.w { u with s := writeTapeBit u.s u.h b }.w 1 := by
  have e := WExec.wr (cap := cap) (0 : Fin 1) b u.w
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq <;> first | rfl | (funext i; fin_cases i; rfl)

theorem u_fwd : WExec cap (.fwd 0) u.w { u with h := u.h + 1 }.w 1 := by
  have e := WExec.fwd (cap := cap) (0 : Fin 1) u.w
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq <;> first | rfl | (funext i; fin_cases i; rfl)

theorem u_incC (hc : u.c < cap) : WExec cap (.inc 0) u.w { u with c := u.c + 1 }.w 3 := by
  have e := WExec.inc (cap := cap) (0 : Fin 3) u.w hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem u_decR (hc : u.r ≤ cap) : WExec cap (.dec 1) u.w { u with r := u.r - 1 }.w 1 := by
  have e := WExec.dec (cap := cap) (1 : Fin 3) u.w hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem u_decK (hc : u.k ≤ cap) : WExec cap (.dec 2) u.w { u with k := u.k - 1 }.w 1 := by
  have e := WExec.dec (cap := cap) (2 : Fin 3) u.w hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

end UStep

variable (cap : ℕ)

/-- One cell written with `b`, the head on, counted. -/
def wrStep (b : Bool) : UProg := .seq (.wr 0 b) (.seq (.fwd 0) (.inc 0))

theorem wrStep_spec (b : Bool) (u : USt) (A B : List Bool) (hs : u.s = A ++ B) (hh : u.h = A.length)
    (hc : u.c < cap) :
    WExec cap (wrStep b) u.w { u with s := A ++ b :: B.drop 1, h := u.h + 1, c := u.c + 1 }.w 7 := by
  have e1 := u_wr cap u b
  rw [show writeTapeBit u.s u.h b = A ++ b :: B.drop 1 by rw [hs, hh, wtb_app]] at e1
  have e2 := u_fwd cap { u with s := A ++ b :: B.drop 1 }
  have e3 := u_incC cap { { u with s := A ++ b :: B.drop 1 } with h := u.h + 1 } (by simp only; omega)
  exact WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) rfl (by omega)

theorem cons_rep (b : Bool) (n : ℕ) (L : List Bool) : b :: (List.replicate n b ++ L) = List.replicate n b ++ b :: L := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem app_rep (A L : List Bool) (b : Bool) (n : ℕ) :
    A ++ [b] ++ List.replicate n b ++ L = A ++ List.replicate (n + 1) b ++ L := by
  rw [List.append_assoc, List.append_assoc, List.singleton_append, cons_rep, List.replicate_succ',
    List.append_assoc, List.append_assoc, List.singleton_append]

/-! ## Erasing a unary word -/

/-- Overwrite `1^n` with blanks, then the closing `0`. -/
def eraseU : UProg := .seq (.whs 0 (wrStep false)) (wrStep false)

theorem eraseLoop_spec (B : List Bool) :
    ∀ (n : ℕ) (u : USt) (A : List Bool), u.s = A ++ (List.replicate n true ++ false :: B) → u.h = A.length →
      u.c + n ≤ cap →
      WExec cap (.whs 0 (wrStep false)) u.w
        { u with s := A ++ List.replicate n false ++ false :: B, h := u.h + n, c := u.c + n }.w (9 * n + 1)
  | 0, u, A, hs, hh, _ => by
    have hb : wbit u.w 0 = false := by
      show readTapeBit u.s u.h = false
      rw [hs, hh, rtb_app]; rfl
    refine WExec.cast cap (WExec.whsF hb) (uw_eq (USt.ext' ?_ rfl rfl rfl rfl rfl)) (by omega)
    show u.s = _
    rw [hs]; simp
  | n + 1, u, A, hs, hh, hc => by
    have hb : wbit u.w 0 = true := by
      show readTapeBit u.s u.h = true
      rw [hs, hh, rtb_app]; rfl
    have e1 := wrStep_spec cap false u A (List.replicate (n + 1) true ++ false :: B) hs hh (by omega)
    have ih := eraseLoop_spec B n
      { u with s := A ++ false :: (List.replicate (n + 1) true ++ false :: B).drop 1, h := u.h + 1, c := u.c + 1 }
      (A ++ [false]) (by simp [List.replicate_succ]) (by simp [hh]) (by show u.c + 1 + n ≤ cap; omega)
    refine WExec.cast cap (WExec.whsT hb e1 ih) (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl)) (by omega)
    · show A ++ [false] ++ List.replicate n false ++ false :: B = A ++ List.replicate (n + 1) false ++ false :: B
      exact app_rep A (false :: B) false n
    · show u.h + 1 + n = u.h + (n + 1); omega
    · show u.c + 1 + n = u.c + (n + 1); omega

theorem eraseU_spec (A B : List Bool) (n : ℕ) (u : USt) (hs : u.s = A ++ (ListEval.unary n ++ B))
    (hh : u.h = A.length) (hc : u.c + n + 1 ≤ cap) :
    WExec cap eraseU u.w { u with
      s := A ++ List.replicate (n + 1) false ++ B, h := u.h + n + 1, c := u.c + n + 1 }.w (9 * n + 1 + 1 + 7) := by
  have hs' : u.s = A ++ (List.replicate n true ++ false :: B) := by rw [hs]; simp [ListEval.unary]
  have e1 := eraseLoop_spec cap B n u A hs' hh (by omega)
  have e2 := wrStep_spec cap false { u with s := A ++ List.replicate n false ++ false :: B, h := u.h + n, c := u.c + n }
    (A ++ List.replicate n false) (false :: B) (by simp) (by simp [hh]) (by show u.c + n < cap; omega)
  refine WExec.cast cap (WExec.seq e1 e2) (uw_eq (USt.ext' ?_ rfl rfl rfl rfl rfl)) le_rfl
  show A ++ List.replicate n false ++ false :: (false :: B).drop 1 = A ++ List.replicate (n + 1) false ++ B
  simp [List.replicate_succ']

/-! ## Writing a unary word -/

/-- Write register `1`'s value as `1^n 0` (the register consumed). -/
def writeU : UProg := .seq (.whr 1 (.seq (.dec 1) (wrStep true))) (wrStep false)

theorem writeLoop_spec : ∀ (n : ℕ) (u : USt) (A B : List Bool), u.s = A ++ B → u.h = A.length → u.r = n →
    u.c + n ≤ cap → n ≤ cap →
    WExec cap (.whr 1 (.seq (.dec 1) (wrStep true))) u.w
      { u with s := A ++ List.replicate n true ++ B.drop n, h := u.h + n, c := u.c + n, r := 0 }.w (11 * n + 1)
  | 0, u, A, B, hs, hh, hr, _, _ => by
    refine WExec.cast cap (WExec.whrF (show u.w.val 1 = 0 from hr)) (uw_eq (USt.ext' ?_ rfl rfl ?_ rfl rfl))
      (by omega)
    · show u.s = _; rw [hs]; simp
    · show u.r = 0; exact hr
  | n + 1, u, A, B, hs, hh, hr, hc, hn => by
    have e1 := u_decR cap u (by omega)
    have e2 := wrStep_spec cap true { u with r := u.r - 1 } A B hs hh (by show u.c < cap; omega)
    have ih := writeLoop_spec n { { u with r := u.r - 1 } with s := A ++ true :: B.drop 1, h := u.h + 1, c := u.c + 1 }
      (A ++ [true]) (B.drop 1) (by simp) (by simp [hh]) (by show u.r - 1 = n; omega)
      (by show u.c + 1 + n ≤ cap; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show u.w.val 1 ≠ 0 by show u.r ≠ 0; omega) (WExec.seq e1 e2) ih)
      (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl)) (by omega)
    · show A ++ [true] ++ List.replicate n true ++ (B.drop 1).drop n = A ++ List.replicate (n + 1) true ++ B.drop (n + 1)
      rw [List.drop_drop, Nat.add_comm 1 n]
      exact app_rep A (B.drop (n + 1)) true n
    · show u.h + 1 + n = u.h + (n + 1); omega
    · show u.c + 1 + n = u.c + (n + 1); omega

theorem writeU_spec (A B : List Bool) (n : ℕ) (u : USt) (hs : u.s = A ++ B) (hh : u.h = A.length) (hr : u.r = n)
    (hc : u.c + n + 1 ≤ cap) :
    WExec cap writeU u.w { u with
      s := A ++ ListEval.unary n ++ B.drop (n + 1), h := u.h + n + 1, c := u.c + n + 1, r := 0 }.w
      (11 * n + 1 + 1 + 7) := by
  have e1 := writeLoop_spec cap n u A B hs hh hr (by omega) (by omega)
  have e2 := wrStep_spec cap false { u with
      s := A ++ List.replicate n true ++ B.drop n, h := u.h + n, c := u.c + n, r := 0 }
    (A ++ List.replicate n true) (B.drop n) (by simp) (by simp [hh]) (by show u.c + n < cap; omega)
  refine WExec.cast cap (WExec.seq e1 e2) (uw_eq (USt.ext' ?_ rfl rfl rfl rfl rfl)) le_rfl
  show A ++ List.replicate n true ++ false :: (B.drop n).drop 1 = A ++ ListEval.unary n ++ B.drop (n + 1)
  simp [ListEval.unary, List.drop_drop, Nat.add_comm]

/-! ## Blank cells -/

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
