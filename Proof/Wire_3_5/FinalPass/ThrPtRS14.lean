import Proof.Wire_3_5.FinalPass.ThrPtRS13

/-! # S2 (THR per point), part 28: formatting a scratch stream

On the one-stream layout (`USt`): `wrList pat` writes the cells of `pat`; `patLoop pat` writes `pat` register `2`'s
count of times (the count moved into register `1` as it goes); **`fmtW_spec`**: `fmtW pat` writes `pat^n 0` from the
head `0` over whatever is there, the count restored, the head rewound. It formats the evaluator's scratch before the
rows (the frames of stage 2's accumulators, the corner word's cells, the population's cells) and blanks it after.
Paper quantity: none beyond the machine model (loop-safe scratch). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ)

theorem u_incR (u : USt) (hc : u.r < cap) : WExec cap (.inc 1) u.w { u with r := u.r + 1 }.w 3 := by
  have e := WExec.inc (cap := cap) (1 : Fin 3) u.w hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem u_move12 (u : USt) (hr : u.r ≤ cap) (hk : u.k + u.r ≤ cap) :
    WExec cap (WM.move 1 2) u.w { u with r := 0, k := u.k + u.r }.w (7 * u.r + 1) := by
  have e := wmove_spec cap (1 : Fin 3) 2 (by decide) u.r u.w rfl hr hk
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem u_rew (u : USt) (hc : u.c ≤ cap) :
    WExec cap (WM.rewind 0 0) u.w { u with c := 0, h := u.h - u.c }.w (5 * u.c + 1) := by
  have e := wrewind_spec cap (0 : Fin 1) (0 : Fin 3) u.c u.w rfl hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · funext i; fin_cases i; rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

/-- The cells of `pat`, in turn. -/
def wrList : List Bool → UProg
  | [] => .skip
  | b :: pat => .seq (wrStep b) (wrList pat)

theorem wrList_spec : ∀ (pat : List Bool) (u : USt) (A B : List Bool), u.s = A ++ B → u.h = A.length →
    u.c + pat.length ≤ cap →
    WExec cap (wrList pat) u.w
      { u with s := A ++ pat ++ B.drop pat.length, h := u.h + pat.length, c := u.c + pat.length }.w
      (8 * pat.length)
  | [], u, A, B, hs, hh, _ => by
    refine WExec.cast cap (WExec.skip u.w) (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl)) (by simp)
    · show u.s = _; rw [hs]; simp
    · show u.h = u.h + 0; rfl
    · show u.c = u.c + 0; rfl
  | b :: pat, u, A, B, hs, hh, hc => by
    simp only [List.length_cons] at hc
    have e1 := wrStep_spec cap b u A B hs hh (by omega)
    have ih := wrList_spec pat { u with s := A ++ b :: B.drop 1, h := u.h + 1, c := u.c + 1 } (A ++ [b]) (B.drop 1)
      (by simp) (by simp [hh]) (by show u.c + 1 + pat.length ≤ cap; omega)
    refine WExec.cast cap (WExec.seq e1 ih) (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl)) (by simp only [List.length_cons]; omega)
    · show A ++ [b] ++ pat ++ (B.drop 1).drop pat.length = A ++ b :: pat ++ B.drop (pat.length + 1)
      rw [List.drop_drop, Nat.add_comm 1 pat.length]
      simp
    · show u.h + 1 + pat.length = u.h + (pat.length + 1); omega
    · show u.c + 1 + pat.length = u.c + (pat.length + 1); omega

theorem flat_len (pat : List Bool) : ∀ n : ℕ, ((List.replicate n pat).flatten).length = n * pat.length
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, List.length_append, flat_len pat n, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

/-- `pat`, register `2`'s count of times (the count moved into register `1`). -/
def patLoop (pat : List Bool) : UProg := .whr 2 (.seq (.dec 2) (.seq (.inc 1) (wrList pat)))

theorem patLoop_spec (pat : List Bool) : ∀ (n : ℕ) (u : USt) (A B : List Bool), u.s = A ++ B → u.h = A.length →
    u.k = n → u.c + n * pat.length ≤ cap → u.r + n ≤ cap → n ≤ cap →
    WExec cap (patLoop pat) u.w
      { u with s := A ++ (List.replicate n pat).flatten ++ B.drop (n * pat.length), h := u.h + n * pat.length,
               c := u.c + n * pat.length, r := u.r + n, k := 0 }.w (n * (8 * pat.length + 8) + 1)
  | 0, u, A, B, hs, hh, hk, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (show u.w.val 2 = 0 from hk)) (uw_eq (USt.ext' ?_ ?_ ?_ ?_ ?_ rfl)) (by omega)
    · show u.s = _; rw [hs]; simp
    · show u.h = u.h + 0 * pat.length; simp
    · show u.c = u.c + 0 * pat.length; simp
    · show u.r = u.r + 0; rfl
    · show u.k = 0; exact hk
  | n + 1, u, A, B, hs, hh, hk, hc, hr, hn => by
    have hm : (n + 1) * pat.length = pat.length + n * pat.length := by ring
    rw [hm] at hc
    have e1 := u_decK cap u (by omega)
    have e2 := u_incR cap { u with k := u.k - 1 } (by show u.r < cap; omega)
    have e3 := wrList_spec cap pat { { u with k := u.k - 1 } with r := u.r + 1 } A B hs hh
      (by show u.c + pat.length ≤ cap; omega)
    have ih := patLoop_spec pat n { { { u with k := u.k - 1 } with r := u.r + 1 } with
        s := A ++ pat ++ B.drop pat.length, h := u.h + pat.length, c := u.c + pat.length }
      (A ++ pat) (B.drop pat.length) rfl (by simp [hh]) (by show u.k - 1 = n; omega)
      (by show u.c + pat.length + n * pat.length ≤ cap; omega) (by show u.r + 1 + n ≤ cap; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show u.w.val 2 ≠ 0 by show u.k ≠ 0; omega) (WExec.seq e1 (WExec.seq e2 e3)) ih)
      (uw_eq (USt.ext' ?_ ?_ ?_ ?_ rfl rfl)) (by rw [Nat.add_mul, Nat.one_mul]; omega)
    · show A ++ pat ++ (List.replicate n pat).flatten ++ (B.drop pat.length).drop (n * pat.length) =
        A ++ (List.replicate (n + 1) pat).flatten ++ B.drop ((n + 1) * pat.length)
      rw [List.drop_drop, hm, List.replicate_succ, List.flatten_cons]
      simp only [List.append_assoc]
    · show u.h + pat.length + n * pat.length = u.h + (n + 1) * pat.length; rw [hm]; omega
    · show u.c + pat.length + n * pat.length = u.c + (n + 1) * pat.length; rw [hm]; omega
    · show u.r + 1 + n = u.r + (n + 1); omega

/-- **A scratch stream formatted**: `pat^n 0` from the head `0`, the count restored, the head rewound. -/
def fmtW (pat : List Bool) : UProg := .seq (patLoop pat) (.seq (WM.move 1 2) (.seq (wrStep false) (WM.rewind 0 0)))

/-- `fmtW`'s step bound. -/
def fmtCost (n l : ℕ) : ℕ := n * (8 * l + 8) + 1 + 1 + ((7 * n + 1) + 1 + (7 + 1 + (5 * (n * l + 1) + 1)))

theorem fmtW_spec (pat : List Bool) (n : ℕ) (u : USt) (B : List Bool) (hs : u.s = B) (hh : u.h = 0) (hc0 : u.c = 0)
    (hr0 : u.r = 0) (hk : u.k = n) (hc : n * pat.length + 1 ≤ cap) (hn : n ≤ cap) :
    WExec cap (fmtW pat) u.w
      { u with s := (List.replicate n pat).flatten ++ false :: B.drop (n * pat.length + 1), h := 0, c := 0, r := 0,
               k := n }.w (fmtCost n pat.length) := by
  have e1 := patLoop_spec cap pat n u [] B (by rw [hs, List.nil_append]) (by rw [hh, List.length_nil]) hk (by omega) (by omega) hn
  have e2 := u_move12 cap { u with
      s := [] ++ (List.replicate n pat).flatten ++ B.drop (n * pat.length), h := u.h + n * pat.length,
      c := u.c + n * pat.length, r := u.r + n, k := 0 } (by show u.r + n ≤ cap; omega)
    (by show 0 + (u.r + n) ≤ cap; omega)
  have e3 := wrStep_spec cap false { { u with
      s := [] ++ (List.replicate n pat).flatten ++ B.drop (n * pat.length), h := u.h + n * pat.length,
      c := u.c + n * pat.length, r := u.r + n, k := 0 } with r := 0, k := 0 + (u.r + n) }
    ((List.replicate n pat).flatten) (B.drop (n * pat.length)) (by simp)
    (by show u.h + n * pat.length = _; rw [flat_len, hh, Nat.zero_add]) (by show u.c + n * pat.length < cap; omega)
  have e4 := u_rew cap { { { u with
      s := [] ++ (List.replicate n pat).flatten ++ B.drop (n * pat.length), h := u.h + n * pat.length,
      c := u.c + n * pat.length, r := u.r + n, k := 0 } with r := 0, k := 0 + (u.r + n) } with
      s := (List.replicate n pat).flatten ++ false :: (B.drop (n * pat.length)).drop 1,
      h := u.h + n * pat.length + 1, c := u.c + n * pat.length + 1 } (by show u.c + n * pat.length + 1 ≤ cap; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (uw_eq (USt.ext' ?_ ?_ rfl ?_ ?_ rfl))
    (by unfold fmtCost; simp only [hr0, hc0]; omega)
  · show (List.replicate n pat).flatten ++ false :: (B.drop (n * pat.length)).drop 1 =
      (List.replicate n pat).flatten ++ false :: B.drop (n * pat.length + 1)
    rw [List.drop_drop]
  · show u.h + n * pat.length + 1 - (u.c + n * pat.length + 1) = 0; omega
  · show 0 = 0; rfl
  · show 0 + (u.r + n) = n; omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
