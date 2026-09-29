import Proof.Wire_3_5.FinalPass.SdSamp

/-! # S4 (the seeds phase), part 9: binary counters for the loop over the centers (P3:1206-1216)

The centers are enumerated by table position `(row, col)`, `row < 2^{dRow}`, `col < 2^{dR}` (`sum_centers`); the
positions are kept as `frame (binary d x)` (the center writer's input). On the one-stream layout (`USt`):
**`maxB_spec`** (register `r` becomes `[x ≠ 2^d − 1]`, the word unchanged: `all_binary`), **`resetB_spec`** (the word
becomes `frame (binary d 0)`), next to Sd1's `incB_spec`. On the body's layout, a one-stream piece runs exactly on a
stream `X` with registers `c, r, k` (**`liftUB`**).

Paper quantity of the main type: the table positions of the cell centers (P3:1206-1209), counted in binary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.ThrPt (USt UProg u_fwdC u_rew u_wr u_incR uw_eq)

/-! ## Binary facts -/

theorem all_binary : ∀ (d x : ℕ), x < 2 ^ d → ((binary d x).all id = true ↔ x + 1 = 2 ^ d)
  | 0, x, h => by simp at h; simp [SignedSortKey.binary, h]
  | d + 1, x, h => by
    have ih := all_binary d (x / 2) (by rw [pow_succ] at h; omega)
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx
    · rw [show binary (d + 1) x = false :: binary d (x / 2) by simp [SignedSortKey.binary, hx]]
      simp only [List.all_cons, id_eq, Bool.false_and]
      constructor
      · intro h'; exact absurd h' (by simp)
      · intro h'; rw [pow_succ] at h'; omega
    · rw [show binary (d + 1) x = true :: binary d (x / 2) by simp [SignedSortKey.binary, hx]]
      simp only [List.all_cons, id_eq, Bool.true_and]
      rw [ih, pow_succ]
      omega

theorem binary_zero_rep : ∀ d : ℕ, binary d 0 = List.replicate d false
  | 0 => rfl
  | d + 1 => by simp [SignedSortKey.binary, binary_zero_rep d, List.replicate_succ]

theorem readTapeBit_end (ws R : List Bool) : readTapeBit (frameP ws ++ false :: R) (2 * ws.length) = false := by
  have e := ListEval.readTapeBit_drop (frameP ws ++ false :: R) (2 * ws.length) 0
  simp only [Nat.add_zero] at e
  rw [e, List.drop_left' (by simp)]
  rfl

variable (cap : ℕ)

/-! ## The all-ones test -/

/-- One bit: to the value, the flag `r := 1` when it is `0`, to the next marker. -/
def maxStep : UProg := .seq (WM.fwdC 0 0) (.seq (.ifs 0 .skip (WM.setF 1)) (WM.fwdC 0 0))

/-- The scan. -/
def maxLoop : UProg := .whs 0 maxStep

theorem maxLoop_spec (ws R : List Bool) (hcap : 2 * ws.length + 1 ≤ cap) :
    ∀ (m i : ℕ) (u : USt), ws.length = i + m → u.s = frameP ws ++ false :: R → u.h = 2 * i → u.c = 2 * i →
      u.r ≤ 1 →
      WExec cap maxLoop u.w
        { u with
          h := 2 * ws.length, c := 2 * ws.length, r := if (ws.drop i).all id then u.r else 1 }.w (m * 20 + 1)
  | 0, i, u, hl, hs, hh, hc, _ => by
    have hb : wbit u.w 0 = false := by
      show readTapeBit u.s u.h = false
      rw [hs, hh, show i = ws.length by omega]
      exact readTapeBit_end ws R
    refine WExec.cast cap (WExec.whsF hb) (uw_eq (USt.ext' rfl (by show u.h = 2 * ws.length; omega)
      (by show u.c = 2 * ws.length; omega) ?_ rfl rfl)) (by omega)
    show u.r = if (ws.drop i).all id then u.r else 1
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | m + 1, i, u, hl, hs, hh, hc, hr => by
    have hi : i < ws.length := by omega
    have hb : wbit u.w 0 = true := by
      show readTapeBit u.s u.h = true
      rw [hs, hh]
      exact readTapeBit_frameP_marker ws _ i hi
    have e1 := u_fwdC cap u (by omega)
    obtain ⟨u1, hu1⟩ : ∃ v : USt, v = { u with h := u.h + 1, c := u.c + 1 } := ⟨_, rfl⟩
    rw [← hu1] at e1
    have hbit : wbit u1.w 0 = ws.getD i false := by
      show readTapeBit u1.s u1.h = _
      rw [hu1]
      show readTapeBit u.s (u.h + 1) = _
      rw [hs, hh]
      exact readTapeBit_frameP ws _ i hi
    -- the flag
    obtain ⟨u2, e2, hu2⟩ : ∃ v : USt, WExec cap (.ifs 0 .skip (WM.setF 1)) u1.w v.w 5 ∧
        v = { u1 with r := if ws.getD i false then u1.r else 1 } := by
      have hr1 : u1.r ≤ 1 := by rw [hu1]; exact hr
      by_cases hg : ws.getD i false = true
      · refine ⟨u1, WExec.mono (WExec.ifsT (by rw [hbit, hg]) (WExec.skip _)) (by omega),
          USt.ext' rfl rfl rfl ?_ rfl rfl⟩
        show u1.r = if ws.getD i false = true then u1.r else 1
        rw [if_pos hg]
      · have hg' : ws.getD i false = false := by simpa using hg
        by_cases hr0 : u1.r = 0
        · refine ⟨{ u1 with r := u1.r + 1 }, WExec.mono (WExec.ifsF (by rw [hbit, hg'])
            (WExec.ifrF (show u1.w.val 1 = 0 from hr0) (u_incR cap u1 (by omega)))) (by omega),
            USt.ext' rfl rfl rfl ?_ rfl rfl⟩
          show u1.r + 1 = if ws.getD i false = true then u1.r else 1
          rw [if_neg hg, hr0]
        · refine ⟨u1, WExec.mono (WExec.ifsF (by rw [hbit, hg'])
            (WExec.ifrT (show u1.w.val 1 ≠ 0 from hr0) (WExec.skip _))) (by omega),
            USt.ext' rfl rfl rfl ?_ rfl rfl⟩
          show u1.r = if ws.getD i false = true then u1.r else 1
          rw [if_neg hg]
          omega
    have e3 := u_fwdC cap u2 (by rw [hu2, hu1]; show u.c + 1 < cap; omega)
    have hr2 : u2.r ≤ 1 := by
      have hr1 : u1.r ≤ 1 := by rw [hu1]; exact hr
      rw [hu2]
      show (if ws.getD i false = true then u1.r else 1) ≤ 1
      split
      · exact hr1
      · exact le_rfl
    have ih := maxLoop_spec ws R hcap m (i + 1) { u2 with h := u2.h + 1, c := u2.c + 1 } (by omega)
      (by rw [hu2, hu1]; exact hs) (by rw [hu2, hu1]; show u.h + 1 + 1 = _; omega)
      (by rw [hu2, hu1]; show u.c + 1 + 1 = _; omega) hr2
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) (uw_eq ?_) (by omega)
    rw [hu2, hu1]
    have hd : ws.drop i = ws.getD i false :: ws.drop (i + 1) := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.drop_eq_getElem_cons hi
    refine USt.ext' rfl rfl rfl ?_ rfl rfl
    show (if (ws.drop (i + 1)).all id then (if ws.getD i false = true then u.r else 1) else 1) =
      (if (ws.drop i).all id then u.r else 1)
    rw [hd]
    cases ws.getD i false <;> simp

/-- **The all-ones test**: the scan, then the head back. -/
def maxB : UProg := .seq maxLoop (WM.rewind 0 0)

theorem maxB_spec (d x : ℕ) (hx : x < 2 ^ d) (R : List Bool) (u : USt) (hs : u.s = frameP (binary d x) ++ false :: R)
    (hh : u.h = 0) (hc : u.c = 0) (hr : u.r = 0) (hcap : 2 * d + 1 ≤ cap) :
    WExec cap maxB u.w { u with r := if x + 1 = 2 ^ d then 0 else 1 }.w (d * 20 + 1 + 1 + (5 * (2 * d) + 1)) := by
  have hl := Sample.binary_length'' d x
  have e1 := maxLoop_spec cap (binary d x) R (by rw [hl]; exact hcap) d 0 u (by rw [hl]; omega) hs (by omega)
    (by omega) (by omega)
  have e2 := u_rew cap
    { u with
      h := 2 * (binary d x).length, c := 2 * (binary d x).length,
      r := if ((binary d x).drop 0).all id then u.r else 1 }
    (by show 2 * (binary d x).length ≤ cap; rw [hl]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) (uw_eq (USt.ext' rfl ?_ ?_ ?_ rfl rfl)) (le_of_eq (by rw [hl]))
  · show 2 * (binary d x).length - 2 * (binary d x).length = u.h; omega
  · show 0 = u.c; omega
  · show (if ((binary d x).drop 0).all id then u.r else 1) = if x + 1 = 2 ^ d then 0 else 1
    rw [List.drop_zero, hr]
    by_cases h : x + 1 = 2 ^ d
    · rw [if_pos ((all_binary d x hx).mpr h), if_pos h]
    · rw [if_neg (fun h' => h ((all_binary d x hx).mp h')), if_neg h]

/-! ## The reset -/

/-- One bit zeroed. -/
def rstStep : UProg := .seq (WM.fwdC 0 0) (.seq (.wr 0 false) (WM.fwdC 0 0))

def rstLoop : UProg := .whs 0 rstStep

theorem rstLoop_spec (ws R : List Bool) (hcap : 2 * ws.length + 1 ≤ cap) :
    ∀ (m i : ℕ) (u : USt), ws.length = i + m →
      u.s = frameP (List.replicate i false ++ ws.drop i) ++ false :: R → u.h = 2 * i → u.c = 2 * i →
      WExec cap rstLoop u.w
        { u with
          s := frameP (List.replicate ws.length false) ++ false :: R, h := 2 * ws.length,
          c := 2 * ws.length }.w (m * 20 + 1)
  | 0, i, u, hl, hs, hh, hc => by
    have hi : i = ws.length := by omega
    have hb : wbit u.w 0 = false := by
      show readTapeBit u.s u.h = false
      rw [hs, hh]
      have := readTapeBit_end (List.replicate i false ++ ws.drop i) R
      simp only [List.length_append, List.length_replicate, List.length_drop] at this
      rw [show i + (ws.length - i) = i by omega] at this
      exact this
    refine WExec.cast cap (WExec.whsF hb) (uw_eq (USt.ext' ?_ (by show u.h = 2 * ws.length; omega)
      (by show u.c = 2 * ws.length; omega) rfl rfl rfl)) (by omega)
    show u.s = frameP (List.replicate ws.length false) ++ false :: R
    rw [hs, List.drop_eq_nil_of_le (by omega), List.append_nil, hi]
  | m + 1, i, u, hl, hs, hh, hc => by
    have hi : i < ws.length := by omega
    have hlen : (List.replicate i false ++ ws.drop i).length = ws.length := by simp; omega
    have hb : wbit u.w 0 = true := by
      show readTapeBit u.s u.h = true
      rw [hs, hh]
      exact readTapeBit_frameP_marker _ _ i (by rw [hlen]; exact hi)
    have e1 := u_fwdC cap u (by omega)
    have e2 := u_wr cap { u with h := u.h + 1, c := u.c + 1 } false
    have hw : writeTapeBit u.s (u.h + 1) false =
        frameP (List.replicate (i + 1) false ++ ws.drop (i + 1)) ++ false :: R := by
      rw [hs, hh, frameP_set _ i false _ (by rw [hlen]; exact hi)]
      congr 2
      rw [List.set_append_right _ _ (by simp), List.length_replicate, Nat.sub_self,
        List.drop_eq_getElem_cons hi, List.set_cons_zero, List.replicate_succ', List.append_assoc,
        List.singleton_append]
    have e3 := u_fwdC cap { { u with h := u.h + 1, c := u.c + 1 } with s := writeTapeBit u.s (u.h + 1) false }
      (by show u.c + 1 < cap; omega)
    have ih := rstLoop_spec ws R hcap m (i + 1)
      { { { u with h := u.h + 1, c := u.c + 1 } with s := writeTapeBit u.s (u.h + 1) false } with
        h := u.h + 1 + 1, c := u.c + 1 + 1 } (by omega) (by show writeTapeBit u.s (u.h + 1) false = _; exact hw)
      (by show u.h + 1 + 1 = _; omega) (by show u.c + 1 + 1 = _; omega)
    exact WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih) (uw_eq (USt.ext' rfl rfl rfl rfl rfl rfl))
      (by omega)

/-- **The reset**: every bit `0`, the head back. -/
def resetB : UProg := .seq rstLoop (WM.rewind 0 0)

theorem resetB_spec (d x : ℕ) (R : List Bool) (u : USt) (hs : u.s = frameP (binary d x) ++ false :: R)
    (hh : u.h = 0) (hc : u.c = 0) (hcap : 2 * d + 1 ≤ cap) :
    WExec cap resetB u.w { u with s := frameP (binary d 0) ++ false :: R }.w (d * 20 + 1 + 1 + (5 * (2 * d) + 1)) := by
  have hl := Sample.binary_length'' d x
  have e1 := rstLoop_spec cap (binary d x) R (by rw [hl]; exact hcap) d 0 u (by rw [hl]; omega)
    (by rw [hs]; simp) (by omega) (by omega)
  have e2 := u_rew cap
    { u with
      s := frameP (List.replicate (binary d x).length false) ++ false :: R, h := 2 * (binary d x).length,
      c := 2 * (binary d x).length }
    (by show 2 * (binary d x).length ≤ cap; rw [hl]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) (uw_eq (USt.ext' ?_ ?_ ?_ rfl rfl rfl)) (le_of_eq (by rw [hl]))
  · show frameP (List.replicate (binary d x).length false) ++ false :: R = frameP (binary d 0) ++ false :: R
    rw [hl, binary_zero_rep]
  · show 2 * (binary d x).length - 2 * (binary d x).length = u.h; omega
  · show 0 = u.c; omega

end NearCubicWires.WireExponent3_5.FinalPass.Sd
