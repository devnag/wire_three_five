import Proof.Wire_3_5.FinalPass.ThrPtRS14

/-! # S2 (THR per point), part 29: copying a count, measuring the table's width (P3:3170-3178)

On the one-stream layout (`USt`): **`cpU_spec`**: register `0` gains register `2`'s value (through register `1`,
register `2` restored). **`measU_spec`**: from the table's first gate — a marker, then the framed `h`-bit word
`1 b 1 b … 1 b 0` — register `2` gets `h` (the pairs counted), the head rewound. The evaluator copies `τ₀` and
`|occs|` into its loop counters and measures stage 2's width `h` this way. Paper quantity: none beyond the machine
model (the table's format, `Corner.gatesW`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ)

theorem u_incK (u : USt) (hc : u.k < cap) : WExec cap (.inc 2) u.w { u with k := u.k + 1 }.w 3 := by
  have e := WExec.inc (cap := cap) (2 : Fin 3) u.w hc
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem u_move21 (u : USt) (hk : u.k ≤ cap) (hr : u.r + u.k ≤ cap) :
    WExec cap (WM.move 2 1) u.w { u with k := 0, r := u.r + u.k }.w (7 * u.k + 1) := by
  have e := wmove_spec cap (2 : Fin 3) 1 (by decide) u.k u.w rfl hk hr
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl
  · rfl

theorem u_fwdC (u : USt) (hc : u.c < cap) : WExec cap (WM.fwdC 0 0) u.w { u with h := u.h + 1, c := u.c + 1 }.w 5 :=
  WExec.cast cap (WExec.seq (u_fwd cap u) (u_incC cap { u with h := u.h + 1 } hc)) rfl le_rfl

/-! ## Copying a count -/

/-- Register `0` gains register `2`'s value (register `1` the temporary). -/
def cpU : UProg := .seq (WM.move 2 1) (.whr 1 (.seq (.dec 1) (.seq (.inc 2) (.inc 0))))

theorem cpLoop_spec : ∀ (n : ℕ) (u : USt), u.r = n → u.k + n ≤ cap → u.c + n ≤ cap → n ≤ cap →
    WExec cap (.whr 1 (.seq (.dec 1) (.seq (.inc 2) (.inc 0)))) u.w
      { u with r := 0, k := u.k + n, c := u.c + n }.w (n * 11 + 1)
  | 0, u, hr, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (show u.w.val 1 = 0 from hr)) (uw_eq (USt.ext' rfl rfl ?_ ?_ ?_ rfl)) (by omega)
    · show u.c = u.c + 0; rfl
    · show u.r = 0; exact hr
    · show u.k = u.k + 0; rfl
  | n + 1, u, hr, hk, hc, hn => by
    have e1 := u_decR cap u (by omega)
    have e2 := u_incK cap { u with r := u.r - 1 } (by show u.k < cap; omega)
    have e3 := u_incC cap { { u with r := u.r - 1 } with k := u.k + 1 } (by show u.c < cap; omega)
    have ih := cpLoop_spec n { { { u with r := u.r - 1 } with k := u.k + 1 } with c := u.c + 1 }
      (by show u.r - 1 = n; omega) (by show u.k + 1 + n ≤ cap; omega) (by show u.c + 1 + n ≤ cap; omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show u.w.val 1 ≠ 0 by show u.r ≠ 0; omega) (WExec.seq e1 (WExec.seq e2 e3)) ih)
      (uw_eq (USt.ext' rfl rfl ?_ rfl ?_ rfl)) (by omega)
    · show u.c + 1 + n = u.c + (n + 1); omega
    · show u.k + 1 + n = u.k + (n + 1); omega

theorem cpU_spec (u : USt) (n : ℕ) (hk : u.k = n) (hr : u.r = 0) (hc : u.c + n ≤ cap) (hn : 2 * n ≤ cap) :
    WExec cap cpU u.w { u with c := u.c + n }.w (7 * n + 1 + 1 + (n * 11 + 1)) := by
  have e1 := u_move21 cap u (by omega) (by omega)
  have e2 := cpLoop_spec cap n { u with k := 0, r := u.r + u.k } (by show u.r + u.k = n; omega)
    (by show 0 + n ≤ cap; omega) (by show u.c + n ≤ cap; omega) (by omega)
  refine WExec.cast cap (WExec.seq e1 e2) (uw_eq (USt.ext' rfl rfl rfl ?_ ?_ rfl)) (by rw [hk])
  · show 0 = u.r; omega
  · show 0 + n = u.k; omega

/-! ## Measuring the width -/

/-- The pairs `1 b` counted into register `2`, then the head rewound (position counter `0`). -/
def measLoop : UProg := .whs 0 (.seq (WM.fwdC 0 0) (.seq (WM.fwdC 0 0) (.inc 2)))

def measU : UProg := .seq (WM.fwdC 0 0) (.seq measLoop (WM.rewind 0 0))

theorem measLoop_spec (h : ℕ) : ∀ (m j : ℕ) (u : USt), (∀ k < h, readTapeBit u.s (1 + 2 * k) = true) →
    readTapeBit u.s (1 + 2 * h) = false → u.h = 1 + 2 * j → u.c = 1 + 2 * j → j + m = h → 2 * h + 1 ≤ cap →
    u.k + m ≤ cap →
    WExec cap measLoop u.w { u with h := 1 + 2 * h, c := 1 + 2 * h, k := u.k + m }.w (m * 17 + 1)
  | 0, j, u, _, hz, hh, hc, hjm, _, _ => by
    have hb : wbit u.w 0 = false := by
      show readTapeBit u.s u.h = false
      rw [hh, show j = h by omega]; exact hz
    refine WExec.cast cap (WExec.whsF hb) (uw_eq (USt.ext' rfl ?_ ?_ rfl ?_ rfl)) (by omega)
    · show u.h = 1 + 2 * h; omega
    · show u.c = 1 + 2 * h; omega
    · show u.k = u.k + 0; rfl
  | m + 1, j, u, hr, hz, hh, hc, hjm, hcap, hk => by
    have hb : wbit u.w 0 = true := by
      show readTapeBit u.s u.h = true
      rw [hh]; exact hr j (by omega)
    have e1 := u_fwdC cap u (by omega)
    have e2 := u_fwdC cap { u with h := u.h + 1, c := u.c + 1 } (by show u.c + 1 < cap; omega)
    have e3 := u_incK cap { { u with h := u.h + 1, c := u.c + 1 } with h := u.h + 1 + 1, c := u.c + 1 + 1 }
      (by show u.k < cap; omega)
    have ih := measLoop_spec h m (j + 1) { { { u with h := u.h + 1, c := u.c + 1 } with
        h := u.h + 1 + 1, c := u.c + 1 + 1 } with k := u.k + 1 } hr hz (by show u.h + 1 + 1 = _; omega)
      (by show u.c + 1 + 1 = _; omega) (by omega) hcap (by show u.k + 1 + m ≤ cap; omega)
    refine WExec.cast cap (WExec.whsT hb (WExec.seq e1 (WExec.seq e2 e3)) ih)
      (uw_eq (USt.ext' rfl rfl rfl rfl ?_ rfl)) (by omega)
    · show u.k + 1 + m = u.k + (m + 1); omega

theorem measU_spec (h : ℕ) (u : USt) (hr : ∀ k < h, readTapeBit u.s (1 + 2 * k) = true)
    (hz : readTapeBit u.s (1 + 2 * h) = false) (hh : u.h = 0) (hc : u.c = 0) (hk : u.k = 0) (hcap : 2 * h + 2 ≤ cap) :
    WExec cap measU u.w { u with k := h }.w (5 + 1 + (h * 17 + 1 + 1 + (5 * (1 + 2 * h) + 1))) := by
  have e1 := u_fwdC cap u (by omega)
  have e2 := measLoop_spec cap h h 0 { u with h := u.h + 1, c := u.c + 1 } hr hz (by show u.h + 1 = _; omega)
    (by show u.c + 1 = _; omega) (by omega) (by omega) (by show u.k + h ≤ cap; omega)
  have e3 := u_rew cap { { u with h := u.h + 1, c := u.c + 1 } with h := 1 + 2 * h, c := 1 + 2 * h, k := u.k + h }
    (by show 1 + 2 * h ≤ cap; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (uw_eq (USt.ext' rfl ?_ ?_ rfl ?_ rfl)) le_rfl
  · show 1 + 2 * h - (1 + 2 * h) = u.h; omega
  · show 0 = u.c; omega
  · show u.k + h = h; omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
