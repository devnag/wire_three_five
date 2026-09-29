import Proof.Wire_3_5.FinalPass.ThrArith3

/-! # The THR digit program's loops: counted loops and the four guarded circuit slots (W17)

`DigsW` loops over the digits `d < τ₀` and, inside a digit, over the occurrences; the circuits `i < a' ≤ 4` sit on
four fixed payload streams, so the circuit loop is unrolled into four slots guarded by a countdown of `a'`. Both are
stated over an explicit family of states `F k`: `count_spec` (a counted loop from `F 0` to `F n`, one body run per
step) and `circ_spec` (the four slots from `F 0` to `F a'`). Main declarations: `countW`, **`count_spec`**, `gdW`,
`circW`, **`circ_spec`**. Paper quantities: the digit index `d` and the circuit index `i` of row `(g, p)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

variable {ns nr : ℕ} (cap : ℕ)

/-- The counted loop: `C` counted down, `body` once per unit. -/
def countW (C : Fin nr) (body : WM ns nr) : WM ns nr := .whr C (.seq (.dec C) body)

theorem count_aux (C : Fin nr) (body : WM ns nr) (n c : ℕ) (hn : n ≤ cap) (F : ℕ → WState ns nr)
    (hC : ∀ k, k ≤ n → (F k).val C = n - k)
    (hstep : ∀ k, k < n → WExec cap body ((F k).setv C (n - k - 1)) (F (k + 1)) c) :
    ∀ (m k : ℕ), k + m = n → WExec cap (countW C body) (F k) (F n) (m * (c + 4) + 1)
  | 0, k, hk => by
    rw [Nat.add_zero] at hk
    subst hk
    exact WExec.cast cap (WExec.whrF (by rw [hC k le_rfl, Nat.sub_self])) rfl (by omega)
  | m + 1, k, hk => by
    have hv := hC k (by omega)
    have d1 := WExec.dec (cap := cap) C (F k) (by rw [hv]; omega)
    rw [hv, show n - k - 1 = n - k - 1 from rfl] at d1
    have d2 := hstep k (by omega)
    have ih := count_aux C body n c hn F hC hstep m (k + 1) (by omega)
    exact WExec.cast cap (WExec.whrT (by rw [hv]; omega) (WExec.seq d1 d2) ih) rfl (by ring_nf; omega)

/-- **The counted loop** from `F 0` to `F n`. -/
theorem count_spec (C : Fin nr) (body : WM ns nr) (n c : ℕ) (hn : n ≤ cap) (F : ℕ → WState ns nr)
    (hC : ∀ k, k ≤ n → (F k).val C = n - k)
    (hstep : ∀ k, k < n → WExec cap body ((F k).setv C (n - k - 1)) (F (k + 1)) c) :
    WExec cap (countW C body) (F 0) (F n) (n * (c + 4) + 1) :=
  count_aux cap C body n c hn F hC hstep n 0 (by omega)

/-- One guarded slot: if `Ac ≠ 0`, `Ac := Ac − 1` and run `b`. -/
def gdW (Ac : Fin nr) (b : WM ns nr) : WM ns nr := .ifr Ac (.seq (.dec Ac) b) .skip

/-- The four circuit slots. -/
def circW (Ac : Fin nr) (body : Fin 4 → WM ns nr) : WM ns nr :=
  .seq (gdW Ac (body 0)) (.seq (gdW Ac (body 1)) (.seq (gdW Ac (body 2)) (gdW Ac (body 3))))

theorem gd_spec (Ac : Fin nr) (b : WM ns nr) (a c i : ℕ) (hac : a ≤ cap) (F : ℕ → WState ns nr)
    (hA : ∀ k, k ≤ a → (F k).val Ac = a - k)
    (hstep : i < a → WExec cap b ((F i).setv Ac (a - i - 1)) (F (i + 1)) c) :
    WExec cap (gdW Ac b) (F (min i a)) (F (min (i + 1) a)) (c + 3) := by
  by_cases hi : i < a
  · rw [Nat.min_eq_left hi.le, Nat.min_eq_left hi]
    have hv := hA i hi.le
    have d1 := WExec.dec (cap := cap) Ac (F i) (by rw [hv]; omega)
    rw [hv] at d1
    have d2 := hstep hi
    exact WExec.cast cap (WExec.ifrT (by rw [hv]; omega) (WExec.seq d1 d2)) rfl (by omega)
  · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    exact WExec.mono (WExec.ifrF (by rw [hA a le_rfl, Nat.sub_self]) (WExec.skip _)) (by omega)

/-- **The four guarded slots** from `F 0` to `F a` (`a ≤ 4`). -/
theorem circ_spec (Ac : Fin nr) (body : Fin 4 → WM ns nr) (a c : ℕ) (ha : a ≤ 4) (hac : a ≤ cap)
    (F : ℕ → WState ns nr) (hA : ∀ k, k ≤ a → (F k).val Ac = a - k)
    (hstep : ∀ i : Fin 4, i.val < a → WExec cap (body i) ((F i.val).setv Ac (a - i.val - 1)) (F (i.val + 1)) c) :
    WExec cap (circW Ac body) (F 0) (F a) (4 * (c + 3) + 3) := by
  have g0 := gd_spec cap Ac (body 0) a c 0 hac F hA (hstep 0)
  have g1 := gd_spec cap Ac (body 1) a c 1 hac F hA (hstep 1)
  have g2 := gd_spec cap Ac (body 2) a c 2 hac F hA (hstep 2)
  have g3 := gd_spec cap Ac (body 3) a c 3 hac F hA (hstep 3)
  have e0 : min 0 a = 0 := Nat.zero_min a
  have e4 : min (3 + 1) a = a := Nat.min_eq_right (by omega)
  rw [e0] at g0
  rw [e4] at g3
  exact WExec.cast cap (WExec.seq g0 (WExec.seq g1 (WExec.seq g2 g3))) rfl (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.ThrArith
