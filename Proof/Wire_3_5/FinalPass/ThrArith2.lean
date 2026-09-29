import Proof.Wire_3_5.FinalPass.ThrArith1

/-! # The THR digit program's register arithmetic, part 2: one binary digit of a residue

(P3:2596-2599, W17.) Digit `d` of the reduced coefficient `a` in base `b₀ = 2` is `a / 2^d mod 2`
(`Primitive.digitOf`). `halfW` halves a register (quotient added to `H2`, parity into `Rb`); `bitOfW` copies `a` and
`d`, halves `d` times, and leaves the parity: `Rb := a / 2^d mod 2`, every other register as it was. Main
declarations: `half_spec`, `halvings_spec`, **`bitOf_spec`**. Paper quantity: the digit `v_{i,d}` of `a_i`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Halving -/

/-- `H2 += Hq / 2`, `Rb := Hq mod 2` (from `Rb = 0`), `Hq := 0`. -/
def halfW (Hq H2 Rb : Fin nr) : WM ns nr :=
  .whr Hq (.seq (.dec Hq) (.ifr Hq (.seq (.dec Hq) (.inc H2)) (.inc Rb)))

theorem half_spec (Hq H2 Rb : Fin nr) (h01 : Hq ≠ H2) (h02 : Hq ≠ Rb) (h12 : H2 ≠ Rb) (hc1 : 1 ≤ cap) :
    ∀ (h : ℕ) (σ : WState ns nr) (q : ℕ), σ.val Hq = h → h ≤ cap → σ.val H2 = q → σ.val Rb = 0 → q + h / 2 ≤ cap →
      WExec cap (halfW Hq H2 Rb) σ (((σ.setv Hq 0).setv H2 (q + h / 2)).setv Rb (h % 2)) (5 * h + 9)
  | 0, σ, q, hh, _, hq, hr, _ => by
    refine WExec.cast cap (WExec.whrF hh) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext x; by_cases x2 : x = Rb
    · rw [x2]; simp [hr]
    · by_cases x1 : x = H2
      · rw [x1]; simp [Function.update_apply, h12, hq]
      · by_cases x0 : x = Hq
        · rw [x0]; simp [Function.update_apply, h01, h02, hh]
        · simp [Function.update_apply, x0, x1, x2]
  | 1, σ, q, hh, _, hq, hr, hqc => by
    have d1 := WExec.dec (cap := cap) Hq σ (by omega)
    have d2 := WExec.inc (cap := cap) Rb (σ.setv Hq (σ.val Hq - 1)) (by simp [Function.update_apply, Ne.symm h02, hr]; omega)
    have d3 := WExec.ifrF (r := Hq) (P := WM.seq (.dec Hq) (.inc H2)) (by simp [hh]) d2
    have d4 := WExec.whrF (cap := cap) (r := Hq) (P := WM.seq (.dec Hq) (.ifr Hq (.seq (.dec Hq) (.inc H2)) (.inc Rb)))
      (σ := (σ.setv Hq (σ.val Hq - 1)).setv Rb ((σ.setv Hq (σ.val Hq - 1)).val Rb + 1))
      (by simp [Function.update_apply, h02, hh])
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d3) d4) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext x; by_cases x2 : x = Rb
    · rw [x2]; simp [Function.update_apply, Ne.symm h02, hr]
    · by_cases x1 : x = H2
      · rw [x1]; simp [Function.update_apply, h12, h01.symm, hq]
      · by_cases x0 : x = Hq
        · rw [x0]; simp [Function.update_apply, h01, h02, hh]
        · simp [Function.update_apply, x0, x1, x2]
  | h + 2, σ, q, hh, hc, hq, hr, hqc => by
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv Hq (σ.val Hq - 1) := ⟨_, rfl⟩
    have d1 := WExec.dec (cap := cap) Hq σ (by omega)
    rw [← e1] at d1
    have d2 := WExec.dec (cap := cap) Hq σ1 (by rw [e1]; simp; omega)
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = σ1.setv Hq (σ1.val Hq - 1) := ⟨_, rfl⟩
    rw [← e2] at d2
    have d3 := WExec.inc (cap := cap) H2 σ2 (by
      rw [e2, e1]; simp [Function.update_apply, Ne.symm h01, hq]
      have : 1 ≤ (h + 2) / 2 := by omega
      omega)
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setv H2 (σ2.val H2 + 1) := ⟨_, rfl⟩
    rw [← e3] at d3
    have d4 := WExec.ifrT (r := Hq) (Q := WM.inc Rb) (by rw [e1]; simp; omega) (WExec.seq d2 d3)
    have ih := half_spec Hq H2 Rb h01 h02 h12 hc1 h σ3 (q + 1)
      (by rw [e3, e2, e1]; simp [Function.update_apply, h01, hh]) (by omega)
      (by rw [e3, e2, e1]; simp [Function.update_apply, Ne.symm h01, hq])
      (by rw [e3, e2, e1]; simp [Function.update_apply, Ne.symm h12, Ne.symm h02, hr])
      (by have : (h + 2) / 2 = h / 2 + 1 := by omega
          omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d4) ih) ?_ (by omega)
    have e5 : q + 1 + h / 2 = q + (h + 2) / 2 := by omega
    have e6 : h % 2 = (h + 2) % 2 := by omega
    rw [e5, e6]
    refine WState.eq ?_ ?_ ?_ ?_
    · rw [e3, e2, e1]; rfl
    · rw [e3, e2, e1]; rfl
    · funext x; by_cases x2 : x = Rb
      · rw [x2]; simp
      · by_cases x1 : x = H2
        · rw [x1]; simp [Function.update_apply, h12]
        · by_cases x0 : x = Hq
          · rw [x0]; simp [Function.update_apply, h01, h02]
          · simp [Function.update_apply, x0, x1, x2, e3, e2, e1]
    · rw [e3, e2, e1]; rfl

/-- The halving step's bound, for values up to `a`. -/
def halfCost (a : ℕ) : ℕ := 12 * a + 20

/-- `Dc` halvings of `Hq` (each: halve, clear the parity, move the quotient back). -/
def halvingsW (Hq H2 Rb Dc : Fin nr) : WM ns nr :=
  .whr Dc (.seq (.dec Dc) (.seq (halfW Hq H2 Rb) (.seq (WM.clear Rb) (WM.move H2 Hq))))

theorem halvings_spec (Hq H2 Rb Dc : Fin nr) (h01 : Hq ≠ H2) (h02 : Hq ≠ Rb) (h12 : H2 ≠ Rb) (h03 : Hq ≠ Dc)
    (h13 : H2 ≠ Dc) (h23 : Rb ≠ Dc) (a : ℕ) (hac : a ≤ cap) (hc1 : 1 ≤ cap) :
    ∀ (k : ℕ) (σ : WState ns nr) (h : ℕ), σ.val Dc = k → k ≤ cap → σ.val Hq = h → h ≤ a → σ.val H2 = 0 →
      σ.val Rb = 0 →
      WExec cap (halvingsW Hq H2 Rb Dc) σ ((σ.setv Dc 0).setv Hq (h / 2 ^ k)) (k * halfCost a + 1)
  | 0, σ, h, hk, _, hh, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hk) ?_ (by omega)
    rw [pow_zero, Nat.div_one, ThrRead.setv_eq_self σ Dc 0 hk, ThrRead.setv_eq_self σ Hq h hh]
  | k + 1, σ, h, hk, hkc, hh, hha, h2, hr => by
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv Dc (σ.val Dc - 1) := ⟨_, rfl⟩
    have d1 := WExec.dec (cap := cap) Dc σ (by omega)
    rw [← e1] at d1
    have d2 := half_spec cap Hq H2 Rb h01 h02 h12 hc1 h σ1 0 (by rw [e1]; simp [Function.update_apply, h03, hh])
      (by omega) (by rw [e1]; simp [Function.update_apply, h13, h2]) (by rw [e1]; simp [Function.update_apply, h23, hr])
      (by have := Nat.div_le_self h 2; omega)
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = ((σ1.setv Hq 0).setv H2 (0 + h / 2)).setv Rb (h % 2) := ⟨_, rfl⟩
    rw [← e2] at d2
    have d3 := wclear_spec cap Rb (h % 2) σ2 (by rw [e2]; simp) (by rw [e2]; simp; omega)
    have hv : (σ2.setv Rb 0).val H2 = h / 2 := by rw [e2]; simp [Function.update_apply, h12]
    have hv' : (σ2.setv Rb 0).val Hq = 0 := by rw [e2]; simp [Function.update_apply, h02, h01]
    have d4 := wmove_spec cap H2 Hq (Ne.symm h01) (h / 2) (σ2.setv Rb 0) hv
      (by rw [hv]; have := Nat.div_le_self h 2; omega)
      (by rw [hv', hv]; have := Nat.div_le_self h 2; omega)
    rw [hv, hv', Nat.zero_add] at d4
    obtain ⟨σ4, e4⟩ : ∃ τ, τ = ((σ2.setv Rb 0).setv H2 0).setv Hq (h / 2) := ⟨_, rfl⟩
    rw [← e4] at d4
    have body : WExec cap (.seq (.dec Dc) (.seq (halfW Hq H2 Rb) (.seq (WM.clear Rb) (WM.move H2 Hq)))) σ σ4
        (halfCost a - 2) := by
      refine WExec.mono (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ?_
      unfold halfCost
      have : h % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have := Nat.div_le_self h 2
      omega
    have ih := halvings_spec Hq H2 Rb Dc h01 h02 h12 h03 h13 h23 a hac hc1 k σ4 (h / 2)
      (by rw [e4, e2, e1]; simp [Function.update_apply, Ne.symm h03, Ne.symm h13, Ne.symm h23, hk])
      (by omega) (by rw [e4]; simp) (by have := Nat.div_le_self h 2; omega)
      (by rw [e4]; simp [Function.update_apply, h01.symm])
      (by rw [e4]; simp [Function.update_apply, h02.symm, h12.symm])
    refine WExec.cast cap (WExec.whrT (by omega) body ih) ?_ (by
      unfold halfCost; rw [Nat.add_mul, Nat.one_mul]; omega)
    have hdiv : h / 2 / 2 ^ k = h / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    rw [hdiv]
    refine WState.eq ?_ ?_ ?_ ?_
    · rw [e4, e2, e1]; rfl
    · rw [e4, e2, e1]; rfl
    · funext x; by_cases x0 : x = Hq
      · rw [x0]; simp
      · by_cases x3 : x = Dc
        · rw [x3]; simp [Function.update_apply, Ne.symm h03]
        · simp only [WState.setv_val, Function.update_apply, if_neg x0, if_neg x3]
          rw [e4, e2, e1]
          by_cases x1 : x = H2
          · rw [x1]; simp [Function.update_apply, h12, h01.symm, h2]
          · by_cases x2 : x = Rb
            · rw [x2]; simp [Function.update_apply, h02.symm, hr]
            · simp [Function.update_apply, x0, x1, x2, x3]
    · rw [e4, e2, e1]; rfl

/-! ## One binary digit -/

/-- `Rb := A / 2^D mod 2` with the registers `B 0 = A`, `B 1 = D`, `B 2 = Hq`, `B 3 = H2`, `B 4 = Rb`, `B 5 = Dc`,
`B 6 = T` (scratch zero, restored). -/
def bitOfW (B : Fin 7 ↪ Fin nr) : WM ns nr :=
  .seq (Hash4.wcopyR (B 0) (B 2) (B 6)) (.seq (Hash4.wcopyR (B 1) (B 5) (B 6))
    (.seq (halvingsW (B 2) (B 3) (B 4) (B 5)) (.seq (halfW (B 2) (B 3) (B 4)) (WM.clear (B 3)))))

/-- `bitOfW`'s bound for values up to `a` and `d` halvings. -/
def bitOfCost (a d : ℕ) : ℕ := 18 * a + 3 + 1 + (18 * d + 3 + 1 + (d * halfCost a + 1 + 1 + (5 * a + 9 + 1 + (3 * a + 1))))

theorem bitOf_spec (B : Fin 7 ↪ Fin nr) (a d : ℕ) (hac : a ≤ cap) (hdc : d ≤ cap) (hc1 : 1 ≤ cap)
    (σ : WState ns nr) (h0 : σ.val (B 0) = a) (h1 : σ.val (B 1) = d) (h2 : σ.val (B 2) = 0)
    (h3 : σ.val (B 3) = 0) (h4 : σ.val (B 4) = 0) (h5 : σ.val (B 5) = 0) (h6 : σ.val (B 6) = 0) :
    WExec cap (bitOfW B) σ (σ.setv (B 4) (a / 2 ^ d % 2)) (bitOfCost a d) := by
  have v : ∀ i j : Fin 7, i ≠ j → B i ≠ B j := fun i j h => B.injective.ne h
  have d1 := Hash4.wcopyR_spec cap (B 0) (B 2) (B 6) (v 0 2 (by decide)) (v 0 6 (by decide)) (v 2 6 (by decide))
    σ h2 h6 (by omega)
  rw [h0] at d1
  have d2 := Hash4.wcopyR_spec cap (B 1) (B 5) (B 6) (v 1 5 (by decide)) (v 1 6 (by decide)) (v 5 6 (by decide))
    (σ.setv (B 2) a) (by simp [Function.update_apply, v 5 2 (by decide), h5])
    (by simp [Function.update_apply, v 6 2 (by decide), h6])
    (by simp [Function.update_apply, v 1 2 (by decide), h1]; omega)
  rw [show (σ.setv (B 2) a).val (B 1) = d by simp [Function.update_apply, v 1 2 (by decide), h1]] at d2
  have d3 := halvings_spec cap (B 2) (B 3) (B 4) (B 5) (v 2 3 (by decide)) (v 2 4 (by decide)) (v 3 4 (by decide))
    (v 2 5 (by decide)) (v 3 5 (by decide)) (v 4 5 (by decide)) a hac hc1 d ((σ.setv (B 2) a).setv (B 5) d) a
    (by simp) hdc (by simp [Function.update_apply, v 2 5 (by decide)]) le_rfl
    (by simp [Function.update_apply, v 3 5 (by decide), v 3 2 (by decide), h3])
    (by simp [Function.update_apply, v 4 5 (by decide), v 4 2 (by decide), h4])
  have hq := Nat.div_le_self a (2 ^ d)
  have d4 := half_spec cap (B 2) (B 3) (B 4) (v 2 3 (by decide)) (v 2 4 (by decide)) (v 3 4 (by decide)) hc1
    (a / 2 ^ d) ((((σ.setv (B 2) a).setv (B 5) d).setv (B 5) 0).setv (B 2) (a / 2 ^ d)) 0 (by simp) (by omega)
    (by simp [Function.update_apply, v 3 2 (by decide), v 3 5 (by decide), h3])
    (by simp [Function.update_apply, v 4 2 (by decide), v 4 5 (by decide), h4])
    (by have := Nat.div_le_self (a / 2 ^ d) 2; omega)
  have d5 := wclear_spec cap (B 3) (0 + a / 2 ^ d / 2)
    (((((((σ.setv (B 2) a).setv (B 5) d).setv (B 5) 0).setv (B 2) (a / 2 ^ d)).setv (B 2) 0).setv (B 3)
      (0 + a / 2 ^ d / 2)).setv (B 4) (a / 2 ^ d % 2))
    (by simp [Function.update_apply, v 3 4 (by decide)])
    (by simp [Function.update_apply, v 3 4 (by decide)]; have := Nat.div_le_self (a / 2 ^ d) 2; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 d5)))) ?_ (by
    unfold bitOfCost; have := Nat.div_le_self (a / 2 ^ d) 2; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext x
  by_cases x4 : x = B 4
  · rw [x4]; simp [Function.update_apply, v 4 3 (by decide)]
  · by_cases x3 : x = B 3
    · rw [x3]; simp [Function.update_apply, x4, h3]
    · by_cases x2 : x = B 2
      · rw [x2]; simp [Function.update_apply, v 2 3 (by decide), v 2 4 (by decide), h2]
      · by_cases x5 : x = B 5
        · rw [x5]; simp [Function.update_apply, v 5 3 (by decide), v 5 4 (by decide), v 5 2 (by decide), h5]
        · simp [Function.update_apply, x2, x3, x4, x5]

end NearCubicWires.WireExponent3_5.FinalPass.ThrArith
