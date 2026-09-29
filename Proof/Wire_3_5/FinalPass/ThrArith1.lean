import Proof.Wire_3_5.FinalPass.ThrRead6

/-! # The THR digit program's register arithmetic, part 1: division with remainder, products modulo `p`

(P3:2543-2551, 2585-2623, W17.) The selection's child index `g_i = (g / Π_{j<i} m_j) mod m_i` is
computed digit by digit with `divmodW` (`Q := X / M`, `Rm := X mod M`, `X` consumed), and the reduced coefficient
`a = (base^i · w) mod p` as `(B_i · (w mod p)) mod p` with `mulLoopW` (`A := (A + S·Y) mod p`, `Y` consumed). Each
routine takes its registers as an embedding `Fin 6 ↪ Fin nr`. Main declarations: `div_step`, `dmLoop_spec`,
**`divmod_spec`**, **`mulLoop_spec`**. Paper quantities: the child index `g_i`, the reduced coefficients `a_i`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

theorem div_step (r n m : ℕ) (hm : 0 < m) : (r + 1) / m + ((r + 1) % m + n) / m = (r + 1 + n) / m := by
  have h := Nat.div_add_mod (r + 1) m
  have e : r + 1 + n = (r + 1) % m + n + m * ((r + 1) / m) := by omega
  rw [e, Nat.add_mul_div_left _ _ hm]; ring

theorem mod_step1 (r n m : ℕ) : ((r + 1) % m + n) % m = (r + (n + 1)) % m := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; congr 1; ring

variable {ns nr : ℕ} (cap : ℕ) (D : Fin 6 ↪ Fin nr)

theorem dne {i j : Fin 6} (h : i ≠ j) : D i ≠ D j := D.injective.ne h

/-! ## Division with remainder -/

/-- The counting loop: per unit of `X`, `Rm := (Rm + 1) mod M` (with `RmD = M − Rm`), a carry into `Q`. -/
def dmLoopW : WM ns nr :=
  .whr (D 0) (.seq (.dec (D 0)) (.seq (incModW (D 3) (D 4)) (.ifr (D 3) .skip (.inc (D 2)))))

theorem dmLoop_spec (m : ℕ) (hm : 1 ≤ m) (hmc : m ≤ cap) :
    ∀ (n : ℕ) (σ : WState ns nr) (q r : ℕ), σ.val (D 0) = n → n ≤ cap → σ.val (D 3) = r → r < m →
      σ.val (D 4) = m - r → σ.val (D 2) = q → q + (r + n) / m ≤ cap →
      WExec cap (dmLoopW D) σ ((((σ.setv (D 0) 0).setv (D 3) ((r + n) % m)).setv (D 4) (m - (r + n) % m)).setv (D 2)
        (q + (r + n) / m)) (n * (7 * m + 17) + 1)
  | 0, σ, q, r, hn, _, hr, hrm, hd, hq, _ => by
    refine WExec.cast cap (WExec.whrF hn) ?_ (by omega)
    rw [Nat.add_zero, Nat.mod_eq_of_lt hrm, Nat.div_eq_of_lt hrm, Nat.add_zero, ThrRead.setv_eq_self σ (D 0) 0 hn]
    refine WState.eq rfl rfl ?_ rfl
    funext x; by_cases h2 : x = D 2
    · rw [h2]; simp [hq]
    · by_cases h4 : x = D 4
      · rw [h4]; simp [Function.update_apply, dne D (show (4 : Fin 6) ≠ 2 by decide), hd]
      · by_cases h3 : x = D 3
        · rw [h3]; simp [Function.update_apply, dne D (show (3 : Fin 6) ≠ 2 by decide),
            dne D (show (3 : Fin 6) ≠ 4 by decide), hr]
        · simp [Function.update_apply, h2, h3, h4]
  | n + 1, σ, q, r, hn, hnc, hr, hrm, hd, hq, hqc => by
    have hpos : 0 < m := by omega
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv (D 0) (σ.val (D 0) - 1) := ⟨_, rfl⟩
    have d1 := WExec.dec (cap := cap) (D 0) σ (by omega)
    rw [← e1] at d1
    have g1 : ∀ i : Fin 6, i ≠ 0 → σ1.val (D i) = σ.val (D i) := fun i hi => by
      rw [e1]; simp [Function.update_apply, dne D hi]
    have d2 := incMod_spec cap (D 3) (D 4) (dne D (by decide)) m r σ1 (by rw [g1 3 (by decide), hr])
      (by rw [g1 4 (by decide), hd]) hrm hmc
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = (σ1.setv (D 3) ((r + 1) % m)).setv (D 4) (m - (r + 1) % m) := ⟨_, rfl⟩
    rw [← e2] at d2
    have v23 : σ2.val (D 3) = (r + 1) % m := by
      rw [e2]; simp [Function.update_apply, dne D (show (3 : Fin 6) ≠ 4 by decide)]
    have v22 : σ2.val (D 2) = q := by
      rw [e2]; simp [Function.update_apply, dne D (show (2 : Fin 6) ≠ 3 by decide),
        dne D (show (2 : Fin 6) ≠ 4 by decide), g1 2 (by decide), hq]
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = if (r + 1) % m = 0 then σ2.setv (D 2) (q + 1) else σ2 := ⟨_, rfl⟩
    have hqd : (r + 1) / m = if (r + 1) % m = 0 then 1 else 0 := by
      by_cases h0 : (r + 1) % m = 0
      · rw [if_pos h0]
        have : r + 1 = m := by
          have := Nat.div_add_mod (r + 1) m
          rcases Nat.lt_or_ge (r + 1) m with hl | hl
          · rw [Nat.mod_eq_of_lt hl] at h0; omega
          · omega
        rw [this, Nat.div_self hpos]
      · rw [if_neg h0]
        have hl : r + 1 < m := by
          rcases Nat.lt_or_ge (r + 1) m with hl | hl
          · exact hl
          · have : r + 1 = m := by omega
            rw [this, Nat.mod_self] at h0; exact absurd rfl h0
        exact Nat.div_eq_of_lt hl
    have d3 : WExec cap (.ifr (D 3) .skip (.inc (D 2))) σ2 σ3 4 := by
      rw [e3]
      by_cases h0 : (r + 1) % m = 0
      · rw [if_pos h0]
        have hi := WExec.inc (cap := cap) (D 2) σ2 (by
          rw [v22]
          have : 1 ≤ (r + (n + 1)) / m := by
            rw [show r + (n + 1) = r + 1 + n by ring, ← div_step r n m hpos, hqd, if_pos h0]; exact Nat.le_add_right 1 _
          exact lt_of_lt_of_le (Nat.lt_add_of_pos_right this) hqc)
        rw [v22] at hi
        exact WExec.ifrF (by rw [v23, h0]) hi
      · rw [if_neg h0]
        exact WExec.mono (WExec.ifrT (by rw [v23]; exact h0) (WExec.skip _)) (by omega)
    have g3 : ∀ i : Fin 6, i ≠ 2 → σ3.val (D i) = σ2.val (D i) := fun i hi => by
      rw [e3]; by_cases h0 : (r + 1) % m = 0
      · rw [if_pos h0]; simp [Function.update_apply, dne D hi]
      · rw [if_neg h0]
    have v32 : σ3.val (D 2) = q + (r + 1) / m := by
      rw [e3, hqd]; by_cases h0 : (r + 1) % m = 0
      · rw [if_pos h0, if_pos h0]; simp
      · rw [if_neg h0, if_neg h0, v22, Nat.add_zero]
    have ih := dmLoop_spec m hm hmc n σ3 (q + (r + 1) / m) ((r + 1) % m)
      (by rw [g3 0 (by decide), e2]; simp [Function.update_apply, dne D (show (0 : Fin 6) ≠ 3 by decide),
        dne D (show (0 : Fin 6) ≠ 4 by decide), e1, hn])
      (by omega) (by rw [g3 3 (by decide), v23]) (Nat.mod_lt _ hpos)
      (by rw [g3 4 (by decide), e2]; simp) v32
      (by rw [Nat.add_assoc, div_step r n m hpos]; rw [show r + (n + 1) = r + 1 + n by ring] at hqc; exact hqc)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by ring_nf; omega)
    rw [mod_step1, Nat.add_assoc, div_step r n m hpos, show r + 1 + n = r + (n + 1) by ring]
    have s3 : σ3.sh = σ.sh ∧ σ3.st = σ.st ∧ σ3.cell = σ.cell := by
      rw [e3, e2, e1]; by_cases h0 : (r + 1) % m = 0
      · rw [if_pos h0]; simp
      · rw [if_neg h0]; simp
    apply WState.eq
    · simp [s3.1]
    · simp [s3.2.1]
    · funext x
      by_cases h2 : x = D 2
      · rw [h2]; simp
      · by_cases h4 : x = D 4
        · rw [h4]; simp [Function.update_apply, dne D (show (4 : Fin 6) ≠ 2 by decide)]
        · by_cases h3 : x = D 3
          · rw [h3]; simp [Function.update_apply, dne D (show (3 : Fin 6) ≠ 2 by decide),
              dne D (show (3 : Fin 6) ≠ 4 by decide)]
          · by_cases h0' : x = D 0
            · rw [h0']; simp [Function.update_apply, dne D (show (0 : Fin 6) ≠ 2 by decide),
                dne D (show (0 : Fin 6) ≠ 4 by decide), dne D (show (0 : Fin 6) ≠ 3 by decide)]
            · simp only [WState.setv_val, Function.update_apply, if_neg h2, if_neg h4, if_neg h3, if_neg h0']
              rw [e3]; by_cases h0 : (r + 1) % m = 0
              · rw [if_pos h0, e2, e1]; simp [Function.update_apply, h2, h3, h4, h0']
              · rw [if_neg h0, e2, e1]; simp [Function.update_apply, h3, h4, h0']
    · simp [s3.2.2]

/-- **Division with remainder**: `Q := X / M`, `Rm := X mod M`, `X := 0` (`RmD`, `T` scratch). -/
def divmodW : WM ns nr := .seq (Hash4.wcopyR (D 1) (D 4) (D 5)) (.seq (dmLoopW D) (WM.clear (D 4)))

theorem divmod_spec (m x : ℕ) (hm : 1 ≤ m) (hmc : m ≤ cap) (hxc : x ≤ cap) (σ : WState ns nr)
    (h0 : σ.val (D 0) = x) (h1 : σ.val (D 1) = m) (h2 : σ.val (D 2) = 0) (h3 : σ.val (D 3) = 0)
    (h4 : σ.val (D 4) = 0) (h5 : σ.val (D 5) = 0) :
    WExec cap (divmodW D) σ (((σ.setv (D 0) 0).setv (D 3) (x % m)).setv (D 2) (x / m))
      (18 * m + 3 + 1 + (x * (7 * m + 17) + 1 + 1 + (3 * m + 1))) := by
  have hpos : 0 < m := by omega
  have d1 := Hash4.wcopyR_spec cap (D 1) (D 4) (D 5) (dne D (by decide)) (dne D (by decide)) (dne D (by decide))
    σ h4 h5 (by omega)
  rw [h1] at d1
  have d2 := dmLoop_spec cap D m hm hmc x (σ.setv (D 4) m) 0 0
    (by simp [Function.update_apply, dne D (show (0 : Fin 6) ≠ 4 by decide), h0]) hxc
    (by simp [Function.update_apply, dne D (show (3 : Fin 6) ≠ 4 by decide), h3]) hpos (by simp)
    (by simp [Function.update_apply, dne D (show (2 : Fin 6) ≠ 4 by decide), h2])
    (by rw [Nat.zero_add, Nat.zero_add]; exact le_trans (Nat.div_le_self _ _) hxc)
  rw [Nat.zero_add, Nat.zero_add] at d2
  have d3 := wclear_spec cap (D 4) (m - x % m)
    (((((σ.setv (D 4) m).setv (D 0) 0).setv (D 3) (x % m)).setv (D 4) (m - x % m)).setv (D 2) (x / m))
    (by simp [Function.update_apply, dne D (show (4 : Fin 6) ≠ 2 by decide)])
    (by simp [Function.update_apply, dne D (show (4 : Fin 6) ≠ 2 by decide)]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext y
  by_cases g4 : y = D 4
  · rw [g4]; simp [Function.update_apply, dne D (show (4 : Fin 6) ≠ 2 by decide),
      dne D (show (4 : Fin 6) ≠ 3 by decide), dne D (show (4 : Fin 6) ≠ 0 by decide), h4]
  · simp [Function.update_apply, g4]

/-! ## Products modulo `p` -/

/-- `A := (A + S·Y) mod p` (with `AD = p − A`), `Y` counted down; `T`, `U` scratch. -/
def mulLoopW : WM ns nr := .whr (D 2) (.seq (.dec (D 2)) (addModW (D 0) (D 1) (D 3) (D 4) (D 5)))

/-- One product step's bound. -/
def mulStep (p : ℕ) : ℕ := 18 * p + 9 + p * (7 * p + 12)

theorem mulLoop_spec (p s : ℕ) (hpc : p ≤ cap) (hsp : s < p) :
    ∀ (n : ℕ) (σ : WState ns nr) (a : ℕ), σ.val (D 2) = n → n ≤ cap → σ.val (D 0) = a → a < p →
      σ.val (D 1) = p - a → σ.val (D 3) = s → σ.val (D 4) = 0 → σ.val (D 5) = 0 →
      WExec cap (mulLoopW D) σ (((σ.setv (D 2) 0).setv (D 0) ((a + s * n) % p)).setv (D 1) (p - (a + s * n) % p))
        (n * mulStep p + 1)
  | 0, σ, a, hn, _, ha, hap, hd, _, _, _ => by
    refine WExec.cast cap (WExec.whrF hn) ?_ (by omega)
    rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hap, ThrRead.setv_eq_self σ (D 2) 0 hn]
    refine WState.eq rfl rfl ?_ rfl
    funext x; by_cases h1 : x = D 1
    · rw [h1]; simp [hd]
    · by_cases h0 : x = D 0
      · rw [h0]; simp [Function.update_apply, dne D (show (0 : Fin 6) ≠ 1 by decide), ha]
      · simp [Function.update_apply, h0, h1]
  | n + 1, σ, a, hn, hnc, ha, hap, hd, hs, hT, hU => by
    have hpos : 0 < p := by omega
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv (D 2) (σ.val (D 2) - 1) := ⟨_, rfl⟩
    have d1 := WExec.dec (cap := cap) (D 2) σ (by omega)
    rw [← e1] at d1
    have g1 : ∀ i : Fin 6, i ≠ 2 → σ1.val (D i) = σ.val (D i) := fun i hi => by
      rw [e1]; simp [Function.update_apply, dne D hi]
    have d2 := addMod_spec cap (D 0) (D 1) (D 3) (D 4) (D 5) (dne D (by decide)) (dne D (by decide))
      (dne D (by decide)) (dne D (by decide)) (dne D (by decide)) (dne D (by decide)) p hpc σ1 a s
      (by rw [g1 4 (by decide), hT]) (by rw [g1 5 (by decide), hU]) (by rw [g1 3 (by decide), hs]) (by omega)
      (by rw [g1 0 (by decide), ha]) (by rw [g1 1 (by decide), hd]) hap
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = ((σ1.setv (D 0) ((a + s) % p)).setv (D 1) (p - (a + s) % p)).setv (D 4) 0 :=
      ⟨_, rfl⟩
    rw [← e2] at d2
    have g2 : ∀ i : Fin 6, i ≠ 0 → i ≠ 1 → i ≠ 4 → σ2.val (D i) = σ1.val (D i) := fun i h0 h1 h4 => by
      rw [e2]; simp [Function.update_apply, dne D h0, dne D h1, dne D h4]
    have ih := mulLoop_spec p s hpc hsp n σ2 ((a + s) % p)
      (by rw [g2 2 (by decide) (by decide) (by decide), e1]; simp [hn]) (by omega)
      (by rw [e2]; simp [Function.update_apply, dne D (show (0 : Fin 6) ≠ 4 by decide),
        dne D (show (0 : Fin 6) ≠ 1 by decide)])
      (Nat.mod_lt _ hpos)
      (by rw [e2]; simp [Function.update_apply, dne D (show (1 : Fin 6) ≠ 4 by decide)])
      (by rw [g2 3 (by decide) (by decide) (by decide), g1 3 (by decide), hs])
      (by rw [e2]; simp)
      (by rw [g2 5 (by decide) (by decide) (by decide), g1 5 (by decide), hU])
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d2) ih) ?_ (by
      unfold mulStep
      have : s * (7 * p + 12) ≤ p * (7 * p + 12) := Nat.mul_le_mul_right _ hsp.le
      ring_nf; ring_nf at this; omega)
    have hm : ((a + s) % p + s * n) % p = (a + s * (n + 1)) % p := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; congr 1; ring
    rw [hm]
    refine WState.eq ?_ ?_ ?_ ?_
    · rw [e2, e1]; rfl
    · rw [e2, e1]; rfl
    · funext x
      by_cases h1 : x = D 1
      · rw [h1]; simp
      · by_cases h0 : x = D 0
        · rw [h0]; simp [Function.update_apply, dne D (show (0 : Fin 6) ≠ 1 by decide)]
        · by_cases h2 : x = D 2
          · rw [h2]; simp [Function.update_apply, dne D (show (2 : Fin 6) ≠ 1 by decide),
              dne D (show (2 : Fin 6) ≠ 0 by decide)]
          · simp only [WState.setv_val, Function.update_apply, if_neg h1, if_neg h0, if_neg h2]
            rw [e2, e1]
            by_cases h4 : x = D 4
            · rw [h4]; simp [Function.update_apply, dne D (show (4 : Fin 6) ≠ 1 by decide),
                dne D (show (4 : Fin 6) ≠ 0 by decide), dne D (show (4 : Fin 6) ≠ 2 by decide), hT]
            · simp [Function.update_apply, h0, h1, h2, h4]
    · rw [e2, e1]; rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrArith
