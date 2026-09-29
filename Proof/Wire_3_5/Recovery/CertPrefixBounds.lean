import Proof.Wire_3_5.Recovery.CertScanLoop

/-! # The prefix's capacities (P3:3758-3759; D1.6, the prefix stage)

Realizes the resource side of "The resulting slice is computable in `E^NP`" (P3:3758) for the prefix: the scan's banks
need three capacities computed from the input length alone, a value capacity `C₁ ≥` every schedule value
`((v−u)^j(v−2u))^{16}L³`, `(v^j·2v)^{16}` with `j ≤ n` (the loop at `c = n` rounds), a round capacity `C₂ ≥` the
schedule round's time, and a scan capacity `C₃ ≥` the scan round's time. Each is base's `CloseoutCapacity.capacity e e n
= 2^{e n + e}` (computed by base's `CloseoutCapacity.machine`), and each constraint is a polynomial in `2^n + 1`
(`q(2^a) = O(a log a)`, `L ≤ q + 2`, values `2^{O(n)}`), so a fixed `e` suffices for every `n` (base's
`Closeout.recovery_budget`).

Paper quantity: the polynomial clock of the prefix; **`prefix_caps`**: `∃ e₁ e₂ e₃`, for every `n`, the capacities
`C_i = capacity e_i e_i n` satisfy the hypotheses of `scanLoop_ready` at `nr = c = n`, and `C_i ≤ 2^{e_i}(2^n+1)^{e_i}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)

/-! ## Polynomials in `2^n + 1` and capacities -/

theorem poly_le_cap (c d n : ℕ) :
    c * (2 ^ n + 1) ^ d ≤ RepairSource.CloseoutCapacity.capacity (natBitLength c + 2 * d + 1)
      (natBitLength c + 2 * d + 1) n := by
  have he := RepairSource.Closeout.recovery_budget c d n
  have hm : max 1 n ≤ n + 1 := by omega
  have hmul := Nat.mul_le_mul_left (natBitLength c + 2 * d + 1) hm
  exact he.trans (Nat.pow_le_pow_right (by decide) (by nlinarith))

theorem cap_le_poly (e n : ℕ) : RepairSource.CloseoutCapacity.capacity e e n ≤ 2 ^ e * (2 ^ n + 1) ^ e := by
  unfold RepairSource.CloseoutCapacity.capacity
  rw [show e * n + e = n * e + e by ring, pow_add, pow_mul, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem self_le_x (n : ℕ) : n + 1 ≤ 2 ^ n + 1 := by have := Nat.lt_two_pow_self (n := n); omega

theorem pow_le_xpow (P n : ℕ) : P ^ n ≤ (2 ^ n + 1) ^ natBitLength P := by
  have hP : P ≤ 2 ^ natBitLength P := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) P).le
  calc P ^ n ≤ (2 ^ natBitLength P) ^ n := Nat.pow_le_pow_left hP n
    _ = (2 ^ n) ^ natBitLength P := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (2 ^ n + 1) ^ natBitLength P := Nat.pow_le_pow_left (by omega) _

/-! ## The width is linear -/

/-- The width's linear constant. -/
def widthK (k A : ℕ) : ℕ := (A + 1) * (k + 2) + 3 * A + 2

theorem widthAt_lin (k A a : ℕ) : widthAt k A a + 2 ≤ widthK k A * (a + 1) := by
  have hc := clog_two_le_self (a * (k + 2) + 2)
  have := Nat.mul_le_mul_left A hc
  unfold widthAt widthK
  nlinarith

theorem candL0_le (k A a : ℕ) : candL0 k A a ≤ widthK k A * (a + 1) := by
  have := widthAt_lin k A a
  have h := clog_two_le_self (widthAt k A a + 2)
  unfold candL0 Ledger.Lq
  omega

/-! ## The schedule round's time is linear in the value capacity -/

theorem roundCostBound_le (p w t : ℕ) : roundCostBound p w t ≤ (8 * p + 8 * w + 168) * (t + 1) := by
  unfold roundCostBound flagCost updateCost writeBackCost UWalkNumbers.productCost
    RepairSource.CloseoutSchedule.RawCompare.budget
  have hmin : min (t + 1) t ≤ t := min_le_right _ _
  simp only [Bool.toNat_true]
  nlinarith

/-! ## The scan round's time as a polynomial in `2^n + 1` -/

section Terms
variable (k A v D : ℕ)

theorem term_width (n : ℕ) : candWidthBound k A (n + 1) ≤ 256 * (A + 2 * k + 10) ^ 2 * (2 ^ n + 1) ^ 2 := by
  have hnx := self_le_x n
  have h : (n + 1) * (k + 2) + A + k + 8 ≤ (A + 2 * k + 10) * (2 ^ n + 1) := by nlinarith
  have h2 := Nat.pow_le_pow_left h 2
  unfold candWidthBound
  rw [mul_pow] at h2
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h2

theorem width_next (n : ℕ) : widthAt k A (n + 1) + 2 ≤ 2 * widthK k A * (2 ^ n + 1) := by
  have hnx := self_le_x n
  have h1 := widthAt_lin k A (n + 1)
  have h2 := Nat.mul_le_mul_left (widthK k A) (show n + 1 + 1 ≤ 2 * (2 ^ n + 1) by omega)
  nlinarith

theorem term_lq (n : ℕ) : candLqBound (widthAt k A (n + 1)) ≤ 256 * (2 * widthK k A + 8) ^ 2 * (2 ^ n + 1) ^ 2 := by
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hw := width_next k A n
  have h : widthAt k A (n + 1) + 8 ≤ (2 * widthK k A + 8) * (2 ^ n + 1) := by nlinarith
  have h2 := Nat.pow_le_pow_left h 2
  unfold candLqBound
  rw [mul_pow] at h2
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h2

theorem term_setup (n t : ℕ) : candSetupBound v (candL0 k A (n + 1)) t ≤
    2 * t + 32 * (2 * widthK k A + 1) ^ 3 * ((2 * v) ^ 16 + 3) * (2 ^ n + 1) ^ 3 + 64 := by
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hnx := self_le_x n
  have hL := candL0_le k A (n + 1)
  have h2 := Nat.mul_le_mul_left (widthK k A) (show n + 1 + 1 ≤ 2 * (2 ^ n + 1) by omega)
  have h : candL0 k A (n + 1) + 1 ≤ (2 * widthK k A + 1) * (2 ^ n + 1) := by nlinarith
  have h3 := Nat.pow_le_pow_left h 3
  rw [mul_pow] at h3
  have h4 := Nat.mul_le_mul_right ((2 * v) ^ 16 + 3) (Nat.mul_le_mul_left 32 h3)
  unfold candSetupBound
  have e : 32 * ((2 * widthK k A + 1) ^ 3 * (2 ^ n + 1) ^ 3) * ((2 * v) ^ 16 + 3) =
      32 * (2 * widthK k A + 1) ^ 3 * ((2 * v) ^ 16 + 3) * (2 ^ n + 1) ^ 3 := by ring
  omega

theorem term_sched (p w t T n : ℕ) (hT : roundCostBound p w t + 1 ≤ T) :
    candSchedCost p w t T n ≤ 3 * ((2 ^ n + 1) * T) + 8 * (2 ^ n + 1) + 7 := by
  have hnx := self_le_x n
  have h : n * (roundCostBound p w t + 1 + (2 * T + 4 + 1 + 0) + 2) ≤ (2 ^ n + 1) * (3 * T + 7) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold candSchedCost
  nlinarith

theorem term_core (n : ℕ) : candCoreBound D (widthAt k A (n + 1)) (1 + n) n ≤
    (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900) *
      (2 * widthK k A + 3) ^ (2 * D + 2) * (2 ^ n + 1) ^ (2 * D + 2) +
    192 * (2 * widthK k A + (2 * widthK k A) ^ D) * (2 ^ n + 1) ^ (D + 2) + 2 * n + 128 := by
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hnx := self_le_x n
  have hw := width_next k A n
  generalize widthAt k A (n + 1) = q at hw ⊢
  generalize 2 ^ n + 1 = x at hx hnx hw ⊢
  generalize widthK k A = K at hw ⊢
  have hq3 : q + 3 ≤ (2 * K + 3) * x := by nlinarith
  have h6 := Nat.mul_le_mul_left (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900)
    (Nat.pow_le_pow_left hq3 (2 * D + 2))
  rw [mul_pow] at h6
  have hqD : (q + 2) ^ D ≤ (2 * K) ^ D * x ^ D := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) D
  have hxD : x ^ D ≤ x ^ (D + 1) := Nat.pow_le_pow_right hx (by omega)
  have hx1 : x ≤ x ^ (D + 1) := by
    calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ (D + 1) := Nat.pow_le_pow_right hx (by omega)
  have ha : q + 2 ≤ 2 * K * x ^ (D + 1) := by nlinarith
  have hb : (2 * K) ^ D * x ^ D ≤ (2 * K) ^ D * x ^ (D + 1) := Nat.mul_le_mul_left _ hxD
  have hsum : q + 2 + (q + 2) ^ D ≤ (2 * K + (2 * K) ^ D) * x ^ (D + 1) := by nlinarith
  have h7 : 64 * (q + 2 + (q + 2) ^ D) * (1 + n + 2) ≤ 192 * (2 * K + (2 * K) ^ D) * x ^ (D + 2) := by
    calc 64 * (q + 2 + (q + 2) ^ D) * (1 + n + 2)
        ≤ 64 * ((2 * K + (2 * K) ^ D) * x ^ (D + 1)) * (3 * x) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hsum) (by omega)
      _ = 192 * (2 * K + (2 * K) ^ D) * x ^ (D + 2) := by ring
  unfold candCoreBound
  have e : (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900) *
      ((2 * K + 3) ^ (2 * D + 2) * x ^ (2 * D + 2)) =
      (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900) *
      (2 * K + 3) ^ (2 * D + 2) * x ^ (2 * D + 2) := by ring
  omega

end Terms

/-! ## The three capacities -/

/-- The capacity `2^{e n + e}` of base's `CloseoutCapacity`. -/
def pcap (e n : ℕ) : ℕ := RepairSource.CloseoutCapacity.capacity e e n

theorem value_bound (k A u v a i n : ℕ) (huv : 2 * u < v) (ha : a ≤ n) (hi : i ≤ n) :
    candA0 k A u v a * ((v - u) ^ 16) ^ i ≤
      widthK k A ^ 3 * (2 * v) ^ 16 * (2 ^ n + 1) ^ (3 + natBitLength ((v - u) ^ 16 + v ^ 16)) ∧
    candB0 v * (v ^ 16) ^ i ≤
      widthK k A ^ 3 * (2 * v) ^ 16 * (2 ^ n + 1) ^ (3 + natBitLength ((v - u) ^ 16 + v ^ 16)) ∧
    1 + i ≤ widthK k A ^ 3 * (2 * v) ^ 16 * (2 ^ n + 1) ^ (3 + natBitLength ((v - u) ^ 16 + v ^ 16)) := by
  have hnx := self_le_x n
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hL : candL0 k A a ≤ widthK k A * (2 ^ n + 1) :=
    (candL0_le k A a).trans (Nat.mul_le_mul_left _ (by omega))
  have hV : (v - 2 * u) ^ 16 ≤ (2 * v) ^ 16 := Nat.pow_le_pow_left (by omega) 16
  have hp1 : 1 ≤ (v - u) ^ 16 := Nat.one_le_pow _ _ (by omega)
  have hw1 : 1 ≤ v ^ 16 := Nat.one_le_pow _ _ (by omega)
  have hpi : ((v - u) ^ 16) ^ i ≤ (2 ^ n + 1) ^ natBitLength ((v - u) ^ 16 + v ^ 16) :=
    (Nat.pow_le_pow_right hp1 hi).trans ((Nat.pow_le_pow_left (Nat.le_add_right _ _) n).trans (pow_le_xpow _ n))
  have hwi : (v ^ 16) ^ i ≤ (2 ^ n + 1) ^ natBitLength ((v - u) ^ 16 + v ^ 16) :=
    (Nat.pow_le_pow_right hw1 hi).trans ((Nat.pow_le_pow_left (Nat.le_add_left _ _) n).trans (pow_le_xpow _ n))
  have hK : 1 ≤ widthK k A ^ 3 * (2 ^ n + 1) ^ 3 := Nat.one_le_iff_ne_zero.mpr (by unfold widthK; positivity)
  generalize natBitLength ((v - u) ^ 16 + v ^ 16) = β at hpi hwi ⊢
  refine ⟨?_, ?_, ?_⟩
  · calc candA0 k A u v a * ((v - u) ^ 16) ^ i
        = candL0 k A a * candL0 k A a * candL0 k A a * (v - 2 * u) ^ 16 * ((v - u) ^ 16) ^ i := rfl
      _ ≤ (widthK k A * (2 ^ n + 1)) * (widthK k A * (2 ^ n + 1)) * (widthK k A * (2 ^ n + 1)) *
          (2 * v) ^ 16 * (2 ^ n + 1) ^ β :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hL hL) hL) hV) hpi
      _ = _ := by ring
  · calc candB0 v * (v ^ 16) ^ i ≤ (2 * v) ^ 16 * (2 ^ n + 1) ^ β := Nat.mul_le_mul_left _ hwi
      _ = 1 * ((2 * v) ^ 16 * (2 ^ n + 1) ^ β) := by ring
      _ ≤ (widthK k A ^ 3 * (2 ^ n + 1) ^ 3) * ((2 * v) ^ 16 * (2 ^ n + 1) ^ β) := Nat.mul_le_mul_right _ hK
      _ = _ := by ring
  · have h1 : 2 ^ n + 1 ≤ (2 ^ n + 1) ^ (3 + β) := by
      calc 2 ^ n + 1 = (2 ^ n + 1) ^ 1 := (pow_one _).symm
        _ ≤ _ := Nat.pow_le_pow_right hx (by omega)
    have h2 : (2 ^ n + 1) ^ (3 + β) ≤ widthK k A ^ 3 * (2 * v) ^ 16 * (2 ^ n + 1) ^ (3 + β) :=
      Nat.le_mul_of_pos_left _ (Nat.mul_pos (pow_pos (by unfold widthK; omega) _) (pow_pos (by omega) _))
    omega

/-- **The value capacity.** -/
theorem caps_one (k A u v : ℕ) (huv : 2 * u < v) : ∃ e1 : ℕ, ∀ n : ℕ, n ≤ pcap e1 n ∧
    ∀ a, a ≤ n → ∀ i, i ≤ n → candA0 k A u v a * ((v - u) ^ 16) ^ i ≤ pcap e1 n ∧
      candB0 v * (v ^ 16) ^ i ≤ pcap e1 n ∧ 1 + i ≤ pcap e1 n := by
  refine ⟨natBitLength (widthK k A ^ 3 * (2 * v) ^ 16) + 2 * (3 + natBitLength ((v - u) ^ 16 + v ^ 16)) + 1,
    fun n => ?_⟩
  have hC := poly_le_cap (widthK k A ^ 3 * (2 * v) ^ 16) (3 + natBitLength ((v - u) ^ 16 + v ^ 16)) n
  refine ⟨?_, fun a ha i hi => ?_⟩
  · have := (value_bound k A u v 0 n n huv (Nat.zero_le _) le_rfl).2.2
    unfold pcap; omega
  · obtain ⟨h1, h2, h3⟩ := value_bound k A u v a i n huv ha hi
    exact ⟨h1.trans hC, h2.trans hC, h3.trans hC⟩

/-- **The round capacity.** -/
theorem caps_two (p w e1 : ℕ) : ∃ e2 : ℕ, ∀ n : ℕ,
    max (pcap e1 n + 1) (max (p + 1) (w + 1)) ≤ pcap e2 n ∧ roundCostBound p w (pcap e1 n) + 1 ≤ pcap e2 n := by
  obtain ⟨S, hS⟩ : ∃ S, S = 8 * p + 8 * w + 168 + p + w + 2 := ⟨_, rfl⟩
  refine ⟨natBitLength (S * (2 * 2 ^ e1)) + 2 * e1 + 1, fun n => ?_⟩
  have hC2 : S * (2 * 2 ^ e1) * (2 ^ n + 1) ^ e1 ≤ pcap (natBitLength (S * (2 * 2 ^ e1)) + 2 * e1 + 1) n :=
    poly_le_cap (S * (2 * 2 ^ e1)) e1 n
  have hC1hi : pcap e1 n ≤ 2 ^ e1 * (2 ^ n + 1) ^ e1 := cap_le_poly e1 n
  have hrc := roundCostBound_le p w (pcap e1 n)
  have hM : 1 ≤ 2 ^ e1 * (2 ^ n + 1) ^ e1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : S * (2 * 2 ^ e1) * (2 ^ n + 1) ^ e1 = S * (2 * (2 ^ e1 * (2 ^ n + 1) ^ e1)) := by ring
  rw [e] at hC2
  generalize pcap (natBitLength (S * (2 * 2 ^ e1)) + 2 * e1 + 1) n = C2 at hC2 ⊢
  generalize pcap e1 n = C1 at hC1hi hrc ⊢
  generalize 2 ^ e1 * (2 ^ n + 1) ^ e1 = M at hC1hi hM hC2
  have h1 : S * (C1 + 1) ≤ S * (2 * M) := Nat.mul_le_mul_left _ (by omega)
  have hS1 : S * (C1 + 1) = (8 * p + 8 * w + 168) * (C1 + 1) + (p + w + 2) * (C1 + 1) := by rw [hS]; ring
  have h2 : p + w + 2 ≤ (p + w + 2) * (C1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : C1 + 1 ≤ (p + w + 2) * (C1 + 1) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨max_le ?_ (max_le ?_ ?_), ?_⟩ <;> omega

/-- **The scan capacity.** -/
theorem caps_three (k A v D p w e1 e2 : ℕ) (hround : ∀ n, roundCostBound p w (pcap e1 n) + 1 ≤ pcap e2 n) :
    ∃ e3 : ℕ, ∀ n : ℕ, pcap e2 n + 1 + n + n + 1 ≤ pcap e3 n ∧
      scanRoundBound k A v D n n p w (pcap e1 n) (pcap e2 n) n + 1 ≤ pcap e3 n := by
  obtain ⟨K1, hK1⟩ : ∃ K, K = 256 * (A + 2 * k + 10) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ K, K = 256 * (2 * widthK k A + 8) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ K, K = 32 * (2 * widthK k A + 1) ^ 3 * ((2 * v) ^ 16 + 3) := ⟨_, rfl⟩
  obtain ⟨K6, hK6⟩ : ∃ K, K = (RepairSource.ProjectionNormalization.DimensionPolynomial.coefficient D 1 + 900) *
    (2 * widthK k A + 3) ^ (2 * D + 2) := ⟨_, rfl⟩
  obtain ⟨K7, hK7⟩ : ∃ K, K = 192 * (2 * widthK k A + (2 * widthK k A) ^ D) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P, P = 2 ^ e1 := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P, P = 2 ^ e2 := ⟨_, rfl⟩
  obtain ⟨d3, hd3⟩ : ∃ d, d = e1 + e2 + 2 * D + 8 := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c, c = K1 + K2 + K3 + 4 * P1 + 4 * P2 + K6 + K7 + 300 := ⟨_, rfl⟩
  refine ⟨natBitLength c3 + 2 * d3 + 1, fun n => ?_⟩
  have hC3 : c3 * (2 ^ n + 1) ^ d3 ≤ pcap (natBitLength c3 + 2 * d3 + 1) n := poly_le_cap c3 d3 n
  have hC1 : pcap e1 n ≤ P1 * (2 ^ n + 1) ^ e1 := by rw [hP1]; exact cap_le_poly e1 n
  have hC2 : pcap e2 n ≤ P2 * (2 ^ n + 1) ^ e2 := by rw [hP2]; exact cap_le_poly e2 n
  have hr := hround n
  have t1 := term_width k A n
  have t2 := term_lq k A n
  have t3 := term_setup k A v n (pcap e1 n)
  have t4 := term_sched p w (pcap e1 n) (pcap e2 n) n hr
  have t5 := term_core k A D n
  rw [← hK1] at t1
  rw [← hK2] at t2
  rw [← hK3] at t3
  rw [← hK6, ← hK7] at t5
  have hx : 1 ≤ 2 ^ n + 1 := Nat.le_add_left 1 _
  have hnx := self_le_x n
  have hp : ∀ a, a ≤ d3 → (2 ^ n + 1) ^ a ≤ (2 ^ n + 1) ^ d3 := fun a h => Nat.pow_le_pow_right hx h
  have ux : 2 ^ n + 1 ≤ (2 ^ n + 1) ^ d3 := by
    calc 2 ^ n + 1 = (2 ^ n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := hp 1 (by omega)
  have uC2' : (2 ^ n + 1) * pcap e2 n ≤ P2 * (2 ^ n + 1) ^ d3 := by
    calc (2 ^ n + 1) * pcap e2 n ≤ (2 ^ n + 1) * (P2 * (2 ^ n + 1) ^ e2) := Nat.mul_le_mul_left _ hC2
      _ = P2 * (2 ^ n + 1) ^ (e2 + 1) := by ring
      _ ≤ P2 * (2 ^ n + 1) ^ d3 := Nat.mul_le_mul_left _ (hp _ (by omega))
  have u1 := Nat.mul_le_mul_left K1 (hp 2 (by omega))
  have u2 := Nat.mul_le_mul_left K2 (hp 2 (by omega))
  have u3 := Nat.mul_le_mul_left K3 (hp 3 (by omega))
  have u6 := Nat.mul_le_mul_left K6 (hp (2 * D + 2) (by omega))
  have u7 := Nat.mul_le_mul_left K7 (hp (D + 2) (by omega))
  have uC1 := hC1.trans (Nat.mul_le_mul_left P1 (hp e1 (by omega)))
  have uC2 := hC2.trans (Nat.mul_le_mul_left P2 (hp e2 (by omega)))
  have hc3Z : c3 * (2 ^ n + 1) ^ d3 = K1 * (2 ^ n + 1) ^ d3 + K2 * (2 ^ n + 1) ^ d3 + K3 * (2 ^ n + 1) ^ d3 +
      4 * (P1 * (2 ^ n + 1) ^ d3) + 4 * (P2 * (2 ^ n + 1) ^ d3) + K6 * (2 ^ n + 1) ^ d3 + K7 * (2 ^ n + 1) ^ d3 +
      300 * (2 ^ n + 1) ^ d3 := by rw [hc3]; ring
  have hZ1 : 1 ≤ (2 ^ n + 1) ^ d3 := hx.trans ux
  generalize (2 ^ n + 1) ^ d3 = Z at *
  refine ⟨?_, ?_⟩
  · omega
  · unfold scanRoundBound candBound
    omega

/-- **The prefix's capacities**: fixed `e₁, e₂, e₃` make `C_i = pcap e_i n` satisfy, for every `n`, the hypotheses of
`scanLoop_ready` at `nr = c = n` with the words `p = (v−u)^{16}`, `w = v^{16}`. -/
theorem prefix_caps (k A u v D : ℕ) (huv : 2 * u < v) : ∃ e1 e2 e3 : ℕ, ∀ n : ℕ,
    n ≤ pcap e1 n ∧
    (∀ a, a ≤ n → ∀ i, i ≤ n → candA0 k A u v a * ((v - u) ^ 16) ^ i ≤ pcap e1 n ∧
      candB0 v * (v ^ 16) ^ i ≤ pcap e1 n ∧ 1 + i ≤ pcap e1 n) ∧
    max (pcap e1 n + 1) (max ((v - u) ^ 16 + 1) (v ^ 16 + 1)) ≤ pcap e2 n ∧
    roundCostBound ((v - u) ^ 16) (v ^ 16) (pcap e1 n) + 1 ≤ pcap e2 n ∧
    pcap e2 n + 1 + n + n + 1 ≤ pcap e3 n ∧
    scanRoundBound k A v D n n ((v - u) ^ 16) (v ^ 16) (pcap e1 n) (pcap e2 n) n + 1 ≤ pcap e3 n := by
  obtain ⟨e1, h1⟩ := caps_one k A u v huv
  obtain ⟨e2, h2⟩ := caps_two ((v - u) ^ 16) (v ^ 16) e1
  obtain ⟨e3, h3⟩ := caps_three k A v D ((v - u) ^ 16) (v ^ 16) e1 e2 (fun n => (h2 n).2)
  exact ⟨e1, e2, e3, fun n => ⟨(h1 n).1, (h1 n).2, (h2 n).1, (h2 n).2, (h3 n).1, (h3 n).2⟩⟩

end NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
