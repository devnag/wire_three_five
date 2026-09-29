import Proof.Wire_3_5.Selection.GateDefs

/-! # C1.4 math: the machine's enumeration of each side is exhaustive and repetition-free (P3:1339-1345)

Paper: "Enumerate its `2^k` error rows [...] Enumerate each half's score vectors" (P3:1339-1345). The machine walks a
counter over each half's bits and a counter over each side's error codes (`GateDefs`). This module proves that the
machine's lists `enumL P`, `enumR P` visit every `(errors, half)` pair exactly once (**`enumL_enumerates`**,
**`enumR_enumerates`**), the hypothesis `Enumerates` of C1.1's `gateRows_eq_gateJoin`. The steps: the machine
positions and the coordinates of a half are inverse bijections (`coordL`/`posL`, `coordR`/`posR`), so `decX`, `decY`
are bijections from counter values below `2^{lw}`, `2^{rw}`; the code segments make `decU` a bijection from values
below `2^{s·h}` (codes `< 2^s = b + 1`). Paper quantity: the enumeration of each half's score vectors. -/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

variable (P : StarParams)

theorem divmod (a m b : ℕ) (hm : m < b) : (a * b + m) / b = a ∧ (a * b + m) % b = m := by
  have hb : 0 < b := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hm, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]

/-- A position inside block `x < y` lies below `y` blocks. -/
theorem blk_lt (x y m b : ℕ) (hx : x < y) (hm : m < b) : x * b + m < y * b :=
  calc x * b + m < x * b + b := Nat.add_lt_add_left hm _
    _ = (x + 1) * b := by ring
    _ ≤ y * b := Nat.mul_le_mul_right _ hx

theorem hh_two : 2 * hh P = P.r := by unfold hh; have := P.r_half_add; omega

theorem rb_le : P.r * P.b ≤ P.n := P.r_mul_b_le

theorem hb_le_rb : hh P * P.b ≤ P.r * P.b := Nat.mul_le_mul_right _ (by unfold hh; omega)

theorem hb2 : hh P * P.b + hh P * P.b = P.r * P.b := by rw [← Nat.add_mul, ← Nat.two_mul, hh_two]

theorem fL_le : fL P ≤ P.n - P.r * P.b := by unfold fL; omega

theorem fL_fR : fL P + fR P = P.n - P.r * P.b := by unfold fL fR; omega

/-- Split a position into its block and index. -/
theorem split_pos (p b : ℕ) (hb : 0 < b) : ∃ q m, p = q * b + m ∧ m < b ∧ p / b = q ∧ p % b = m :=
  ⟨p / b, p % b, (Nat.div_add_mod' p b).symm, Nat.mod_lt p hb, rfl, rfl⟩

/-! ## Left positions and coordinates -/

theorem coordL_lt (p : ℕ) (hp : p < lw P) : coordL P p < P.n := by
  have hb := P.b_pos
  have h1 := rb_le P
  have h2 := hb_le_rb P
  have h3 := fL_le P
  unfold lw at hp
  unfold coordL
  split_ifs with h
  · obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
    rw [hq, hmm]
    have hqh : q < hh P := by
      by_contra hc
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have := blk_lt (hh P - 1 - q) (hh P) m P.b (by omega) hm
    omega
  · omega

theorem coordL_side (p : ℕ) (hp : p < lw P) :
    P.centerSide ⟨coordL P p, coordL_lt P p hp⟩ = true := by
  have hb := P.b_pos
  have h2 := hb_le_rb P
  have h3 := fL_le P
  unfold StarParams.centerSide
  simp only [decide_eq_true_eq]
  unfold lw at hp
  unfold coordL
  split_ifs with h
  · left
    obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
    rw [hq, hmm]
    have hqh : q < hh P := by
      by_contra hc
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    exact blk_lt (hh P - 1 - q) (hh P) m P.b (by omega) hm
  · right
    unfold fL at hp
    constructor <;> omega

theorem posL_coordL (p : ℕ) (hp : p < lw P) : posL P (coordL P p) = p := by
  have hb := P.b_pos
  have h2 := hb_le_rb P
  unfold lw at hp
  by_cases h : p < hh P * P.b
  · obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
    have hqh : q < hh P := by
      by_contra hc
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlt := blk_lt (hh P - 1 - q) (hh P) m P.b (by omega) hm
    obtain ⟨d1, d2⟩ := divmod (hh P - 1 - q) m P.b hm
    unfold coordL posL
    rw [if_pos h, hq, hmm, if_pos hlt, d1, d2]
    have e : hh P - 1 - (hh P - 1 - q) = q := by omega
    rw [e]
  · unfold coordL posL
    rw [if_neg h, if_neg (by omega)]
    omega

theorem posL_lt (c : Fin P.n) (hc : P.centerSide c = true) : posL P c.val < lw P := by
  have hb := P.b_pos
  unfold StarParams.centerSide at hc
  simp only [decide_eq_true_eq] at hc
  unfold posL lw
  split_ifs with h
  · obtain ⟨q, m, hcq, hm, hq, hmm⟩ := split_pos c.val P.b hb
    rw [hq, hmm]
    have hqh : q < hh P := by
      by_contra hc'
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have := blk_lt (hh P - 1 - q) (hh P) m P.b (by omega) hm
    omega
  · rcases hc with hc | hc
    · exact absurd hc h
    · unfold fL; omega

theorem coordL_posL (c : Fin P.n) (hc : P.centerSide c = true) : coordL P (posL P c.val) = c.val := by
  have hb := P.b_pos
  have h2 := hb_le_rb P
  unfold StarParams.centerSide at hc
  simp only [decide_eq_true_eq] at hc
  by_cases h : c.val < hh P * P.b
  · obtain ⟨q, m, hcq, hm, hq, hmm⟩ := split_pos c.val P.b hb
    have hqh : q < hh P := by
      by_contra hc'
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlt := blk_lt (hh P - 1 - q) (hh P) m P.b (by omega) hm
    obtain ⟨d1, d2⟩ := divmod (hh P - 1 - q) m P.b hm
    unfold coordL posL
    rw [if_pos h, hq, hmm, if_pos hlt, d1, d2]
    have e : hh P - 1 - (hh P - 1 - q) = q := by omega
    rw [e, hcq]
  · rcases hc with hc | hc
    · exact absurd hc h
    · unfold coordL posL
      rw [if_neg h, if_neg (by omega)]
      omega

/-! ## Right positions and coordinates -/

/-- A right block position lies below `rb`. -/
theorem blkR_lt (q m : ℕ) (hq : q < hh P) (hm : m < P.b) : (hh P + (hh P - 1 - q)) * P.b + m < P.r * P.b := by
  have h5 := hh_two P
  exact blk_lt (hh P + (hh P - 1 - q)) P.r m P.b (by omega) hm

theorem coordR_lt (p : ℕ) (hp : p < rw P) : coordR P p < P.n := by
  have hb := P.b_pos
  have h1 := rb_le P
  have h4 := fL_fR P
  have h5 := hb2 P
  unfold rw at hp
  unfold coordR
  split_ifs with h
  · obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
    rw [hq, hmm]
    have hqh : q < hh P := by
      by_contra hc
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have := blkR_lt P q m hqh hm
    omega
  · omega

theorem coordR_side (p : ℕ) (hp : p < rw P) :
    ¬ P.centerSide ⟨coordR P p, coordR_lt P p hp⟩ = true := by
  have hb := P.b_pos
  have h1 := rb_le P
  have h4 := fL_fR P
  have h5 := hb2 P
  unfold StarParams.centerSide
  simp only [decide_eq_true_eq, not_or, not_and, not_lt]
  unfold rw at hp
  unfold coordR
  split_ifs with h
  · obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
    rw [hq, hmm]
    have hqh : q < hh P := by
      by_contra hc
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hhi := blkR_lt P q m hqh hm
    have hlo : hh P * P.b ≤ (hh P + (hh P - 1 - q)) * P.b := Nat.mul_le_mul_right _ (by omega)
    refine ⟨?_, fun h' => absurd h' (by omega)⟩
    show hh P * P.b ≤ _
    omega
  · refine ⟨?_, fun _ => ?_⟩
    · show hh P * P.b ≤ _; omega
    · unfold fL; omega

theorem posR_coordR (p : ℕ) (hp : p < rw P) : posR P (coordR P p) = p := by
  have hb := P.b_pos
  have h5 := hb2 P
  have h6 := hh_two P
  unfold rw at hp
  by_cases h : p < hh P * P.b
  · obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
    have hqh : q < hh P := by
      by_contra hc
      have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlt := blkR_lt P q m hqh hm
    obtain ⟨d1, d2⟩ := divmod (hh P + (hh P - 1 - q)) m P.b hm
    unfold coordR posR
    rw [if_pos h, hq, hmm, if_pos hlt, d1, d2]
    have e : hh P - 1 - (hh P + (hh P - 1 - q) - hh P) = q := by omega
    rw [e]
  · unfold coordR posR
    rw [if_neg h, if_neg (by omega)]
    omega

theorem posR_lt (c : Fin P.n) (hc : ¬ P.centerSide c = true) : posR P c.val < rw P := by
  have hb := P.b_pos
  have h4 := fL_fR P
  have h5 := hb2 P
  have h6 := hh_two P
  unfold StarParams.centerSide at hc
  simp only [decide_eq_true_eq, not_or, not_and, not_lt] at hc
  obtain ⟨hc1, hc2⟩ := hc
  change hh P * P.b ≤ c.val at hc1
  unfold posR rw
  split_ifs with h
  · obtain ⟨q, m, hcq, hm, hq, hmm⟩ := split_pos c.val P.b hb
    rw [hq, hmm]
    have hq1 : hh P ≤ q := by
      by_contra hc'
      have := blk_lt q (hh P) m P.b (by omega) hm
      omega
    have hq2 : q < P.r := by
      by_contra hc'
      have : P.r * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have := blk_lt (hh P - 1 - (q - hh P)) (hh P) m P.b (by omega) hm
    omega
  · have := hc2 (by omega)
    have hn := c.isLt
    unfold fR
    unfold fL at h4 this ⊢
    omega

theorem coordR_posR (c : Fin P.n) (hc : ¬ P.centerSide c = true) : coordR P (posR P c.val) = c.val := by
  have hb := P.b_pos
  have h5 := hb2 P
  have h6 := hh_two P
  unfold StarParams.centerSide at hc
  simp only [decide_eq_true_eq, not_or, not_and, not_lt] at hc
  obtain ⟨hc1, hc2⟩ := hc
  change hh P * P.b ≤ c.val at hc1
  by_cases h : c.val < P.r * P.b
  · obtain ⟨q, m, hcq, hm, hq, hmm⟩ := split_pos c.val P.b hb
    have hq1 : hh P ≤ q := by
      by_contra hc'
      have := blk_lt q (hh P) m P.b (by omega) hm
      omega
    have hq2 : q < P.r := by
      by_contra hc'
      have : P.r * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlt := blk_lt (hh P - 1 - (q - hh P)) (hh P) m P.b (by omega) hm
    obtain ⟨d1, d2⟩ := divmod (hh P - 1 - (q - hh P)) m P.b hm
    unfold coordR posR
    rw [if_pos h, hq, hmm, if_pos hlt, d1, d2]
    have e : hh P + (hh P - 1 - (hh P - 1 - (q - hh P))) = q := by omega
    rw [e, hcq]
  · have := hc2 (by omega)
    unfold coordR posR
    rw [if_neg h, if_neg (by omega)]
    unfold fL
    omega

/-! ## Base-`B` digits -/

/-- Digit `t` of `u` in base `B`. -/
def digit (B t u : ℕ) : ℕ := u / B ^ t % B

/-- The number with base-`B` digits `d 0, …, d (h−1)`. -/
def encDigits (B : ℕ) (d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | h + 1 => d 0 + B * encDigits B (fun t => d (t + 1)) h

theorem enc_lt (B : ℕ) (hB : 2 ≤ B) : ∀ (h : ℕ) (d : ℕ → ℕ), (∀ t < h, d t < B) → encDigits B d h < B ^ h
  | 0, _, _ => by simp [encDigits]
  | h + 1, d, hd => by
    have ih := enc_lt B hB h (fun t => d (t + 1)) (fun t ht => hd (t + 1) (by omega))
    have h0 := hd 0 (by omega)
    simp only [encDigits, Nat.pow_succ]
    have : B * encDigits B (fun t => d (t + 1)) h + B ≤ B * B ^ h := by
      calc B * encDigits B (fun t => d (t + 1)) h + B = B * (encDigits B (fun t => d (t + 1)) h + 1) := by ring
        _ ≤ B * B ^ h := Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (B ^ h) B]
    omega

theorem digit_enc (B : ℕ) (hB : 2 ≤ B) : ∀ (h : ℕ) (d : ℕ → ℕ), (∀ t < h, d t < B) → ∀ t < h,
    digit B t (encDigits B d h) = d t
  | 0, _, _, t, ht => absurd ht (by omega)
  | h + 1, d, hd, t, ht => by
    have h0 := hd 0 (by omega)
    have hBp : 0 < B := by omega
    unfold digit
    simp only [encDigits]
    cases t with
    | zero =>
      simp only [pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
    | succ t =>
      have ih := digit_enc B hB h (fun t => d (t + 1)) (fun t' ht' => hd (t' + 1) (by omega)) t (by omega)
      unfold digit at ih
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hBp, Nat.div_eq_of_lt h0,
        Nat.zero_add]
      exact ih

theorem digit_ext (B : ℕ) (hB : 2 ≤ B) : ∀ (h u u' : ℕ), u < B ^ h → u' < B ^ h →
    (∀ t < h, digit B t u = digit B t u') → u = u'
  | 0, u, u', hu, hu', _ => by simp at hu hu'; omega
  | h + 1, u, u', hu, hu', hd => by
    have hBp : 0 < B := by omega
    have h0 := hd 0 (by omega)
    simp only [digit, pow_zero, Nat.div_one] at h0
    have hq : u / B = u' / B := by
      apply digit_ext B hB h
      · rw [Nat.div_lt_iff_lt_mul hBp, ← Nat.pow_succ]; exact hu
      · rw [Nat.div_lt_iff_lt_mul hBp, ← Nat.pow_succ]; exact hu'
      · intro t ht
        have := hd (t + 1) (by omega)
        unfold digit at this ⊢
        rwa [Nat.pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    rw [← Nat.div_add_mod u B, ← Nat.div_add_mod u' B, hq, h0]

/-! ## The halves as counter values -/

theorem testBit_digit (x p : ℕ) : x.testBit p = decide (digit 2 p x = 1) := by
  unfold digit; rw [Nat.testBit_eq_decide_div_mod_eq]

theorem decX_inj (x x' : ℕ) (hx : x < 2 ^ lw P) (hx' : x' < 2 ^ lw P) (h : decX P x = decX P x') : x = x' := by
  apply digit_ext 2 le_rfl (lw P) x x' hx hx'
  intro p hp
  have hb := congrFun h ⟨⟨coordL P p, coordL_lt P p hp⟩, coordL_side P p hp⟩
  simp only [decX, posL_coordL P p hp, testBit_digit] at hb
  have h1 : digit 2 p x < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : digit 2 p x' < 2 := Nat.mod_lt _ (by norm_num)
  by_cases e : digit 2 p x = 1 <;> by_cases e' : digit 2 p x' = 1 <;> simp_all <;> omega

/-- The counter value of a left half. -/
def encX (f : P.SideL → Bool) : ℕ :=
  encDigits 2 (fun p => if hp : p < lw P then
    (if f ⟨⟨coordL P p, coordL_lt P p hp⟩, coordL_side P p hp⟩ then 1 else 0) else 0) (lw P)

theorem encX_spec (f : P.SideL → Bool) : encX P f < 2 ^ lw P ∧ decX P (encX P f) = f := by
  have hd : ∀ t < lw P, (fun p => if hp : p < lw P then
      (if f ⟨⟨coordL P p, coordL_lt P p hp⟩, coordL_side P p hp⟩ then 1 else 0) else 0) t < 2 := by
    intro t _; dsimp only; split_ifs <;> omega
  refine ⟨enc_lt 2 le_rfl _ _ hd, ?_⟩
  funext i
  have hp := posL_lt P i.1 i.2
  have hdig := digit_enc 2 le_rfl (lw P) _ hd (posL P i.1.val) hp
  unfold decX encX
  rw [testBit_digit, hdig]
  simp only [dif_pos hp]
  have hi : (⟨⟨coordL P (posL P i.1.val), coordL_lt P _ hp⟩, coordL_side P _ hp⟩ : P.SideL) = i := by
    apply Subtype.ext; apply Fin.ext; exact coordL_posL P i.1 i.2
  rw [hi]
  split_ifs <;> simp_all

theorem decY_inj (y y' : ℕ) (hy : y < 2 ^ rw P) (hy' : y' < 2 ^ rw P) (h : decY P y = decY P y') : y = y' := by
  apply digit_ext 2 le_rfl (rw P) y y' hy hy'
  intro p hp
  have hb := congrFun h ⟨⟨coordR P p, coordR_lt P p hp⟩, coordR_side P p hp⟩
  simp only [decY, posR_coordR P p hp, testBit_digit] at hb
  have h1 : digit 2 p y < 2 := Nat.mod_lt _ (by norm_num)
  have h2 : digit 2 p y' < 2 := Nat.mod_lt _ (by norm_num)
  by_cases e : digit 2 p y = 1 <;> by_cases e' : digit 2 p y' = 1 <;> simp_all <;> omega

/-- The counter value of a right half. -/
def encY (f : P.SideR → Bool) : ℕ :=
  encDigits 2 (fun p => if hp : p < rw P then
    (if f ⟨⟨coordR P p, coordR_lt P p hp⟩, coordR_side P p hp⟩ then 1 else 0) else 0) (rw P)

theorem encY_spec (f : P.SideR → Bool) : encY P f < 2 ^ rw P ∧ decY P (encY P f) = f := by
  have hd : ∀ t < rw P, (fun p => if hp : p < rw P then
      (if f ⟨⟨coordR P p, coordR_lt P p hp⟩, coordR_side P p hp⟩ then 1 else 0) else 0) t < 2 := by
    intro t _; dsimp only; split_ifs <;> omega
  refine ⟨enc_lt 2 le_rfl _ _ hd, ?_⟩
  funext i
  have hp := posR_lt P i.1 i.2
  have hdig := digit_enc 2 le_rfl (rw P) _ hd (posR P i.1.val) hp
  unfold decY encY
  rw [testBit_digit, hdig]
  simp only [dif_pos hp]
  have hi : (⟨⟨coordR P (posR P i.1.val), coordR_lt P _ hp⟩, coordR_side P _ hp⟩ : P.SideR) = i := by
    apply Subtype.ext; apply Fin.ext; exact coordR_posR P i.1 i.2
  rw [hi]
  split_ifs <;> simp_all

/-! ## The errors as counter values -/

theorem errCode_digit (u j : ℕ) : errCode P u j = digit (2 ^ P.s) (hh P - 1 - j) u := by
  unfold errCode digit; rw [← Nat.pow_mul]

theorem two_le_pow_s : 2 ≤ 2 ^ P.s := by
  have := P.one_le_s
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ P.s := Nat.pow_le_pow_right (by norm_num) this

theorem decU_inj (u u' : ℕ) (hu : u < 2 ^ (P.s * hh P)) (hu' : u' < 2 ^ (P.s * hh P)) (h : decU P u = decU P u') :
    u = u' := by
  rw [Nat.pow_mul] at hu hu'
  apply digit_ext (2 ^ P.s) (two_le_pow_s P) (hh P) u u' hu hu'
  intro t ht
  have hj : hh P - 1 - t < P.r / 2 := by show hh P - 1 - t < hh P; omega
  have hc := congrFun h ⟨hh P - 1 - t, hj⟩
  have e : hh P - 1 - (hh P - 1 - t) = t := by omega
  rw [← e, ← errCode_digit, ← errCode_digit]
  unfold decU at hc
  by_cases ha : errCode P u (hh P - 1 - t) = 0 <;> by_cases hb : errCode P u' (hh P - 1 - t) = 0
  · rw [ha, hb]
  · rw [dif_pos ha, dif_neg hb] at hc; exact absurd hc (by simp)
  · rw [dif_neg ha, dif_pos hb] at hc; exact absurd hc (by simp)
  · rw [dif_neg ha, dif_neg hb] at hc
    have hv := congrArg (fun o => o.map Fin.val) hc
    simp only [Option.map_some, Option.some.injEq] at hv
    omega

/-- The code of an error choice: `0` for none, `i + 1` for `e_i`. -/
def cd (P : StarParams) (o : Option (Fin P.b)) : ℕ := match o with
  | none => 0
  | some i => i.val + 1

/-- The counter value of a side's errors. -/
def encU (e : P.Errors) : ℕ :=
  encDigits (2 ^ P.s) (fun t => if ht : hh P - 1 - t < P.r / 2 then cd P (e ⟨hh P - 1 - t, ht⟩) else 0) (hh P)

theorem cd_lt (o : Option (Fin P.b)) : cd P o < 2 ^ P.s := by
  have := P.b_succ
  cases o with
  | none => simp [cd]
  | some i => simp only [cd]; have := i.isLt; omega

theorem encU_spec (e : P.Errors) : encU P e < 2 ^ (P.s * hh P) ∧ decU P (encU P e) = e := by
  have hd : ∀ t < hh P, (fun t => if ht : hh P - 1 - t < P.r / 2 then cd P (e ⟨hh P - 1 - t, ht⟩) else 0) t <
      2 ^ P.s := by
    intro t _; dsimp only; split_ifs
    · exact cd_lt P _
    · exact Nat.two_pow_pos _
  refine ⟨by rw [Nat.pow_mul]; exact enc_lt _ (two_le_pow_s P) _ _ hd, ?_⟩
  funext j
  have hjh : j.val < hh P := j.isLt
  have hdig := digit_enc (2 ^ P.s) (two_le_pow_s P) (hh P) _ hd (hh P - 1 - j.val) (by omega)
  have e1 : hh P - 1 - (hh P - 1 - j.val) = j.val := by omega
  have hc : errCode P (encU P e) j.val = cd P (e j) := by
    rw [errCode_digit]
    unfold encU
    rw [hdig]
    simp only [e1]
    rw [dif_pos j.isLt]
  unfold decU
  cases hej : e j with
  | none =>
    rw [hej] at hc
    simp only [cd] at hc
    rw [dif_pos hc]
  | some i =>
    rw [hej] at hc
    simp only [cd] at hc
    rw [dif_neg (by omega)]
    congr 1
    apply Fin.ext
    simp only
    omega

/-! ## The machine's enumerations -/

theorem nodup_enum {α β : Type} (M1 M2 : ℕ) (f : ℕ → α) (g : ℕ → β)
    (hf : ∀ u u', u < M1 → u' < M1 → f u = f u' → u = u') (hg : ∀ x x', x < M2 → x' < M2 → g x = g x' → x = x') :
    ((List.range M1).flatMap fun u => (List.range M2).map fun x => (f u, g x)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · apply List.Nodup.map_on _ (List.nodup_range)
    intro x hx x' hx' he
    exact hg x x' (List.mem_range.mp hx) (List.mem_range.mp hx') (Prod.mk.inj he).2
  · apply List.Pairwise.imp_of_mem _ (List.nodup_range)
    intro u u' hu hu' hne
    rw [Function.onFun, List.disjoint_left]
    intro q hq hq'
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨x', _, he⟩ := List.mem_map.mp hq'
    exact hne (hf u u' (List.mem_range.mp hu) (List.mem_range.mp hu') (Prod.mk.inj he).1.symm)

/-- **The machine's left points visit every `(errors, half)` pair exactly once.** -/
theorem enumL_enumerates : Enumerates (enumL P) (fun _ => True) := by
  refine ⟨nodup_enum _ _ _ _ (decU_inj P) (decX_inj P), fun q => ⟨fun _ => trivial, fun _ => ?_⟩⟩
  obtain ⟨e, f⟩ := q
  unfold enumL
  rw [List.mem_flatMap]
  refine ⟨encU P e, List.mem_range.mpr (encU_spec P e).1, List.mem_map.mpr ⟨encX P f,
    List.mem_range.mpr (encX_spec P f).1, ?_⟩⟩
  rw [(encU_spec P e).2, (encX_spec P f).2]

/-- **The machine's right points visit every `(errors, half)` pair exactly once.** -/
theorem enumR_enumerates : Enumerates (enumR P) (fun _ => True) := by
  refine ⟨nodup_enum _ _ _ _ (decU_inj P) (decY_inj P), fun q => ⟨fun _ => trivial, fun _ => ?_⟩⟩
  obtain ⟨e, f⟩ := q
  unfold enumR
  rw [List.mem_flatMap]
  refine ⟨encU P e, List.mem_range.mpr (encU_spec P e).1, List.mem_map.mpr ⟨encY P f,
    List.mem_range.mpr (encY_spec P f).1, ?_⟩⟩
  rw [(encU_spec P e).2, (encY_spec P f).2]

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
