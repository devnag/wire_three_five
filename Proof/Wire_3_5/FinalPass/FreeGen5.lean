import Proof.Wire_3_5.FinalPass.FreeGen4

/-! # The free numbers' program, part 4: C4.K's `FreeProg` and its bounds (`freeOk κ : FreeOk`)

**`freeProg κ`**: C4.K's `FreeProg` at the program `freeW κ` (values `freeVal κ`, `200` units, at every capacity above
`need κ x`). **`freeOk κ`**: the record `FreeOk` (the mode-independent part of C4.K's contract): the capacity above
`need` from `2^{Do(B+1)²}` (`need_le`, with the read fields small), the cost `≤ 160000·(cap+1)²`, the values `≤ need`
(`val_le_need`), the pad's exponent polynomial in `n`, the pad `2^ρ ≤ 2^{n−2kh}·4^{dA}(n+1)^{dA} + 2^{dR(B+1)²}`
(`padX`), the compiler request's numbers `≤ K3·(nc + a + M + 1)·(β + 1)⁶` (`c3X`).

Paper quantity of the main type: the free numbers of a call with their sizes (C4.K's numbers, P3:3011-3016,
3034-3036). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.C4Set

/-! ## The bit length -/

theorem n_lt_B (n : ℕ) : n < 2 ^ natBitLength n := by
  unfold natBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) n

theorem beta_le_B (x : FreeIn) : β x ≤ natBitLength x.n + 1 := by
  unfold β
  apply Nat.clog_le_of_le_pow
  have h := n_lt_B x.n
  have h1 : 1 ≤ 2 ^ natBitLength x.n := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem le_two_pow_self (k : ℕ) : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le

theorem sq_le_two_pow (k : ℕ) : k * k ≤ 2 ^ (2 * k) := by
  have h := le_two_pow_self k
  calc k * k ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul h h
    _ = 2 ^ (2 * k) := by rw [← pow_add]; ring_nf

theorem W_le (x : FreeIn) : W x ≤ β x + 4 := by unfold W; omega

/-! ## The capacity -/

/-- The capacity's exponent. -/
def needD (κ : FreeK) (Ds : ℕ) : ℕ := Ds + κ.dC + 8

/-- The capacity's coefficient. -/
def needK (κ : FreeK) : ℕ :=
  300 + 3 * (κ.dT + κ.dQ + κ.dH + κ.dP + κ.dC + κ.dA + κ.dR) + 6 * (κ.mA + κ.mB + κ.mC + κ.mD + κ.mF + κ.mE)

theorem need_le (κ : FreeK) (Ds : ℕ) (x : FreeIn) (hs : FreeSmall Ds x) :
    need κ x ≤ needK κ * 2 ^ (needD κ Ds * (natBitLength x.n + 1) ^ 2) := by
  obtain ⟨hkh, hnc, ha, hM⟩ := hs
  have hB := beta_le_B x
  have hn := n_lt_B x.n
  obtain ⟨B, hBd⟩ : ∃ B, B = natBitLength x.n := ⟨_, rfl⟩
  rw [← hBd] at hkh hnc ha hM hB hn ⊢
  have hQ : 1 ≤ (B + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hpw : ∀ e, e ≤ needD κ Ds * (B + 1) ^ 2 → 2 ^ e ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) :=
    fun e he => Nat.pow_le_pow_right (by norm_num) he
  have hDg : ∀ c, c ≤ needD κ Ds → c * (B + 1) ^ 2 ≤ needD κ Ds * (B + 1) ^ 2 := fun c hc => Nat.mul_le_mul_right _ hc
  have hsq : (B + 1) * (B + 1) = (B + 1) ^ 2 := by ring
  have hU0 : 1 ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) := Nat.one_le_two_pow
  -- the atoms below `U = 2^{D(B+1)²}`
  have uN : x.n ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) :=
    hn.le.trans (hpw _ (by have := hDg 1 (by unfold needD; omega); nlinarith))
  have uB : β x ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) :=
    (hB.trans (le_two_pow_self _)).trans (hpw _ (by have := hDg 1 (by unfold needD; omega); nlinarith))
  have hbb : β x * β x ≤ (B + 1) ^ 2 := by rw [← hsq]; exact Nat.mul_le_mul hB hB
  have uG : β x * β x ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) :=
    (hbb.trans (le_two_pow_self _)).trans (hpw _ (by have := hDg 1 (by unfold needD; omega); omega))
  have uG4 : β x * β x * (β x * β x) ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) := by
    have h1 := Nat.mul_le_mul hbb hbb
    have h2 := sq_le_two_pow ((B + 1) ^ 2)
    exact (h1.trans h2).trans (hpw _ (by have := hDg 2 (by unfold needD; omega); omega))
  have uG6 : β x * β x * (β x * β x) * (β x * β x) ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) := by
    have h1 := Nat.mul_le_mul (Nat.mul_le_mul hbb hbb) hbb
    have h2 := sq_le_two_pow ((B + 1) ^ 2)
    have h3 := le_two_pow_self ((B + 1) ^ 2)
    have h4 : 2 ^ (2 * (B + 1) ^ 2) * 2 ^ ((B + 1) ^ 2) = 2 ^ (3 * (B + 1) ^ 2) := by rw [← pow_add]; ring_nf
    calc _ ≤ (B + 1) ^ 2 * (B + 1) ^ 2 * (B + 1) ^ 2 := h1
      _ ≤ 2 ^ (2 * (B + 1) ^ 2) * 2 ^ ((B + 1) ^ 2) := Nat.mul_le_mul h2 h3
      _ = 2 ^ (3 * (B + 1) ^ 2) := h4
      _ ≤ _ := hpw _ (by have := hDg 3 (by unfold needD; omega); omega)
  have uP : 2 ^ (κ.dC * (β x * β x) + 1) ≤ 2 * 2 ^ (needD κ Ds * (B + 1) ^ 2) := by
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (hpw _ ((Nat.mul_le_mul_left κ.dC hbb).trans (hDg κ.dC (by unfold needD; omega))))
  have uS : 2 ^ (Ds * (B + 1) ^ 2) ≤ 2 ^ (needD κ Ds * (B + 1) ^ 2) := hpw _ (hDg Ds (by unfold needD; omega))
  have uW : W x ≤ 5 * 2 ^ (needD κ Ds * (B + 1) ^ 2) := by have := W_le x; omega
  have uAW : x.a * W x ≤ 5 * 2 ^ (needD κ Ds * (B + 1) ^ 2) := by
    have h1 : x.a * W x ≤ 2 ^ (Ds * (B + 1) ^ 2) * (5 * 2 ^ ((B + 1) ^ 2)) := by
      refine Nat.mul_le_mul ha ?_
      have := W_le x
      have h2 : β x + 4 ≤ 5 * 2 ^ ((B + 1) ^ 2) := by
        have := (hB.trans (le_two_pow_self _)).trans (Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num)
          (show B + 1 ≤ (B + 1) ^ 2 by nlinarith))
        have : 1 ≤ 2 ^ ((B + 1) ^ 2) := Nat.one_le_two_pow
        omega
      omega
    have h3 : 2 ^ (Ds * (B + 1) ^ 2) * (5 * 2 ^ ((B + 1) ^ 2)) = 5 * 2 ^ ((Ds + 1) * (B + 1) ^ 2) := by
      rw [Nat.add_mul, pow_add, one_mul]; ring
    rw [h3] at h1
    exact h1.trans (Nat.mul_le_mul_left 5 (hpw _ (hDg (Ds + 1) (by unfold needD; omega))))
  unfold need
  have hPw : 1 ≤ 2 ^ (κ.dC * (β x * β x) + 1) := Nat.one_le_two_pow
  generalize 2 ^ (needD κ Ds * (B + 1) ^ 2) = U at uN uB uG uG4 uG6 uP uS uW uAW hU0 ⊢
  generalize 2 ^ (κ.dC * (β x * β x) + 1) = PW at uP hPw ⊢
  have p1 := Nat.mul_le_mul_left κ.dT uG
  have p2 := Nat.mul_le_mul_left κ.dQ uG
  have p3 := Nat.mul_le_mul_left κ.dH uG
  have p4 := Nat.mul_le_mul_left κ.dP uG6
  have p5 := Nat.mul_le_mul_left κ.dC uG
  have p6 := Nat.mul_le_mul_left κ.mA (hnc.trans uS)
  have p7 := Nat.mul_le_mul_left κ.mB uAW
  have p8 := Nat.mul_le_mul_left κ.mC uW
  have p9 := Nat.mul_le_mul_left κ.mD (ha.trans uS)
  have p10 := Nat.mul_le_mul_left κ.mF (hM.trans uS)
  have p11 := Nat.mul_le_mul_left κ.dA uB
  have p12 := Nat.mul_le_mul_left κ.dR uG
  have hU1 : 1 ≤ U := hU0
  have e : needK κ * U = 300 * U + 3 * (κ.dT * U) + 3 * (κ.dQ * U) + 3 * (κ.dH * U) + 3 * (κ.dP * U) +
      3 * (κ.dC * U) + 3 * (κ.dA * U) + 3 * (κ.dR * U) + 6 * (κ.mA * U) + 6 * (κ.mB * U) + 6 * (κ.mC * U) +
      6 * (κ.mD * U) + 6 * (κ.mF * U) + 6 * (κ.mE * U) := by unfold needK; ring
  have q1 : κ.dT ≤ κ.dT * U := Nat.le_mul_of_pos_right _ hU1
  have q2 : κ.dQ ≤ κ.dQ * U := Nat.le_mul_of_pos_right _ hU1
  have q3 : κ.dH ≤ κ.dH * U := Nat.le_mul_of_pos_right _ hU1
  have q4 : κ.dP ≤ κ.dP * U := Nat.le_mul_of_pos_right _ hU1
  have q5 : κ.dC ≤ κ.dC * U := Nat.le_mul_of_pos_right _ hU1
  have q6 : κ.dA ≤ κ.dA * U := Nat.le_mul_of_pos_right _ hU1
  have q7 : κ.dR ≤ κ.dR * U := Nat.le_mul_of_pos_right _ hU1
  have q8 : κ.mA ≤ κ.mA * U := Nat.le_mul_of_pos_right _ hU1
  have q9 : κ.mB ≤ κ.mB * U := Nat.le_mul_of_pos_right _ hU1
  have q10 : κ.mC ≤ κ.mC * U := Nat.le_mul_of_pos_right _ hU1
  have q11 : κ.mD ≤ κ.mD * U := Nat.le_mul_of_pos_right _ hU1
  have q12 : κ.mF ≤ κ.mF * U := Nat.le_mul_of_pos_right _ hU1
  have q13 : κ.mE ≤ κ.mE * U := Nat.le_mul_of_pos_right _ hU1
  have r7 : κ.mB * (5 * U) = 5 * (κ.mB * U) := by ring
  have r8 : κ.mC * (5 * U) = 5 * (κ.mC * U) := by ring
  rw [e]
  omega

/-! ## The record -/

theorem val_le_need (κ : FreeK) (x : FreeIn) (j : Fin 7) (hj : j.val ≠ 6) : freeVal κ x j ≤ need κ x := by
  unfold need
  have hP : 2 ^ (κ.dC * (β x * β x)) ≤ 2 ^ (κ.dC * (β x * β x) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  fin_cases j <;> simp [freeVal] at hj ⊢ <;> omega

theorem rho_le' (κ : FreeK) (x : FreeIn) : freeVal κ x 6 ≤ 4 * (1 + κ.dA + κ.dR) * (x.n + 1) ^ 2 := by
  have hb : β x ≤ x.n + 2 := by
    unfold β; exact Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have h1 := Nat.mul_le_mul_left κ.dA hb
  have h2 := Nat.mul_le_mul_left κ.dR (Nat.mul_le_mul hb hb)
  have e : 4 * (1 + κ.dA + κ.dR) * (x.n + 1) ^ 2 = 4 * ((x.n + 1) * (x.n + 1)) + 4 * κ.dA * ((x.n + 1) * (x.n + 1)) +
      4 * κ.dR * ((x.n + 1) * (x.n + 1)) := by ring
  have e2 : κ.dR * ((x.n + 2) * (x.n + 2)) ≤ 4 * κ.dR * ((x.n + 1) * (x.n + 1)) := by
    have : (x.n + 2) * (x.n + 2) ≤ 4 * ((x.n + 1) * (x.n + 1)) := by nlinarith
    calc κ.dR * ((x.n + 2) * (x.n + 2)) ≤ κ.dR * (4 * ((x.n + 1) * (x.n + 1))) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have e3 : κ.dA * (x.n + 2) ≤ 4 * κ.dA * ((x.n + 1) * (x.n + 1)) := by
    have : x.n + 2 ≤ 4 * ((x.n + 1) * (x.n + 1)) := by nlinarith
    calc κ.dA * (x.n + 2) ≤ κ.dA * (4 * ((x.n + 1) * (x.n + 1))) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have e4 : x.n ≤ 4 * ((x.n + 1) * (x.n + 1)) := by nlinarith
  rw [e]
  simp only [freeVal, Matrix.cons_val]
  apply max_le <;> omega

theorem two_pow_beta (x : FreeIn) : 2 ^ β x ≤ 4 * (x.n + 1) := by
  unfold β
  rcases Nat.lt_or_ge (x.n + 2) 3 with hs | hs
  · have h1 : Nat.clog 2 (x.n + 2) ≤ 1 := Nat.clog_le_of_le_pow (by omega)
    calc 2 ^ Nat.clog 2 (x.n + 2) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
      _ ≤ 4 * (x.n + 1) := by omega
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < x.n + 2 by omega)
    have h2 : 1 ≤ Nat.clog 2 (x.n + 2) := Nat.clog_pos (by norm_num) (by omega)
    have e : 2 ^ Nat.clog 2 (x.n + 2) = 2 * 2 ^ (Nat.clog 2 (x.n + 2) - 1) := by
      conv_lhs => rw [show Nat.clog 2 (x.n + 2) = Nat.clog 2 (x.n + 2) - 1 + 1 by omega]
      rw [pow_succ]; ring
    rw [Nat.pred_eq_sub_one] at h1
    omega

theorem padX' (κ : FreeK) (x : FreeIn) :
    2 ^ freeVal κ x 6 ≤ (4 ^ κ.dA + 1) * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.dA + κ.dR) +
      2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2)) := by
  simp only [freeVal, Matrix.cons_val]
  have hA : 2 ^ (x.n - (x.kh + x.kh) + κ.dA * β x) ≤ 4 ^ κ.dA * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.dA + κ.dR)) := by
    rw [pow_add, Nat.mul_comm κ.dA (β x), pow_mul]
    have h1 : (2 ^ β x) ^ κ.dA ≤ (4 * (x.n + 1)) ^ κ.dA := Nat.pow_le_pow_left (two_pow_beta x) _
    rw [mul_pow] at h1
    have h2 : (x.n + 1) ^ κ.dA ≤ (x.n + 1) ^ (κ.dA + κ.dR) := Nat.pow_le_pow_right (by omega) (by omega)
    calc 2 ^ (x.n - (x.kh + x.kh)) * (2 ^ β x) ^ κ.dA ≤ 2 ^ (x.n - (x.kh + x.kh)) * (4 ^ κ.dA * (x.n + 1) ^ κ.dA) :=
          Nat.mul_le_mul_left _ h1
      _ ≤ 2 ^ (x.n - (x.kh + x.kh)) * (4 ^ κ.dA * (x.n + 1) ^ (κ.dA + κ.dR)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
      _ = _ := by ring
  have hR : 2 ^ (κ.dR * (β x * β x)) ≤ 2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2) := by
    have hB := beta_le_B x
    have hbb : β x * β x ≤ (natBitLength x.n + 1) ^ 2 := by
      have := Nat.mul_le_mul hB hB; rw [sq]; exact this
    have h1 : 2 ^ (κ.dR * (β x * β x)) ≤ 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul (by omega) hbb)
    exact h1.trans (Nat.le_mul_of_pos_left _ Nat.one_le_two_pow)
  have hmax : 2 ^ max (x.n - (x.kh + x.kh) + κ.dA * β x) (κ.dR * (β x * β x)) ≤
      2 ^ (x.n - (x.kh + x.kh) + κ.dA * β x) + 2 ^ (κ.dR * (β x * β x)) := by
    rcases le_total (x.n - (x.kh + x.kh) + κ.dA * β x) (κ.dR * (β x * β x)) with h | h
    · rw [max_eq_right h]; exact Nat.le_add_left _ _
    · rw [max_eq_left h]; exact Nat.le_add_right _ _
  have e : (4 ^ κ.dA + 1) * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.dA + κ.dR) +
      2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2)) =
      4 ^ κ.dA * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.dA + κ.dR)) +
      2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.dA + κ.dR) +
      (4 ^ κ.dA + 1) * (2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2)) := by ring
  have h3 : 2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2) ≤
      (4 ^ κ.dA + 1) * (2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  rw [e]
  generalize 2 ^ max (x.n - (x.kh + x.kh) + κ.dA * β x) (κ.dR * (β x * β x)) = A at hmax ⊢
  generalize 2 ^ (x.n - (x.kh + x.kh) + κ.dA * β x) = A1 at hmax hA ⊢
  generalize 2 ^ (κ.dR * (β x * β x)) = A2 at hmax hR ⊢
  generalize 2 ^ (x.n / 2) * 2 ^ ((κ.dA + κ.dR) * (natBitLength x.n + 1) ^ 2) = A3 at hR h3 ⊢
  generalize 4 ^ κ.dA * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.dA + κ.dR)) = A4 at hA ⊢
  generalize (4 ^ κ.dA + 1) * A3 = A5 at h3 ⊢
  omega

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

