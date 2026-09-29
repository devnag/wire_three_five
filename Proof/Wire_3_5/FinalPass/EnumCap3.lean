import Proof.Wire_3_5.FinalPass.EnumCap2

/-! # The enumeration's side conditions at a call, generic in the batch, part 3: `qG` below a power of two

P3:3011-3016. The group size bound `qG` (the reference one) is below `2^E` with `E` linear in the entry-count exponent, the
row-word exponent and the call's small numbers: `qG + 1 ≤ 2^{e_N + 2x + (8R+1)e_b + 5}`,
`x = 14 + 24ℓ + 40k_h + TWd + |p'| + 8R`, whenever `n_T ≤ 2^{e_N}` and `1 ≤ b ≤ 2^{e_b}`. The row words of a printed
batch meet the shape bound `T·(w·(K·(2D(A+1)+2)+2)+7)+1` (BShape6 `exprWord_le`), which is below
`2^{e_T+e_w+e_K+e_D+e_A+4}`. Mode-generic.

* `foldr_max_le`, **`bsz_le`**, **`wordB_le`**, `xG`, **`qG_lt_pow`**.

Paper quantity of the main type: the group's size bound as a power of two. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)

theorem foldr_max_le (B : ℕ) (h1 : 1 ≤ B) : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ B) → l.foldr max 1 ≤ B
  | [], _ => by simpa using h1
  | x :: t, h => by
    rw [List.foldr_cons]
    exact max_le (h x (List.mem_cons_self ..)) (foldr_max_le B h1 t (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- **The batch's row-word bound** below any common bound of its rows' words. -/
theorem bsz_le (batch : List SExpr) (B : ℕ) (h1 : 1 ≤ B) (h : ∀ V ∈ batch, (exprWord V).length ≤ B) :
    PrimT.C4Grp.bsz batch ≤ B := by
  unfold PrimT.C4Grp.bsz
  refine foldr_max_le B h1 _ (fun x hx => ?_)
  obtain ⟨V, hV, rfl⟩ := List.mem_map.mp hx
  exact h V hV

/-- **The row-word shape below a power of two.** -/
theorem wordB_le (T w K D A eT ew eK eD eA : ℕ) (hT : T ≤ 2 ^ eT) (hw : w ≤ 2 ^ ew) (hK : K ≤ 2 ^ eK)
    (hD : D ≤ 2 ^ eD) (hA : A + 1 ≤ 2 ^ eA) :
    T * (w * (K * (2 * D * (A + 1) + 2) + 1 + 1) + 6 + 1) + 1 ≤ 2 ^ (eT + ew + eK + eD + eA + 4) := by
  have e : 2 ^ (eT + ew + eK + eD + eA + 4) = 16 * (2 ^ eT * (2 ^ ew * (2 ^ eK * (2 ^ eD * 2 ^ eA)))) := by
    rw [pow_add, pow_add, pow_add, pow_add, pow_add]
    ring
  rw [e]
  have ha : 1 ≤ 2 ^ eT := Nat.one_le_two_pow
  have hb : 1 ≤ 2 ^ ew := Nat.one_le_two_pow
  have hc : 1 ≤ 2 ^ eK := Nat.one_le_two_pow
  have hd : 1 ≤ 2 ^ eD := Nat.one_le_two_pow
  have hf : 1 ≤ 2 ^ eA := Nat.one_le_two_pow
  generalize 2 ^ eT = a at hT ha ⊢
  generalize 2 ^ ew = b at hw hb ⊢
  generalize 2 ^ eK = c at hK hc ⊢
  generalize 2 ^ eD = d at hD hd ⊢
  generalize 2 ^ eA = f at hA hf ⊢
  have p1 : 1 ≤ d * f := Nat.mul_pos hd hf
  have s1 : 2 * D * (A + 1) + 2 ≤ 4 * (d * f) := by
    have k := Nat.mul_le_mul hD hA
    have e1 : 2 * D * (A + 1) = 2 * (D * (A + 1)) := by ring
    omega
  have p2 : 1 ≤ c * (d * f) := Nat.mul_pos hc p1
  have s2 : K * (2 * D * (A + 1) + 2) + 1 + 1 ≤ 6 * (c * (d * f)) := by
    have k := Nat.mul_le_mul hK s1
    have e1 : c * (4 * (d * f)) = 4 * (c * (d * f)) := by ring
    omega
  have p3 : 1 ≤ b * (c * (d * f)) := Nat.mul_pos hb p2
  have s3 : w * (K * (2 * D * (A + 1) + 2) + 1 + 1) + 6 + 1 ≤ 13 * (b * (c * (d * f))) := by
    have k := Nat.mul_le_mul hw s2
    have e1 : b * (6 * (c * (d * f))) = 6 * (b * (c * (d * f))) := by ring
    omega
  have p4 : 1 ≤ a * (b * (c * (d * f))) := Nat.mul_pos ha p3
  have k := Nat.mul_le_mul hT s3
  have e1 : a * (13 * (b * (c * (d * f)))) = 13 * (a * (b * (c * (d * f)))) := by ring
  omega

/-- The call's small numbers in `qG`'s exponent. -/
def xG (P : SeedParams) (R TWd plen : ℕ) : ℕ := 14 + 24 * P.ell + 40 * P.kh + TWd + plen + 8 * R

/-- **`qG` below a power of two**: `qG + 1 ≤ 2^{e_N + 2x + (8R+1)e_b + 5}`. -/
theorem qG_lt_pow (P : SeedParams) (nT R b TWd plen eN eb : ℕ) (hb1 : 1 ≤ b) (hb : b ≤ 2 ^ eb)
    (hnT : nT ≤ 2 ^ eN) :
    PrimT.C4Grp.qG P nT R b TWd plen + 1 ≤ 2 ^ (eN + 2 * xG P R TWd plen + (8 * R + 1) * eb + 5) := by
  obtain ⟨X, hXd⟩ : ∃ X, X = xG P R TWd plen := ⟨_, rfl⟩
  rw [← hXd]
  have hX : X < 2 ^ X := Nat.lt_two_pow_self
  have hsm : 8 * P.ell + 2 * P.kh + TWd + 8 + plen + R ≤ X := by rw [hXd]; unfold xG; omega
  have hT0 : PrimT.C4Grp.T0 P + 8 * R + 1 ≤ X := by rw [hXd]; unfold xG PrimT.C4Grp.T0; omega
  have hkh2 : (2 ^ P.kh) ^ 2 ≤ 2 ^ X := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by rw [hXd]; unfold xG; omega)
  have hW : 2 ^ (8 + 8 * P.ell + 8 * P.kh) ≤ 2 ^ X :=
    Nat.pow_le_pow_right (by norm_num) (by rw [hXd]; unfold xG; omega)
  have hbR : b ^ (8 * R) ≤ (2 ^ eb) ^ (8 * R) := Nat.pow_le_pow_left hb _
  have hTb : PrimT.C4Grp.T0 P + 8 * R * b + 1 ≤ 2 ^ X * 2 ^ eb := by
    have e1 : (PrimT.C4Grp.T0 P + 8 * R + 1) * b = PrimT.C4Grp.T0 P * b + 8 * R * b + b := by ring
    have h1 : PrimT.C4Grp.T0 P ≤ PrimT.C4Grp.T0 P * b := Nat.le_mul_of_pos_right _ hb1
    have h2 : (PrimT.C4Grp.T0 P + 8 * R + 1) * b ≤ 2 ^ X * 2 ^ eb := Nat.mul_le_mul (by omega) hb
    omega
  have hFs : PrimT.C4Grp.Fs P R b ≤ 2 * ((2 ^ eb) ^ (8 * R) * (2 ^ X * 2 ^ eb)) := by
    unfold PrimT.C4Grp.Fs
    have k := Nat.mul_le_mul hbR hTb
    have h1 : 1 ≤ (2 ^ eb) ^ (8 * R) * (2 ^ X * 2 ^ eb) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hN : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1 ≤ 2 * (2 ^ eN * 2 ^ X) := by
    have k := Nat.mul_le_mul hnT hW
    have h1 : 1 ≤ 2 ^ eN * 2 ^ X := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hprod : (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1) * PrimT.C4Grp.Fs P R b ≤
      4 * (2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) :=
    calc _ ≤ (2 * (2 ^ eN * 2 ^ X)) * (2 * ((2 ^ eb) ^ (8 * R) * (2 ^ X * 2 ^ eb))) := Nat.mul_le_mul hN hFs
      _ = 4 * (2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) := by ring
  have hA1 : 1 ≤ 2 ^ eN := Nat.one_le_two_pow
  have hB1 : 1 ≤ 2 ^ X := Nat.one_le_two_pow
  have hC1 : 1 ≤ 2 ^ eb := Nat.one_le_two_pow
  have hD1 : 1 ≤ (2 ^ eb) ^ (8 * R) := Nat.one_le_pow _ _ hC1
  have hnk : nT * (2 ^ P.kh) ^ 2 ≤ 2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) := by
    have k := Nat.mul_le_mul hnT hkh2
    have m1 : 2 ^ eN * 2 ^ X ≤ 2 ^ eN * 2 ^ X * (2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos hB1 hC1) hD1)
    have e1 : 2 ^ eN * 2 ^ X * (2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) =
        2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) := by ring
    omega
  have hbM : b ≤ 2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) := by
    have m1 : 2 ^ eb ≤ 2 ^ eb * (2 ^ eN * 2 ^ X * 2 ^ X * (2 ^ eb) ^ (8 * R)) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA1 hB1) hB1) hD1)
    have e1 : 2 ^ eb * (2 ^ eN * 2 ^ X * 2 ^ X * (2 ^ eb) ^ (8 * R)) =
        2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) := by ring
    omega
  have hXM : 2 ^ X ≤ 2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) := by
    have m1 : 2 ^ X ≤ 2 ^ X * (2 ^ eN * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hA1 hB1) hC1) hD1)
    have e1 : 2 ^ X * (2 ^ eN * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) =
        2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) := by ring
    omega
  have e : 2 ^ (eN + 2 * X + (8 * R + 1) * eb + 5) = 32 * (2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R)) := by
    rw [← pow_mul, show eN + 2 * X + (8 * R + 1) * eb + 5 = eN + X + X + eb + eb * (8 * R) + 5 by ring]
    rw [pow_add, pow_add, pow_add, pow_add, pow_add]
    ring
  rw [e]
  unfold PrimT.C4Grp.qG
  generalize 2 ^ eN * 2 ^ X * 2 ^ X * 2 ^ eb * (2 ^ eb) ^ (8 * R) = M at hprod hnk hbM hXM ⊢
  generalize (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1) * PrimT.C4Grp.Fs P R b = Y at hprod ⊢
  generalize nT * (2 ^ P.kh) ^ 2 = Z at hnk ⊢
  generalize 2 ^ X = B at hX hXM
  omega

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
