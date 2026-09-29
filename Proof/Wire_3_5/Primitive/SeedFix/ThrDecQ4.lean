import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ3

/-! # THR decode front, packaging part 4: the front's needs `FNeed` at `c₀`

**`fneed_arith`**: from the call's atom bounds (`Atoms`, at the numbers machine's need constants `C_N`, `D_N`), the
front's capacity needs `FNeed` at `c₀ = U^{3A+20}` (the numbers phase's `TNeed` from `tneed_arith`; the unit layout,
`TOT`, the index, the FILTER bank, the docks' count `tV`, the post-dock sums).

Paper quantity of the main type: the front's capacity within `2^{O(L²)}` (P3:2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm

section Arith
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} (N : PrimThrW.Nums4.NumsPort4 alg Dexp)
variable {Q Y A : ℕ} {w : List Bool} {n : ℕ} {codes cc : List ℕ} {Kb cr fe : ℕ} {hs xs : List ℕ} {tg : ℕ}
  {FP : GapParams} {kh : ℕ} {L : List ℕ}

/-- **The front's needs at `c₀`.** -/
theorem fneed_arith (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L N.Cn N.Dn) :
    FNeed N (cZero Q Y A) w n codes cc Kb cr fe hs xs tg FP kh L := by
  obtain ⟨uw, un, un26, uKb, ucr, ufe, ufeL, uhs, uxs, ulen, uerr, usb1, usb, ulfw, ukh1, ukh, uCn, uL⟩ := atomsU hAt
  have hU := U_ge hAt
  have hA := hAt.hA
  have hDn := hAt.aDn
  have hxsl := hAt.axsl
  set U := UQ Q Y A with hUd
  have U1 : U ≤ cZero Q Y A := by have := U_pow_le hAt (k := 1) (by omega); simpa using this
  have h0 := uhs 0
  have h1 := uhs 1
  have h2 := uhs 2
  have h6 := uhs 6
  have h8 := uhs 8
  have x0 : xs.getD 0 0 ≤ U := by
    have := uxs 0
    rcases xs with _ | ⟨a, t⟩
    · simp
    · simpa using this
  have x1 : xs.getD 1 0 ≤ U := by
    have := uxs 1
    rcases xs with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp
    · simp
    · simpa using this
  have TOTb : 2 ^ FP.seedBits * hs.getD 2 0 * hs.getD 6 0 * 2 ^ (2 * kh) * ((xs.length + 1) * 3 + 2) ≤ U ^ 5 := by
    have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul usb h2) h6) ukh)
      (show (xs.length + 1) * 3 + 2 ≤ U by omega)
    have e : U ^ 5 = U * U * U * U * U := by ring
    rw [e]; exact m
  have U5 : U ^ 5 * 8 ≤ cZero Q Y A := by
    have := c_mul_U hAt (c := 8) (k := 5) (by omega) (by omega); rw [Nat.mul_comm]; exact this
  have U5' : 1 ≤ U ^ 5 := Nat.one_le_pow _ _ (by omega)
  have pD : (n + hs.getD 1 0 + 1) ^ N.Dn ≤ U ^ (2 * A) := by
    have b : n + hs.getD 1 0 + 1 ≤ U * U := by nlinarith
    calc (n + hs.getD 1 0 + 1) ^ N.Dn ≤ (U * U) ^ N.Dn := Nat.pow_le_pow_left b _
      _ = U ^ (2 * N.Dn) := by rw [← pow_two, ← pow_mul]
      _ ≤ U ^ (2 * A) := Nat.pow_le_pow_right (by omega) (by omega)
  have UA : U ^ (2 * A) ≤ U ^ (2 * A + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have UA2 : U ^ (2 * A + 1) * 16 ≤ cZero Q Y A := by
    have := c_mul_U hAt (c := 16) (k := 2 * A + 1) (by omega) (by omega); rw [Nat.mul_comm]; exact this
  have tVb : tV w.length n (hs.getD 1 0) N.Cn N.Dn ≤ U ^ (2 * A + 1) * 8 := by
    unfold tV
    have m : (n + hs.getD 1 0 + 1) ^ N.Dn * N.Cn ≤ U ^ (2 * A) * U := Nat.mul_le_mul pD uCn
    have e : U ^ (2 * A) * U = U ^ (2 * A + 1) := by ring
    rw [e] at m
    have : U ≤ U ^ (2 * A + 1) := by
      calc U = U ^ 1 := (pow_one U).symm
        _ ≤ U ^ (2 * A + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hsum : hs.sum ≤ 16 * U := by
    rw [sum16 hs hAt.ahsl]
    have := uhs 3; have := uhs 4; have := uhs 5; have := uhs 7; have := uhs 9; have := uhs 10; have := uhs 11
    have := uhs 12; have := uhs 13; have := uhs 14; have := uhs 15
    omega
  refine ⟨tneed_arith hAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · have : U ≤ U ^ 5 := by
      calc U = U ^ 1 := (pow_one U).symm
        _ ≤ U ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have := c_mul_U hAt (c := 12) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · have := c_mul_U hAt (c := 12) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · exact uCn.trans U1
  · exact pD.trans (U_pow_le hAt (by omega))
  · have : U ≤ U ^ (2 * A + 1) := by
      calc U = U ^ 1 := (pow_one U).symm
        _ ≤ U ^ (2 * A + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  · have := c_mul_U hAt (c := 4) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · have := c_mul_U hAt (c := 8) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · have := c_mul_U hAt (c := 40) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega

end Arith

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
