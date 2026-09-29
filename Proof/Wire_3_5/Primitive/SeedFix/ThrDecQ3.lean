import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ2
import Proof.Wire_3_5.Primitive.ThresholdWriter.TF3Cost

/-! # THR decode front, packaging part 3: the front's needs from the call's atom bounds

**`Atoms`**: the call's register values, each at most `Q·2^{A·Y}` (`Y = L²`); **`tneed_arith`**, **`fneed_arith`**: the
numbers phase's needs `TNeed` and the front's needs `FNeed` at `c₀ = QY Q Y (A + 9) (A² + 60A + 60)`.

Paper quantity of the main type: the front's capacity within `2^{O(L²)}` (P3:2597-2599). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrDecF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm

/-- **The call's atom bounds.** -/
structure Atoms (Q Y A : ℕ) (w : List Bool) (n : ℕ) (codes cc : List ℕ) (Kb cr fe : ℕ) (hs xs : List ℕ) (tg : ℕ)
    (FP : GapParams) (kh : ℕ) (L : List ℕ) (Cn Dn : ℕ) : Prop where
  hQ : 1 ≤ Q
  hY : 1 ≤ Y
  hA : 8 ≤ A
  aw : w.length ≤ QY Q Y 0 A
  an : n + 3 ≤ QY Q Y 0 A
  an26 : (n + 1) ^ 26 * 2 ≤ QY Q Y 0 A
  acodes : codes.length ≤ 4
  acc : cc.length ≤ 2
  aKb : Kb ≤ w.length
  acr : cr ≤ QY Q Y 0 A
  afe : fe + 4 ≤ QY Q Y 0 A
  afeL : fe * Nat.clog 2 (n + 2) ≤ QY Q Y 0 A
  ahsl : hs.length = 16
  ahs : ∀ k, hs.getD k 0 ≤ QY Q Y 1 A
  axsl : xs.length ≤ 2
  axs : ∀ k, (xs ++ [tg]).getD k 0 ≤ QY Q Y 0 A
  acap : FP.cap = hs.getD 1 0
  alen : FP.len + 8 ≤ QY Q Y 0 A
  aerr : FP.errExp + 4 ≤ QY Q Y 0 A
  asb : FP.seedBits + 1 ≤ A * Y
  alfw : FP.labelBits + FP.fieldBits + FP.walkLen + 512 ≤ QY Q Y 0 A
  akh : 2 * kh + 1 ≤ A * Y
  aCn : Cn ≤ QY Q Y 0 A
  aDn : Dn ≤ A
  aL : (Data.unaryList L).length ≤ QY Q Y 1 A

/-- The atoms' common bound `U = Q·2^{(A+2)·Y}`. -/
def UQ (Q Y A : ℕ) : ℕ := QY Q Y 1 (A + 2)

/-- The front's virtual capacity `c₀ = U^{3A+20}`. -/
def cZero (Q Y A : ℕ) : ℕ := UQ Q Y A ^ (3 * A + 20)

section Arith
variable {Q Y A : ℕ} {w : List Bool} {n : ℕ} {codes cc : List ℕ} {Kb cr fe : ℕ} {hs xs : List ℕ} {tg : ℕ}
  {FP : GapParams} {kh : ℕ} {L : List ℕ} {Cn Dn : ℕ}

theorem U_ge (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) : 1024 ≤ UQ Q Y A := by
  have hQ := hAt.hQ
  have hY := hAt.hY
  have hA := hAt.hA
  unfold UQ QY
  have h1 : 2 ^ 10 ≤ 2 ^ ((A + 2) * Y) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h2 : 1 ≤ Q ^ 1 := by simpa using hQ
  calc 1024 = 1 * 2 ^ 10 := by norm_num
    _ ≤ Q ^ 1 * 2 ^ ((A + 2) * Y) := Nat.mul_le_mul h2 h1

theorem at_U (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) {X i a : ℕ} (h : X ≤ QY Q Y i a)
    (hi : i ≤ 1) (ha : a ≤ A + 2) : X ≤ UQ Q Y A := qy_mono hAt.hQ h hi ha

theorem at_2powU (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) {e : ℕ} (he : e ≤ A * Y) :
    2 ^ e ≤ UQ Q Y A := by
  have hQ := hAt.hQ
  unfold UQ QY
  calc 2 ^ e ≤ 1 * 2 ^ ((A + 2) * Y) := by
        rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) (le_trans he (Nat.mul_le_mul_right _ (by omega)))
    _ ≤ Q ^ 1 * 2 ^ ((A + 2) * Y) := Nat.mul_le_mul (by simpa using hQ) le_rfl

theorem U_pow_le (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) {k : ℕ} (hk : k ≤ 3 * A + 20) :
    UQ Q Y A ^ k ≤ cZero Q Y A := Nat.pow_le_pow_right (by have := U_ge hAt; omega) hk

theorem c_mul_U (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) {c k : ℕ} (hc : c ≤ 1024)
    (hk : k + 1 ≤ 3 * A + 20) : c * UQ Q Y A ^ k ≤ cZero Q Y A := by
  have hU := U_ge hAt
  calc c * UQ Q Y A ^ k ≤ UQ Q Y A * UQ Q Y A ^ k := Nat.mul_le_mul_right _ (by omega)
    _ = UQ Q Y A ^ (k + 1) := by ring
    _ ≤ cZero Q Y A := U_pow_le hAt hk

/-- The atoms below `U`. -/
theorem atomsU (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) :
    w.length ≤ UQ Q Y A ∧ n + 3 ≤ UQ Q Y A ∧ (n + 1) ^ 26 * 2 ≤ UQ Q Y A ∧ Kb ≤ UQ Q Y A ∧ cr ≤ UQ Q Y A ∧
    fe + 4 ≤ UQ Q Y A ∧ fe * Nat.clog 2 (n + 2) ≤ UQ Q Y A ∧ (∀ k, hs.getD k 0 ≤ UQ Q Y A) ∧
    (∀ k, (xs ++ [tg]).getD k 0 ≤ UQ Q Y A) ∧ FP.len + 8 ≤ UQ Q Y A ∧ FP.errExp + 4 ≤ UQ Q Y A ∧
    2 ^ (FP.seedBits + 1) ≤ UQ Q Y A ∧ 2 ^ FP.seedBits ≤ UQ Q Y A ∧
    FP.labelBits + FP.fieldBits + FP.walkLen + 512 ≤ UQ Q Y A ∧ 2 ^ (2 * kh + 1) ≤ UQ Q Y A ∧
    2 ^ (2 * kh) ≤ UQ Q Y A ∧ Cn ≤ UQ Q Y A ∧ (Data.unaryList L).length ≤ UQ Q Y A := by
  have hA := hAt.hA
  have hw := at_U hAt hAt.aw (by omega) (by omega)
  exact ⟨hw, at_U hAt hAt.an (by omega) (by omega), at_U hAt hAt.an26 (by omega) (by omega), hAt.aKb.trans hw,
    at_U hAt hAt.acr (by omega) (by omega), at_U hAt hAt.afe (by omega) (by omega),
    at_U hAt hAt.afeL (by omega) (by omega), fun k => at_U hAt (hAt.ahs k) le_rfl (by omega),
    fun k => at_U hAt (hAt.axs k) (by omega) (by omega), at_U hAt hAt.alen (by omega) (by omega),
    at_U hAt hAt.aerr (by omega) (by omega), at_2powU hAt hAt.asb, at_2powU hAt (by have := hAt.asb; omega),
    at_U hAt hAt.alfw (by omega) (by omega), at_2powU hAt hAt.akh, at_2powU hAt (by have := hAt.akh; omega),
    at_U hAt hAt.aCn (by omega) (by omega), at_U hAt hAt.aL le_rfl (by omega)⟩

/-- **The numbers phase's needs at `c₀`.** -/
theorem tneed_arith (hAt : Atoms Q Y A w n codes cc Kb cr fe hs xs tg FP kh L Cn Dn) :
    TNeed (cZero Q Y A) w n codes cc Kb cr fe hs xs tg FP kh := by
  obtain ⟨uw, un, un26, uKb, ucr, ufe, ufeL, uhs, uxs, ulen, uerr, usb1, usb, ulfw, ukh1, ukh, uCn, uL⟩ := atomsU hAt
  have hU := U_ge hAt
  have hA := hAt.hA
  set U := UQ Q Y A with hUd
  have U1 : U ≤ cZero Q Y A := by have := U_pow_le hAt (k := 1) (by omega); simpa using this
  have b1 := PrimThrW.TF3Cost.two_pow_nbl_le n
  have b2 := PrimThrW.TF3Cost.two_pow_nbl_le codes.length
  have b3 := PrimThrW.TF3Cost.two_pow_nbl_le cc.length
  have hc := hAt.acodes
  have hcc := hAt.acc
  have hxsl := hAt.axsl
  have hcap : FP.cap = hs.getD 1 0 := hAt.acap
  have h1 := uhs 1
  have h2 := uhs 2
  have h6 := uhs 6
  have UU : U * U ≤ cZero Q Y A := by have := U_pow_le hAt (k := 2) (by omega); rw [pow_two] at this; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := c_mul_U hAt (c := 4) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · have e1 : 2 ^ (natBitLength n + 1) ≤ 4 * n + 4 := by rw [pow_succ]; omega
    have e2 : 2 ^ (natBitLength codes.length + 1) ≤ 20 := by rw [pow_succ]; omega
    have e3 : 2 ^ (natBitLength cc.length + 1) ≤ 12 := by rw [pow_succ]; omega
    have := c_mul_U hAt (c := 16) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · have m : (fe + 4) * (n + 3) ≤ U * U := Nat.mul_le_mul ufe un
    have := c_mul_U hAt (c := 30) (k := 2) (by omega) (by omega)
    rw [pow_two] at this
    nlinarith
  · intro k; exact le_trans (by
      by_cases hk : k < hs.length
      · rw [List.getD_append _ _ _ _ hk]; exact uhs k
      · rw [List.getD_append_right _ _ _ _ (by omega)]; exact uxs (k - hs.length)) U1
  · have := c_mul_U hAt (c := 8) (k := 1) (by omega) (by omega); rw [pow_one] at this; rw [hcap]; omega
  · have := c_mul_U hAt (c := 40) (k := 1) (by omega) (by omega); rw [pow_one] at this; rw [hcap]; omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · have := c_mul_U hAt (c := 4) (k := 1) (by omega) (by omega); rw [pow_one] at this; omega
  · have m := Nat.mul_le_mul usb h2
    omega
  · have m := Nat.mul_le_mul (Nat.mul_le_mul usb h2) h6
    have := U_pow_le hAt (k := 3) (by omega)
    have e : U ^ 3 = U * U * U := by ring
    rw [e] at this; omega
  · have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul usb h2) h6) ukh
    have := U_pow_le hAt (k := 4) (by omega)
    have e : U ^ 4 = U * U * U * U := by ring
    rw [e] at this; omega
  · have m := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul usb h2) h6) ukh)
      (show (xs.length + 1) * 3 + 2 ≤ U by omega)
    have := U_pow_le hAt (k := 5) (by omega)
    have e : U ^ 5 = U * U * U * U * U := by ring
    rw [e] at this; omega

end Arith

end NearCubicWires.WireExponent3_5.PrimT.ThrDecF
