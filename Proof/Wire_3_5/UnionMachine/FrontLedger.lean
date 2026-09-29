import Proof.Wire_3_5.Foundations.Contracts
import Proof.Wire_3_5.Ledger.LedgerBudget

/-! # C6 front, the capacities' ledger (the approved capacity `C·2^{q−⌊k/4⌋}·(q+1)^D`)

"The time for one primitive call is `2^{q/2+O(k)} q^{O(1)} + 2^{O(Ψ)} q^{O(1)} + 2^{q−k} q^{O(1)} + 2^{q−k/4} q^{O(1)}`"
(prim:runtime, P3:3105-3115): at the row-B ledger (`rowBBudget` at the machines' contracts `costsOf E coef`), the
main pass dominates eventually, because the star width `k = r·⌊log₂(q/r+1)⌋ ≤ (2c_r+3)L²` and the load `Ψ` are `o(q)`
(`starWidth_le`, `rowBr_succ_le`, `eventually_load_le`), while `k ≥ A·L` eventually (`eventually_starWidth_ge`).
* **`cb_upper`**: eventually `callBudget q ≤ 4·coef·2^{q−⌊k/4⌋}·(q+1)^{A_main}`;
* **`cb_lower`**: `coef·2^{q−⌊k/4⌋}·q^{A_main} ≤ callBudget q` (the main pass alone);
* **`poly_small`**: eventually `c·(q+1)^d ≤ 2^{q−⌊k/4⌋}` for every `c`, `d`.
So the front's capacity `C·2^{q−⌊k/4⌋}·(q+1)^D` is within a constant and a power of `q+1` of `callBudget q`, and above
every polynomial in `q` eventually.

Paper quantity of the main type: the per-call running time `callBudget q` (P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontLedger
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Ledger Filter

section Ledger
variable {kclk : ℕ} (E : Envelope) (coef : ℕ) (P : RowBParams) (W : WidthData kclk E)

theorem pow_le_two_pow_Lq (q A : ℕ) : q ^ A ≤ 2 ^ (A * Lq q) := by
  have h : q ≤ 2 ^ Lq q := by
    unfold Lq
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (q + 2)
    omega
  calc q ^ A ≤ (2 ^ Lq q) ^ A := Nat.pow_le_pow_left h A
    _ = 2 ^ (A * Lq q) := by rw [← pow_mul, Nat.mul_comm]

theorem kOf_le (q : ℕ) :
    (rowBBudget E (Machine.costsOf E coef) P W).kOf q ≤ (2 * P.cr + 3) * (Lq q * Lq q) := by
  rw [rowBBudget_kOf]
  have h1 := starWidth_le (rowBr P.cr q) q
  have h2 := rowBr_succ_le P.cr q
  have h3 : rowBr P.cr q * Lq q ≤ (2 * P.cr + 3) * Lq q * Lq q := Nat.mul_le_mul_right _ (by omega)
  have e : (2 * P.cr + 3) * Lq q * Lq q = (2 * P.cr + 3) * (Lq q * Lq q) := by ring
  omega

/-- The per-call budget at the row-B ledger, unfolded. -/
theorem callBudget_eq (q : ℕ) : (rowBBudget E (Machine.costsOf E coef) P W).callBudget q =
    coef * (2 ^ (q / 2 + E.csel * (rowBBudget E (Machine.costsOf E coef) P W).kOf q) * q ^ E.Asel) +
    coef * (2 ^ (E.cpsi * (rowBBudget E (Machine.costsOf E coef) P W).psiOf q) * q ^ E.Apre) +
    coef * (2 ^ (q - (rowBBudget E (Machine.costsOf E coef) P W).kOf q) * q ^ E.Atable) +
    coef * (2 ^ (q - (rowBBudget E (Machine.costsOf E coef) P W).kOf q / 4) * q ^ E.Amain) := rfl

/-- **The main pass alone** bounds the per-call budget below. -/
theorem cb_lower (q : ℕ) :
    coef * (2 ^ (q - (rowBBudget E (Machine.costsOf E coef) P W).kOf q / 4) * q ^ E.Amain) ≤
      (rowBBudget E (Machine.costsOf E coef) P W).callBudget q := by
  rw [callBudget_eq]
  omega

/-- **The main pass dominates eventually**: `callBudget q ≤ 4·coef·2^{q−⌊k/4⌋}·(q+1)^{A_main}`. -/
theorem cb_upper : ∀ᶠ q : ℕ in atTop, (rowBBudget E (Machine.costsOf E coef) P W).callBudget q ≤
    4 * coef * (2 ^ (q - (rowBBudget E (Machine.costsOf E coef) P W).kOf q / 4) * (q + 1) ^ E.Amain) := by
  filter_upwards [eventually_load_le P.cap P.CD P.cr P.Csp P.sp P.sp_le (4 * E.cpsi),
    eventually_mul_Lq_pow_le (8 * (E.csel * (2 * P.cr + 3) + E.Asel + E.Apre + (2 * P.cr + 3) + 1)) 2,
    eventually_starWidth_ge P.cr (2 * E.Atable) P.cr_pos] with q hpsi hL hkge
  rw [callBudget_eq]
  have hk := kOf_le E coef P W q
  have hkge' : 2 * E.Atable * Lq q ≤ (rowBBudget E (Machine.costsOf E coef) P W).kOf q := by
    rw [rowBBudget_kOf]; exact hkge
  have hψ : 4 * E.cpsi * (rowBBudget E (Machine.costsOf E coef) P W).psiOf q ≤ q := by
    rw [rowBBudget_psiOf]; exact hpsi
  set k := (rowBBudget E (Machine.costsOf E coef) P W).kOf q with hkdef
  set ψ := (rowBBudget E (Machine.costsOf E coef) P W).psiOf q with hψdef
  set L := Lq q with hLdef
  set c1 := 2 * P.cr + 3 with hc1
  set K0 := E.csel * c1 + E.Asel + E.Apre + c1 + 1 with hK0
  set X := L * L with hX
  have hL1 : 1 ≤ L := Lq_pos q
  have hLX : L ≤ X := Nat.le_mul_of_pos_right L hL1
  have hLq : 8 * (K0 * X) ≤ q := by
    have e : 8 * K0 * L ^ 2 = 8 * (K0 * X) := by rw [hX]; ring
    omega
  have f1 : E.csel * k ≤ K0 * X := by
    calc E.csel * k ≤ E.csel * (c1 * X) := Nat.mul_le_mul_left _ hk
      _ = (E.csel * c1) * X := by ring
      _ ≤ K0 * X := Nat.mul_le_mul_right _ (by omega)
  have f2 : k ≤ K0 * X := hk.trans (Nat.mul_le_mul_right _ (by omega))
  have f3 : E.Asel * L ≤ K0 * X := (Nat.mul_le_mul_left _ hLX).trans (Nat.mul_le_mul_right _ (by omega))
  have f4 : E.Apre * L ≤ K0 * X := (Nat.mul_le_mul_left _ hLX).trans (Nat.mul_le_mul_right _ (by omega))
  have f5 : E.cpsi * ψ ≤ q / 4 := by
    have e : 4 * E.cpsi * ψ = 4 * (E.cpsi * ψ) := by ring
    omega
  have f6 : E.Atable * L ≤ k / 2 := by
    have e : 2 * E.Atable * L = 2 * (E.Atable * L) := by ring
    omega
  set m := q - k / 4 with hm
  have hsel : 2 ^ (q / 2 + E.csel * k) * q ^ E.Asel ≤ 2 ^ m := by
    calc 2 ^ (q / 2 + E.csel * k) * q ^ E.Asel ≤ 2 ^ (q / 2 + E.csel * k) * 2 ^ (E.Asel * L) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow_Lq q E.Asel)
      _ = 2 ^ (q / 2 + E.csel * k + E.Asel * L) := by rw [← pow_add]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpre : 2 ^ (E.cpsi * ψ) * q ^ E.Apre ≤ 2 ^ m := by
    calc 2 ^ (E.cpsi * ψ) * q ^ E.Apre ≤ 2 ^ (E.cpsi * ψ) * 2 ^ (E.Apre * L) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow_Lq q E.Apre)
      _ = 2 ^ (E.cpsi * ψ + E.Apre * L) := by rw [← pow_add]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have htab : 2 ^ (q - k) * q ^ E.Atable ≤ 2 ^ m := by
    calc 2 ^ (q - k) * q ^ E.Atable ≤ 2 ^ (q - k) * 2 ^ (E.Atable * L) :=
          Nat.mul_le_mul_left _ (pow_le_two_pow_Lq q E.Atable)
      _ = 2 ^ (q - k + E.Atable * L) := by rw [← pow_add]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmain : 2 ^ m * q ^ E.Amain ≤ 2 ^ m * (q + 1) ^ E.Amain :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h1 : 1 ≤ (q + 1) ^ E.Amain := Nat.one_le_pow _ _ (by omega)
  have h2 : 2 ^ m ≤ 2 ^ m * (q + 1) ^ E.Amain := Nat.le_mul_of_pos_right _ h1
  have hsum : 2 ^ (q / 2 + E.csel * k) * q ^ E.Asel + 2 ^ (E.cpsi * ψ) * q ^ E.Apre +
      2 ^ (q - k) * q ^ E.Atable + 2 ^ m * q ^ E.Amain ≤ 4 * (2 ^ m * (q + 1) ^ E.Amain) := by omega
  calc coef * (2 ^ (q / 2 + E.csel * k) * q ^ E.Asel) + coef * (2 ^ (E.cpsi * ψ) * q ^ E.Apre) +
        coef * (2 ^ (q - k) * q ^ E.Atable) + coef * (2 ^ m * q ^ E.Amain)
      = coef * (2 ^ (q / 2 + E.csel * k) * q ^ E.Asel + 2 ^ (E.cpsi * ψ) * q ^ E.Apre +
        2 ^ (q - k) * q ^ E.Atable + 2 ^ m * q ^ E.Amain) := by ring
    _ ≤ coef * (4 * (2 ^ m * (q + 1) ^ E.Amain)) := Nat.mul_le_mul_left _ hsum
    _ = 4 * coef * (2 ^ m * (q + 1) ^ E.Amain) := by ring

/-- **Every polynomial is eventually below `2^{q−⌊k/4⌋}`.** -/
theorem poly_small (c d : ℕ) : ∀ᶠ q : ℕ in atTop,
    c * (q + 1) ^ d ≤ 2 ^ (q - (rowBBudget E (Machine.costsOf E coef) P W).kOf q / 4) := by
  have h1 : ∀ᶠ μ : ℕ in atTop, c * (2 * μ + 2) ^ d ≤ 2 ^ μ := eventually_mul_affine_pow_le_two_pow c 2 2 d
  have hT : Tendsto (fun q : ℕ => q / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun q hq => by omega⟩
  filter_upwards [hT.eventually h1, eventually_mul_Lq_pow_le (2 * P.cr + 3) 2] with q hq hL
  have hk := kOf_le E coef P W q
  have e : (2 * P.cr + 3) * Lq q ^ 2 = (2 * P.cr + 3) * (Lq q * Lq q) := by ring
  calc c * (q + 1) ^ d ≤ c * (2 * (q / 2) + 2) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ ≤ 2 ^ (q / 2) := hq
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

end Ledger

end NearCubicWires.WireExponent3_5.UnionMachine.FrontLedger
