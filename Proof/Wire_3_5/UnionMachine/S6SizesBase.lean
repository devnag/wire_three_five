import Proof.Wire_3_5.Primitive.Writers.S6FitBase
import Proof.Wire_3_5.FinalPass.SymBuildBase
import Proof.Wire_3_5.Primitive.Writers.ThrCap4Base
import Proof.Wire_3_5.Primitive.SeedFix.TabThrLayout

/-! # N1–N3: the final pass's request sizes, `∀ l`, at the S6Fit statements

The S6 (`S6Fit.s6Target`) reads three bounds on the call family of `gate0 l F`, exponents before `F`, coefficients
after (verbatim in `PrimAsm.S6Fit`):

* **N1 `FpInBound`**: `|fpIn| + 1 ≤ K_in·2^k·(n+1)^{D_in}` — the request word (`CallSize.gate_word_length_le`,
  `wordBound_poly`), the printed sample `Q` pairs of `2(2kh+1)` bits (`sampleWord_len`, `Q ≤ 2^{(5kh+3)/4}·poly`,
  `CallIndexR.symCount_leR` / `thrCount_leR`, `(5kh+3)/4 ≤ 2kh = k`), the THR hash bits `≤ c_H·L²` (`ThrSide2.hbC_le`);
* **N2 `SeedCountBound`**: `|GapSeed| ≤ gapK·N^{gapZR l fe}` (`CallIndexR.gapSeed_leR`);
* **N3 `PtCountBound`**: `|centers|·|GapSeed|·Q ≤ K_p·2^{n−⌊k/4⌋}·(n+1)^{D_q}` — `|centers| = 2^{n−k}` (`card_centers`),
  `n − k + ⌊(5kh+3)/4⌋ ≤ n − ⌊k/4⌋ + 1` at `k = 2kh ≤ n` (`SymFr.kh_two`, `NumsX.rs_le`).

Every call of the family is on-star (`Call ⊇ StarAt`), so the off-star branches never occur.

* `sampleWord_len`, `pt_arith`, `in_arith`, `cW`, `dW`, `wordBound_le`, `DqS`, `KpS`, `DinS`, `KinS`,
  **`seedCount_bound`**, **`ptCount_bound`**, **`fpIn_bound`**.

Paper quantities of the main types: the final pass's input length, the filter seeds, the point evaluations
`|centers|·|E|·Q` (prim:runtime P3:3105-3115, P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.S6Sizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline

/-- The printed sample's length: `Q` pairs of framed `kh`-bit halves. -/
theorem sampleWord_len (kh : ℕ) (S : List (ℕ × ℕ)) :
    (FinalPass.Sample.sampleWord kh S).length = S.length * (4 * kh + 2) := by
  induction S with
  | nil => simp [FinalPass.Sample.sampleWord]
  | cons p S ih =>
      simp only [FinalPass.Sample.sampleWord, List.flatMap_cons, List.length_append, RepairOrdinary.frame_length,
        RepairOrdinary.SignedSortKey.binary_length, List.length_cons] at ih ⊢
      rw [ih]
      ring

/-- N3's arithmetic: `2^{n−k}·G·Q ≤ 2c₁c₂2^{D}·2^{n−⌊k/4⌋}·(n+1)^{D}`. -/
theorem pt_arith (n K h g z Dq G Q c1 c2 : ℕ) (hK : 2 * h = K) (hKn : K ≤ n) (hG : G ≤ c1 * (n + 2) ^ g)
    (hQ : Q ≤ 2 ^ ((5 * h + 3) / 4) * (c2 * (n + 2) ^ z)) (hD : g + z ≤ Dq) :
    2 ^ (n - K) * G * Q ≤ 2 * c1 * c2 * 2 ^ Dq * 2 ^ (n - K / 4) * (n + 1) ^ Dq := by
  have e1 : 2 ^ (n - K) * 2 ^ ((5 * h + 3) / 4) ≤ 2 * 2 ^ (n - K / 4) := by
    rw [← pow_add]
    calc 2 ^ (n - K + (5 * h + 3) / 4) ≤ 2 ^ (n - K / 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 * 2 ^ (n - K / 4) := by rw [pow_succ]; ring
  have e2 : (n + 2) ^ g * (n + 2) ^ z ≤ 2 ^ Dq * (n + 1) ^ Dq := by
    rw [← pow_add]
    calc (n + 2) ^ (g + z) ≤ (n + 2) ^ Dq := Nat.pow_le_pow_right (by omega) hD
      _ ≤ (2 * (n + 1)) ^ Dq := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ Dq * (n + 1) ^ Dq := by rw [mul_pow]
  calc 2 ^ (n - K) * G * Q ≤ 2 ^ (n - K) * (c1 * (n + 2) ^ g) * (2 ^ ((5 * h + 3) / 4) * (c2 * (n + 2) ^ z)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hG) hQ
    _ = (2 ^ (n - K) * 2 ^ ((5 * h + 3) / 4)) * (c1 * c2) * ((n + 2) ^ g * (n + 2) ^ z) := by ring
    _ ≤ (2 * 2 ^ (n - K / 4)) * (c1 * c2) * (2 ^ Dq * (n + 1) ^ Dq) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ e1) e2
    _ = 2 * c1 * c2 * 2 ^ Dq * 2 ^ (n - K / 4) * (n + 1) ^ Dq := by ring

/-- N1's arithmetic: the word, the sample and the hash bits below `(c_w + 2c + c_H + 1)2^{D}·2^k·(n+1)^{D}`. -/
theorem in_arith (n K h Q W S H z Din cw dw c cH : ℕ) (hK : 2 * h = K) (hKn : K ≤ n) (hW : W ≤ cw * (n + 1) ^ dw)
    (hQ : Q ≤ 2 ^ ((5 * h + 3) / 4) * (c * (n + 2) ^ z)) (hS : S ≤ Q * (4 * h + 2) + H) (hH : H ≤ cH * (n + 2) ^ 2)
    (hD1 : dw ≤ Din) (hD2 : z + 1 ≤ Din) (hD3 : 2 ≤ Din) :
    W + S + 1 ≤ (cw + 2 * c + cH + 1) * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by
  have hNX : (n + 2) ^ Din ≤ 2 ^ Din * (n + 1) ^ Din := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have hT1 : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  have hD1' : 1 ≤ 2 ^ Din := Nat.one_le_two_pow
  have hX1 : 1 ≤ (n + 1) ^ Din := Nat.one_le_pow _ _ (by omega)
  have hE : 2 ^ ((5 * h + 3) / 4) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTX : 1 ≤ 2 ^ Din * 2 ^ K * (n + 1) ^ Din := Nat.mul_pos (Nat.mul_pos hD1' hT1) hX1
  have a1 : W ≤ cw * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by
    refine hW.trans ?_
    calc cw * (n + 1) ^ dw ≤ cw * (n + 1) ^ Din := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hD1)
      _ ≤ cw * (2 ^ Din * 2 ^ K * (n + 1) ^ Din) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.mul_pos hD1' hT1))
      _ = cw * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by ring
  have a2 : Q * (4 * h + 2) ≤ 2 * c * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by
    have q1 : Q ≤ 2 ^ K * (c * (n + 2) ^ z) := hQ.trans (Nat.mul_le_mul_right _ hE)
    have q2 : 4 * h + 2 ≤ 2 * (n + 2) := by omega
    calc Q * (4 * h + 2) ≤ (2 ^ K * (c * (n + 2) ^ z)) * (2 * (n + 2)) := Nat.mul_le_mul q1 q2
      _ = 2 * c * 2 ^ K * (n + 2) ^ (z + 1) := by ring
      _ ≤ 2 * c * 2 ^ K * (n + 2) ^ Din := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hD2)
      _ ≤ 2 * c * 2 ^ K * (2 ^ Din * (n + 1) ^ Din) := Nat.mul_le_mul_left _ hNX
      _ = 2 * c * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by ring
  have a3 : H ≤ cH * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by
    refine hH.trans ?_
    calc cH * (n + 2) ^ 2 ≤ cH * (n + 2) ^ Din := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hD3)
      _ ≤ cH * (2 ^ Din * (n + 1) ^ Din) := Nat.mul_le_mul_left _ hNX
      _ ≤ cH * (2 ^ Din * 2 ^ K * (n + 1) ^ Din) := by
          apply Nat.mul_le_mul_left
          calc 2 ^ Din * (n + 1) ^ Din = 2 ^ Din * 1 * (n + 1) ^ Din := by ring
            _ ≤ 2 ^ Din * 2 ^ K * (n + 1) ^ Din :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hT1)
      _ = cH * 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by ring
  have e : (cw + 2 * c + cH + 1) * 2 ^ Din * 2 ^ K * (n + 1) ^ Din =
      cw * 2 ^ Din * 2 ^ K * (n + 1) ^ Din + 2 * c * 2 ^ Din * 2 ^ K * (n + 1) ^ Din +
        cH * 2 ^ Din * 2 ^ K * (n + 1) ^ Din + 2 ^ Din * 2 ^ K * (n + 1) ^ Din := by ring
  rw [e]
  omega

/-- The request word's polynomial (`CallSize.wordBound_poly`): coefficient. -/
noncomputable def cW : ℕ := Classical.choose CallSize.wordBound_poly

/-- The request word's polynomial: degree. -/
noncomputable def dW : ℕ := Classical.choose (Classical.choose_spec CallSize.wordBound_poly)

theorem wordBound_le (n : ℕ) : CallSize.wordBound 26 26 2 n ≤ cW * (n + 1) ^ dW :=
  (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2 n

/-- N3's coefficient (`c_r`, before the power of two). -/
def KpS (cr : ℕ) : ℕ := 2 * CallIndexR.gapK cr * (8192 * (CallIndexR.symKI cr + CallIndexR.gapK cr))

end NearCubicWires.WireExponent3_5.UnionMachine.S6Sizes
