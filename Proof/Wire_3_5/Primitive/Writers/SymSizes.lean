import Proof.Wire_3_5.Primitive.Writers.SymLeafIface
import Proof.Wire_3_5.Primitive.Writers.NumsXSRun

/-! # SYM leaf, part 1: the POP rows fit the SYM dimension's POP term

The SYM dimension `m_S = mOfT K_F P + T` (`NumsXS.mS`) carries the POP term
`T = (3·J·(4S + 257) + 1)·(L·D₂ + K₀)` (`NumsXS.tS`) with `S = ⌈√(64²·B')⌉`, `J = bitlen B' + 9`,
`B' = 8192·B_S`. It is built to reach the POP row's counting capacity `(8L_s+2)^{3·lbP+1}` (`PopSetupSpecB.need_le`,
`PopPipeLe`), `L_s` a POP slice's length:

* `natCeilSqrt_le_of`, `natCeilSqrt_mono`, `ceilDiv_le_self`;
* **`lbP_le`**: `lbP Pl ≤ (bitlen B' + 9)·(4⌈√(64²B')⌉ + 257)` whenever `Pl.B ≤ B'` (list:base P3:1384-1398:
  `J` windows `W_j = 64 + ⌈⌈√(64²B)⌉/2^{⌊j/3⌋}⌉`);
* **`popY_le`**: `(8L_s+2)^{3·lbP+1} ≤ 2^T` when `⌈log₂(8L_s+2)⌉ ≤ L·D₂ + K₀`.

Paper quantities of the main types: the list bound `Σ_j W_j = O(√B + L)` (list:base P3:1376-1398) and the POP rows'
count (row:sym P3:2477-2496) within the SYM dimension. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink

theorem natCeilSqrt_le_of {x r : ℕ} (h : x ≤ r * r) : CanonicalFourfoldRowProgram.natCeilSqrt x ≤ r := by
  unfold CanonicalFourfoldRowProgram.natCeilSqrt
  have hs : Nat.sqrt x ≤ r := by
    calc Nat.sqrt x ≤ Nat.sqrt (r * r) := Nat.sqrt_le_sqrt h
      _ = r := Nat.sqrt_eq r
  simp only
  split_ifs with he
  · exact hs
  · have h1 : Nat.sqrt x * Nat.sqrt x ≤ x := Nat.sqrt_le x
    have h2 : Nat.sqrt x * Nat.sqrt x < r * r := by omega
    have h3 : Nat.sqrt x < r := Nat.mul_self_lt_mul_self_iff.mp h2
    omega

theorem natCeilSqrt_mono {x y : ℕ} (h : x ≤ y) :
    CanonicalFourfoldRowProgram.natCeilSqrt x ≤ CanonicalFourfoldRowProgram.natCeilSqrt y :=
  natCeilSqrt_le_of (le_trans h (CanonicalFourfoldRowProgram.le_natCeilSqrt_sq y))

theorem ceilDiv_le_self (a d : ℕ) (hd : 1 ≤ d) : a ⌈/⌉ d ≤ a := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Nat.div_eq_of_lt (by omega)]
  · apply Nat.div_le_of_le_mul
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have e : (d' + 1) * (a' + 1) = d' * a' + d' + a' + 1 := by ring
    omega

/-- **The list bound** `lbP Pl ≤ (bitlen B' + 9)·(4⌈√(64²B')⌉ + 257)` for `Pl.B ≤ B'`. -/
theorem lbP_le (Pl : FlatListParams) (B' : ℕ) (hB : Pl.B ≤ B') :
    lbP Pl ≤ (natBitLength B' + 9) * (4 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B') + 257) := by
  unfold lbP ListMachine.listBound
  simp only
  have hW : ∀ j ∈ Finset.range Pl.base.J, 4 * Pl.base.W j ≤
      4 * (64 + CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B')) := by
    intro j _
    unfold BaseListParams.W
    have h1 := ceilDiv_le_self (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) (2 ^ (j / 3))
      Nat.one_le_two_pow
    have h2 : CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) ≤
        CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B') := natCeilSqrt_mono (Nat.mul_le_mul_left _ hB)
    omega
  have hJ : Pl.base.J ≤ natBitLength B' + 9 := by
    show Nat.clog 2 Pl.B + 9 ≤ natBitLength B' + 9
    have : Nat.clog 2 Pl.B ≤ Nat.log 2 B' + 1 :=
      Nat.clog_le_of_le_pow (le_trans hB (Nat.lt_pow_succ_log_self (by norm_num) B').le)
    unfold natBitLength; omega
  have hs : ∑ j ∈ Finset.range Pl.base.J, 4 * Pl.base.W j ≤
      Pl.base.J * (4 * (64 + CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B'))) := by
    calc ∑ j ∈ Finset.range Pl.base.J, 4 * Pl.base.W j
        ≤ ∑ _j ∈ Finset.range Pl.base.J, 4 * (64 + CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B')) :=
          Finset.sum_le_sum hW
      _ = _ := by simp
  have hs2 := Nat.mul_le_mul_right (4 * (64 + CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B'))) hJ
  have e : (natBitLength B' + 9) * (4 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B') + 257) =
      (natBitLength B' + 9) * (4 * (64 + CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B'))) + (natBitLength B' + 9) := by
    ring
  omega

/-- **The POP rows' counting capacity fits `2^T`.** -/
theorem popY_le (Pl : FlatListParams) (B' Ls LD : ℕ) (hB : Pl.B ≤ B') (hL : Nat.clog 2 (8 * Ls + 2) ≤ LD) :
    (8 * Ls + 2) ^ (3 * lbP Pl + 1) ≤
      2 ^ ((((natBitLength B' + 9) * (2 * (2 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B')) + 257)) * 3 + 1) * LD) := by
  have h1 := lbP_le Pl B' hB
  have h2 : 8 * Ls + 2 ≤ 2 ^ Nat.clog 2 (8 * Ls + 2) := Nat.le_pow_clog (by norm_num) _
  calc (8 * Ls + 2) ^ (3 * lbP Pl + 1) ≤ (2 ^ Nat.clog 2 (8 * Ls + 2)) ^ (3 * lbP Pl + 1) := Nat.pow_le_pow_left h2 _
    _ = 2 ^ (Nat.clog 2 (8 * Ls + 2) * (3 * lbP Pl + 1)) := by rw [← pow_mul]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      have e : 2 * (2 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B')) =
          4 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B') := by ring
      rw [e]
      have h3 : 3 * lbP Pl + 1 ≤ (natBitLength B' + 9) * (4 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B') + 257) * 3 + 1 := by
        omega
      calc Nat.clog 2 (8 * Ls + 2) * (3 * lbP Pl + 1)
          ≤ LD * ((natBitLength B' + 9) * (4 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B') + 257) * 3 + 1) :=
            Nat.mul_le_mul hL h3
        _ = _ := by ring

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
