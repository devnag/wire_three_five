import Proof.Wire_3_5.FinalPass.SymBuildBase
import Proof.Wire_3_5.Primitive.Writers.ThrCap4Base
import Proof.Wire_3_5.Primitive.SeedFix.TabThrLayout

/-! # PA2 c4 THR block, piece 6 part 3: the THR rows' degree and words, and the enumeration's capacity

P3:2121-2157 (filt:majorant's windows `W_j = 16t + 20(⌊√(tB_*)⌋+1)/2^{⌊j/2⌋} + 20`), P3:3094-3107 (the THR degree
`d_T = C_D(√(B_T L) + L²)` in the load `Ψ_T = C_D²(k+L)²(√(B_T L) + L²)`), P3:3011-3016: at a THR call the rows'
factor degree `D_T = max(384·w_f + 1, 3·Σ_j(4W_j+1))` is at most `d_{DT}(⌊√(B_T L)⌋ + L²)` (`d_{DT}` fixed before `F`),
every row's word is below `2^{e_b}` (`thr_word_le`), and under the load floor `16·thrC1 ≤ C_D` (fixed before `F`)
and `12 d_T ≤ d_C` the capacity `2^{⌊n/16⌋ + d_C L²}` covers `capC·(qG+1)^6`: the enumeration's hypotheses hold at
every child prefix (the mode-generic `EnumCap.enumOk_of`). The twin of the SymDeg, SymCap1–3.

* `loadThr_le`, `sqrt_le_mul`, `sum_div_pow2_le`; `thrDg`, `dDT`, **`thrDg_lin`**; `eb`, **`thrBsz_le`**;
  `thrC1`, **`thrE_num`**.

Paper quantities of the main types: the THR degree `d_T`, the THR rows' words and the enumeration's group size. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (cK pow_N_le one_le_L n2_le_L pow_mono_mul sum_div_pow3_le)
open Finset

/-- **The THR load**: `C_D²(k+L)²(⌊√(B_T L)⌋ + L²) ≤ Ψ`. -/
theorem loadThr_le (CD k L BT BS : ℕ) :
    CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) ≤ loadPsi CD k L BT BS := by
  have h1 : loadThr CD k L BT ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_max_left _ _
  refine le_trans ?_ h1
  unfold loadThr sqrtUp
  have e : CD * CD * ((k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L)) =
      CD * ((k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2))) := by ring
  rw [e]
  apply Nat.mul_le_mul_left
  have : (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + L ^ 2)) ≤ (k + L) ^ 2 * (CD * (Nat.sqrt (BT * L) + 1 + L ^ 2)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  omega

/-- `⌊√y⌋ ≤ c(⌊√x⌋ + 1)` when `y ≤ c²x`. -/
theorem sqrt_le_mul {x y c : ℕ} (h : y ≤ c * c * x) : Nat.sqrt y ≤ c * (Nat.sqrt x + 1) := by
  have hx : x < (Nat.sqrt x + 1) * (Nat.sqrt x + 1) := Nat.lt_succ_sqrt x
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc; simp at h; subst h; simp
  have h2 : y < c * (Nat.sqrt x + 1) * (c * (Nat.sqrt x + 1)) := by
    have e : c * (Nat.sqrt x + 1) * (c * (Nat.sqrt x + 1)) = c * c * ((Nat.sqrt x + 1) * (Nat.sqrt x + 1)) := by ring
    rw [e]
    exact lt_of_le_of_lt h (Nat.mul_lt_mul_of_pos_left hx (Nat.mul_pos hc hc))
  exact Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (lt_of_lt_of_le h2 (by nlinarith)))

/-- `Σ_{j<J} ⌊C/2^{⌊j/2⌋}⌋ ≤ 6C`. -/
theorem sum_div_pow2_le (C J : ℕ) : ∑ j ∈ range J, C / 2 ^ (j / 2) ≤ 6 * C :=
  (sum_le_sum fun j _ => Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) Nat.one_le_two_pow).trans
    (sum_div_pow3_le C J)

section Gate
variable (l : Literals) 

/-- The THR rows' word exponent. -/
def eb (dig L D k : ℕ) : ℕ :=
  2 * dig * (26 * L + 3) + (2 * dig + 1) + (26 * L + 6) * D + D + (k + 26 * L + 6) + 4

/-- The row-word shape below `2^{e_b}` (pure arithmetic). -/
theorem thr_word_arith (M dig G D N2 k L : ℕ) (hM : M + 1 ≤ 2 ^ (26 * L + 3)) (hG : 4 * G + 1 ≤ 2 ^ (26 * L + 6))
    (hA : 4 * N2 * G + 1 ≤ 2 ^ (k + 26 * L + 6)) :
    ((M + 1) ^ 2) ^ dig * ((2 * dig + 1) * ((4 * G + 1) ^ D * (2 * D * (4 * N2 * G + 1) + 2) + 1 + 1) + 6 + 1) + 1 ≤
      2 ^ eb dig L D k := by
  have hT : ((M + 1) ^ 2) ^ dig ≤ 2 ^ (2 * dig * (26 * L + 3)) := by
    have h2 := pow_mono_mul 2 hM
    have h3 := pow_mono_mul dig h2
    exact h3.trans (le_of_eq (by ring_nf))
  have hw : 2 * dig + 1 ≤ 2 ^ (2 * dig + 1) := (Nat.lt_two_pow_self).le
  have hK := pow_mono_mul D hG
  have hD : D ≤ 2 ^ D := (Nat.lt_two_pow_self).le
  have key := FinalPass.EnumCap.wordB_le _ _ _ _ _ _ _ _ _ _ hT hw hK hD hA
  refine key.trans (le_of_eq ?_)
  unfold eb
  congr 1
  ring

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
