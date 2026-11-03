import Proof.Wire_3_5.FinalPass.SymCap1
import Proof.Wire_3_5.FinalPass.SymOcc2
import Proof.Wire_3_5.FinalPass.SymSz1Base
import Proof.Wire_3_5.Primitive.Writers.BShape6
import Proof.Wire_3_5.Primitive.Writers.SymSizes
import Proof.Wire_3_5.UnionMachine.FiltPipeLe

/-! # The SYM enumeration's capacity, part 2: the SYM rows' words and the degree bound

P3:3011-3016 at a SYM call: every printed SYM row's word (`sym_word_le`, BShape6) is below
`2^{(26L+7)D + k + 80L + 24}` (`M ≤ 4(n+1)^{26}`, the walk `w ≤ L + 4`, `|pool| ≤ 8(n+1)^{26}`, `2k_h = k`), so the batch's
`bsz` is; and the degree bound `D = max(384·w_f + 1, 3·lbP)` of `sym_factor_count` is at most
`384(f_e L + 1) + 1 + 3(71 + 12k + ZL)(23296⌊√B_S⌋ + 23553)` (the filter walk `w_f ≤ f_e L + 1`; `lbP_le` at
`B' = 8192·B_S`, `B_S ≤ capK(c_r)(n+2)^Z`, `4c_r ≤ k`).

* `symDg`, `nb_le`, **`symBsz_le`**, **`symDg_le`**.

Paper quantities of the main types: the SYM batch's row words and the list bound `Σ_j W_j` (list:base P3:1376-1398). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

/-- A bit length below an exponent. -/
theorem nb_le (x m : ℕ) (h : x ≤ 2 ^ m) : natBitLength x ≤ m + 1 := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  rw [Nat.log_pow (by norm_num)] at this
  omega

/-- `(n+1)^{26} ≤ 2^{26L}`. -/
theorem n26_le (n : ℕ) : (n + 1) ^ 26 ≤ 2 ^ (26 * Nat.clog 2 (n + 2)) :=
  pow_mono_mul 26 (le_trans (by omega) (n2_le_L n))

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
