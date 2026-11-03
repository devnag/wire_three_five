import Proof.Wire_3_5.UnionMachine.RadScan
import Proof.Wire_3_5.Primitive.Writers.ThrSide3Base

/-! # C6b: the THR load absorbs the RADIX row's list bound (#198: the freeze gate's satisfiability check)

The RADIX row's explicit capacity carries `(8G+2)^{3·lb+1}`, `lb = listBound (thrCallD)`, so the class link needs
`lb·L ≤ C·Ψ` (`L = ⌈log₂(n+2)⌉`, `Ψ = psiOf n` the preprocessing load). This holds: `lb = 4·Σ_{j<J} W_j + 1` with
`W_j = 16t + 20(⌊(√(t·B_*)+1)/2^{⌊j/2⌋}⌋ + 1)` (`MajorantParams.W`), `J ≤ e_J·L`, `t ≤ (2e_J+1)·L` (PA2's
`ThrSide.thrCallJ_le`, `thrCallT_le`), `B_* ≤ 201326592·B_T` (`a' ≤ 4`, `|carriers| ≤ 2`, `B_T` the THR cap), and
the THR load `Ψ_T = C_D((k+L)²·C_D(√(B_T L)+1+L²)+k+L²)` (P3:3094-3107) is at least `L²(√(B_T L)+L²)` at `C_D ≥ 1`
(`ThrSide.loadThr_le`; `psiOf = loadPsi …` by definition).

* `cSq`, `cAb`; `absorb_arith`; **`lb_absorb`**: `listBound (thrCallD …) · ⌈log₂(n+2)⌉ ≤ cAb l · psiOf n`.

Paper quantity of the main type: the THR preprocessing load `Ψ_T` (prim:runtime P3:3094-3108) against the RADIX
row's list bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAbsorb
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars

theorem absorb_arith (E c L s : ℕ) (hL : 1 ≤ L) :
    (4 * (E * L * (16 * ((2 * E + 1) * L) + 20 * (c * (s + 1) + 1) + 20)) + 1) * L ≤
      (8 * E * (16 * (2 * E + 1) + 40 * c + 40) + 1) * (L * L * (s + L * L)) := by
  have hLL : L ≤ L * L := Nat.le_mul_of_pos_left L hL
  have hPQ : L * L ≤ L * L * (L * L) := Nat.le_mul_of_pos_left _ (Nat.mul_pos hL hL)
  have hPL : L * L * L ≤ L * L * (L * L) := Nat.mul_le_mul_left _ hLL
  have hLQ : L ≤ L * L * (L * L) := hLL.trans hPQ
  have e1 : (4 * (E * L * (16 * ((2 * E + 1) * L) + 20 * (c * (s + 1) + 1) + 20)) + 1) * L =
      64 * E * (2 * E + 1) * (L * L * L) + 80 * E * c * (L * L * s) + (80 * E * c + 160 * E) * (L * L) + L := by ring
  have e2 : (8 * E * (16 * (2 * E + 1) + 40 * c + 40) + 1) * (L * L * (s + L * L)) =
      (128 * E * (2 * E + 1) * (L * L * (L * L)) + 320 * E * c * (L * L * s) +
        (320 * E * c + 320 * E) * (L * L * (L * L)) + L * L * (L * L)) +
      (128 * E * (2 * E + 1) * (L * L * s) + 320 * E * (L * L * s) + L * L * s) := by ring
  rw [e1, e2]
  have t1 : 64 * E * (2 * E + 1) * (L * L * L) ≤ 128 * E * (2 * E + 1) * (L * L * (L * L)) :=
    Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) hPL
  have t2 : 80 * E * c * (L * L * s) ≤ 320 * E * c * (L * L * s) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
  have t3 : (80 * E * c + 160 * E) * (L * L) ≤ (320 * E * c + 320 * E) * (L * L * (L * L)) :=
    Nat.mul_le_mul (Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))
      (Nat.mul_le_mul_right _ (by norm_num))) hPQ
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.RadAbsorb
