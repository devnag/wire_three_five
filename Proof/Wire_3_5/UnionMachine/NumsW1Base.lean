import Proof.Wire_3_5.UnionMachine.NumsA4Base

/-! # NW assembly, part 1: `V` is polynomial in the input, and the denominator split

P3:3044-3048 ("Fixed polynomially many states, filter seeds, row lookups, and requested means are absorbed by
`poly(n)`"), P3:3170-3181: phase (d) writes `max(2^e·V, 1)` in `T_f`-bit binary and needs `T + e + V + 2` below its
capacity, a polynomial in `X = |fpIn| + 1`. At every request of the family (every call is on-star):

* `V ≤ K_V·X^{D_V}`: SYM `V = |E|·|FlatSeed|·Q` (`gapSeed_leR`, `vsym_le`), THR `V = |PrimeIndex(cut)|·|E|·Q`
  (`cut_le`, `card_prime_le`), `Q ≤ |fpIn|` (the printed sample; `q_le_fpIn`, `q_le_fpIn_thr`);
* **`denSplit`**: `fpDen r = max (2^{eOf r}·vOf r) 1` (`|centers| = 2^{n−k}`, `card_centers`).

* `EV`, `DV`, `KV`, `q_le_fpIn_thr`, **`vOf_le`**, **`denSplit`**.

Paper quantities of the main type: `V`, the final pass's denominator `Den = 2^{n−k}·V` (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Gate
variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)


/-- The arithmetic of `V`'s bound. -/
theorem v_arith (n X g f q gK fK gz zv : ℕ) (hX : n + 1 ≤ X) (hg : g ≤ gK * (n + 2) ^ gz)
    (hf : f ≤ 2 * (fK + 1) * (n + 2) ^ zv) (hq : q ≤ X) :
    g * f * q ≤ 2 * gK * (fK + 1) * 2 ^ (zv + gz) * X ^ (zv + gz + 1) := by
  have hP : (n + 2) ^ gz * (n + 2) ^ zv ≤ 2 ^ (zv + gz) * X ^ (zv + gz) := by
    rw [← pow_add, add_comm gz zv, ← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  calc g * f * q ≤ (gK * (n + 2) ^ gz) * (2 * (fK + 1) * (n + 2) ^ zv) * X :=
        Nat.mul_le_mul (Nat.mul_le_mul hg hf) hq
    _ = 2 * gK * (fK + 1) * ((n + 2) ^ gz * (n + 2) ^ zv) * X := by ring
    _ ≤ 2 * gK * (fK + 1) * (2 ^ (zv + gz) * X ^ (zv + gz)) * X :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP)
    _ = 2 * gK * (fK + 1) * 2 ^ (zv + gz) * X ^ (zv + gz + 1) := by rw [pow_succ]; ring

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
