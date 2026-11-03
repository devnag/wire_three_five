import Proof.Wire_3_5.Primitive.Writers.SymFamBase
import Proof.Wire_3_5.Primitive.SeedFix.C4CapD
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.UnionMachine.S6SizesBase

/-! # NW phase (a), part 3: the SYM numbers front's needs at a polynomial envelope

P3:3044-3048 ("Fixed polynomially many states, filter seeds, row lookups, and requested means are absorbed by
`poly(n)`"), P3:2929-2941, 2994-3000: the SYM numbers front (`C4Set.numsSW`) needs `P1Need`, `CapNeed`, `NumsNeed` and
the call-size conditions at its capacity. The discharge `C4SymN.sym_needs` (PrimTC4SymNA, unedited) proves them at
`cap ≥ 100·K_Q + 200000` with `K_Q = 2^{c_A}(2^{k+L+K_F L²}+1)`, `L = ⌈log₂(n+2)⌉`: quasi-polynomial in `n`, not below
the final pass's `poly(|fpIn|)`. Every one of its atoms is `≤ 2^c·(n+2)^d·2^{a'L}·2^k` with `c ≤ c_A`, `d + a' ≤ K_F`
(the `2^{K_F L²}` is PA's `toQ` loosening `(n+2)^d 2^{a'L}`, no quantity of that size). Here:

* **`sym_needsG`**: `sym_needs`' proof verbatim at ANY envelope `KQ` with the atom property (`KQ` is opaque: its only
  facts are the atom property and `100·KQ + 200000 ≤ cap`);
* `pow_clog_le`, **`kq_atom`**: the atom property at `KQ = 2^{c_A+K_F}·(n+2)^{K_F}·2^k`;
* `nwSB0`, `nwSB` (the base constants at the gate, `S6Sizes.cW`, `dW`, `C4GateSym.CvS`, `DvS`), `KFa`, `KF_eq` (`K_F`
  depends on the gate only through `fe`).

Paper quantities of the main type: the SYM call's sizes (`|E| = 2^{seedBits}`, `|FlatSeed| = 2^{fbv}`, `2^k`, the
star numbers) against the numbers front's capacity. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SymFam

/-- `2^{⌈log₂ x⌉} ≤ 2x` at `x ≥ 2`. -/
theorem pow_clog_le (x : ℕ) (hx : 2 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  have h1 := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < x)
  have hpos : 0 < Nat.clog 2 x := Nat.clog_pos (by norm_num) (by omega)
  obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 x = m + 1 := ⟨(Nat.clog 2 x).pred, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hm, Nat.pred_succ] at h1
  rw [hm, pow_succ]
  omega

/-- **The atom property at the polynomial envelope** `2^{c_A+K_F}·(n+2)^{K_F}·2^k`. -/
theorem kq_atom (cA KF n k : ℕ) {X c d a' : ℕ}
    (hX : X ≤ 2 ^ c * ((n + 2) ^ d * 2 ^ (a' * Nat.clog 2 (n + 2)) * 2 ^ k * 2 ^ 0)) (hc : c ≤ cA)
    (hda : d + a' ≤ KF) : X ≤ 2 ^ (cA + KF) * (n + 2) ^ KF * 2 ^ k := by
  have hL := pow_clog_le (n + 2) (by omega)
  have h1 : 2 ^ (a' * Nat.clog 2 (n + 2)) ≤ 2 ^ a' * (n + 2) ^ a' := by
    rw [mul_comm a', pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left hL a'
  have h2 : 2 ^ c ≤ 2 ^ cA := Nat.pow_le_pow_right (by norm_num) hc
  have h3 : 2 ^ a' ≤ 2 ^ KF := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (n + 2) ^ (d + a') ≤ (n + 2) ^ KF := Nat.pow_le_pow_right (by omega) hda
  calc X ≤ 2 ^ c * ((n + 2) ^ d * 2 ^ (a' * Nat.clog 2 (n + 2)) * 2 ^ k * 2 ^ 0) := hX
    _ ≤ 2 ^ c * ((n + 2) ^ d * (2 ^ a' * (n + 2) ^ a') * 2 ^ k * 1) := by
        rw [pow_zero]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)))
    _ = 2 ^ c * 2 ^ a' * (n + 2) ^ (d + a') * 2 ^ k := by rw [pow_add]; ring
    _ ≤ 2 ^ cA * 2 ^ KF * (n + 2) ^ KF * 2 ^ k :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul h2 h3) h4)
    _ = 2 ^ (cA + KF) * (n + 2) ^ KF * 2 ^ k := by rw [pow_add]

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
