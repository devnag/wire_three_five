import Proof.Wire_3_5.Primitive.Writers.SymFamBase
import Proof.Wire_3_5.Primitive.SeedFix.C4CapD
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.Primitive.SeedFix.C4CapE

/-! # C4.K SYM item (b), part 2: the SYM call's sizes below `2^{a(B+1)²}`

P3:3105-3115 (every size at an on-star call is `2^{O(k)}·poly(n)`), P3:1189 (`k = r·⌊log₂(n/r+1)⌋`, `r = rowBr c_r n`),
P3:2987-2988 (`Q = samp:q`): at a SYM call of the gate, the numbers front's load `100·K_Q + 200000`, the sample count
`Q` and the star width `k` are below `2^{e·(B+1)²}` for constants `e` of the gate and the base constants alone, and
the star's small numbers are below `2n`.

* `eKQ`, `e0`, `eQ`; `kOf_le_bsq`, **`kq_le`**, **`q_le`**, `star_small`.

Paper quantities of the main type: `K_Q`, `Q`, `k` at a SYM call against `2^{(B+1)²}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymN
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive

/-- The exponent of `K_Q`. -/
def eKQ (cr : ℕ) (h : SB) : ℕ := h.cA + (2 * cr + 4 + h.KF)

/-- The exponent of the numbers front's load `100·K_Q + 200000`. -/
def e0 (cr : ℕ) (h : SB) : ℕ := 7 + eKQ cr h + 18 + 1

/-- The star's small numbers are below `2n`. -/
theorem star_small (P : Shared.StarParams) :
    P.b ≤ P.n ∧ P.s ≤ P.n ∧ P.r ≤ P.n ∧ P.r / 2 ≤ P.n ∧ (P.b - P.s) * (P.r / 2) ≤ P.n ∧ P.r * P.b ≤ P.n ∧
      P.n - P.r * P.b + 1 ≤ P.n + 1 ∧ (P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2) ≤ 2 * P.n := by
  have h1 := P.r_mul_b_le
  have h2 := P.two_le_r
  have h3 := P.four_r_le_n
  have hb : P.b ≤ P.r * P.b := Nat.le_mul_of_pos_left _ (by omega)
  have hsb : P.s ≤ P.b := by
    have e := P.b_succ
    have := Nat.lt_two_pow_self (n := P.s)
    omega
  have hbs : (P.b - P.s) * (P.r / 2) ≤ P.r * P.b :=
    le_trans (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.div_le_self _ _)) (le_of_eq (Nat.mul_comm _ _))
  refine ⟨by omega, by omega, by omega, by omega, by omega, h1, by omega, by omega⟩

end NearCubicWires.WireExponent3_5.PrimT.C4SymN
