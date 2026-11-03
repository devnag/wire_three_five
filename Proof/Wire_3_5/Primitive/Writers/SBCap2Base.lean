import Proof.Wire_3_5.Primitive.Writers.SBCap1

/-! # SB: the capacity target, part 2 — `sbNeed` polynomial in `|fpIn r| + 1`

* `ul_le` (the small-number word within `10^5·Z`), `sbNeed_Z` (every term of `sbNeed` against one majorant);
* `DD`, `KcF`, **`sbCap : StarRStmt l → SBCapStmt l`** (`sbNeed ≤ KcF l F·(N+1)^{DD l}` at every star request).

Donors: `CallIndexR.cap_leR`, `SymSizes.sparse_le_gate`/`TS4.spT_le`, `SymSizes.lambda_le`, `SymSizes.rowBt_le`,
`TS4.two_pow_le`, `FpInLen.n_le_fpIn`, the carriers' envelope.

Paper quantity of the main type: SB's capacity (`prim:runtime`, P3:3105-3115; "all powers of `n` are fixed before a
fixed `r`", P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.FinalPass.Out.Car NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

/-- The small-number word within `10^5·Z`. -/
theorem ul_le (P : Shared.StarParams) (CAP fe c0 c1 nc : ℕ) :
    (Data.unaryList (sbList P CAP (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length ≤
      10 ^ 5 * ((P.n + 1) ^ 26 + CAP + fe * (2 * P.n + 4) + P.n * P.n + c0 + c1 + nc + 10) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := atoms P fe CAP
  rw [SymDec.unaryList_length_le]
  simp only [sbList, swOf, lbOf, ellOf, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
  generalize (P.n + 1) ^ 26 = Y at a9 a10 ⊢
  generalize natBitLength (CAP * 32 - 1) = NB2 at a11 ⊢
  generalize natBitLength (Y * 2 - 1) = NB1 at a10 ⊢
  have hmx : max NB2 NB1 ≤ CAP * 32 + Y * 2 + 1 := by clear * - a10 a11; omega
  generalize max NB2 NB1 = MX at hmx ⊢
  generalize Nat.clog 2 (P.n + 2) = L at a8 a12 ⊢
  generalize fe * L = FL at a8 ⊢
  have hx : P.n - P.r * P.b ≤ P.n := Nat.sub_le _ _
  generalize P.n - P.r * P.b = XX at hx ⊢
  have d1 : (XX + 1) / 2 ≤ XX + 1 := Nat.div_le_self _ _
  have d2 : XX / 2 ≤ XX := Nat.div_le_self _ _
  have d5 : FL / 4 ≤ FL := Nat.div_le_self _ _
  have d7 : P.r / 2 ≤ P.r := Nat.div_le_self _ _
  generalize (XX + 1) / 2 = D1 at d1 ⊢
  generalize XX / 2 = D2 at d2 ⊢
  generalize FL / 4 = D5 at d5 ⊢
  generalize P.r / 2 = D7 at d7 a6 a7 ⊢
  clear * - a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 hmx hx d1 d2 d5 d7
  omega

theorem mbOf_le (m : Mode) : mbOf m ≤ 1 := by unfold mbOf; split <;> omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
