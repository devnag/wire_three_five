import Proof.Wire_3_5.Primitive.Writers.ThrBud1

/-! # PA2 c4 THR block, piece 8 part 2: `thr_steps_gen` (the THR stage's `hBd`)

The THR twin of the `sym_steps_gen` (C4BudF): at every THR call where the numbers fit the capacity v2 (`ThrFitAt` at
`M = 2^{capExp2 C_c n}`, `thr_fits2`), the THR stage's steps (`thr_stage_of_big`'s `hBd`: the setup at the THR
input `req.word ++ hbF`, the data stage `S.cost3`, the hash bits, the numbers machine `thrBigCost`, the strip's C3
budget `thrB`, the loop over any child family whose cells fit the pad, the finisher) are within `c₄·seedClasses E₄`,
`c₄` after `F` (P3:3098-3100, 3105-3115).
* **`thr_ell_le`** (`ℓ ≤ 2(e_Q+1)·bsq n`, `Q ≤ 2^{2e_Q·bsq n}`, `k_h ≤ bsq n`), `w_le` (`|req.word ++ hbF|`, the translation's
  words and `kbT n` within the strip polynomial), **`thr_steps_gen`**.

Paper quantity of the main type: the THR stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrBud
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapCost)

section Gate
variable (l : Literals) 

/-- `a ≤ 460Q + 40020`, `Q ≤ cX`, `1 ≤ X` give `a ≤ (460c + 40020)X`. -/
theorem lin_le {a Q c X : ℕ} (h1 : a ≤ 460 * Q + 40020) (h2 : Q ≤ c * X) (hX : 1 ≤ X) : a ≤ (460 * c + 40020) * X := by
  have e : (460 * c + 40020) * X = 460 * (c * X) + 40020 * X := by ring
  omega

/-- **The strip's own steps** at values below `M`. -/
theorem y_le (cs pr wl h Q m M : ℕ) (h5 : pr + 1 ≤ M) (h3 : h + 1 ≤ M) (h2 : Q + 1 ≤ M) (h4 : m + 1 ≤ M)
    (hw : wl + 1 ≤ M) : ThrStrip.thrB 0 cs pr wl h Q m ≤ 28 * M + 2 * cs + 51 := by
  unfold ThrStrip.thrB bigCost
  omega

/-- The pad's exponent at rate `1` (`ρ + 1 ≤ M`). -/
theorem rho_le (Cc n r : ℕ) (h : r + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n)) : r ≤ 2 ^ Cc * 2 ^ (n / 8) := by
  have hM : (2 ^ PrimT.C4Cap.capExp2 Cc n) = 2 ^ Cc * 2 ^ (n / 8) := by unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  omega

/-- The strip's own steps at rate `1`. -/
theorem y_le' (cs pr wl h Q m Cc n KH : ℕ) (h5 : pr + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n)) (h3 : h + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n))
    (h2 : Q + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n)) (h4 : m + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n)) (hw : wl + 1 ≤ (2 ^ PrimT.C4Cap.capExp2 Cc n))
    (hcs : cs ≤ KH * 2 ^ (n / 8)) : ThrStrip.thrB 0 cs pr wl h Q m ≤ (28 * 2 ^ Cc + 2 * KH + 51) * 2 ^ (n / 8) := by
  have h1 := y_le cs pr wl h Q m _ h5 h3 h2 h4 hw
  have hM : (2 ^ PrimT.C4Cap.capExp2 Cc n) = 2 ^ Cc * 2 ^ (n / 8) := by unfold PrimT.C4Cap.capExp2; rw [pow_add, mul_comm]
  have hX : 1 ≤ 2 ^ (n / 8) := Nat.one_le_two_pow
  rw [hM] at h1
  have e : (28 * 2 ^ Cc + 2 * KH + 51) * 2 ^ (n / 8) = 28 * (2 ^ Cc * 2 ^ (n / 8)) + 2 * (KH * 2 ^ (n / 8)) +
      51 * 2 ^ (n / 8) := by ring
  omega

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrBud
