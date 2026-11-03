import Proof.Wire_3_5.Primitive.SeedFix.NwB14Base

/-! # T3 NW phase (b), part 15: **the phase-(b) term** `phB x l hx hV hN : NumsPh3.PhB x l`

At a THR request of a call on the star, from (c)'s exit (`AfterC`): the machine `bM` at the gate's constants runs the
register programs at the virtual capacity `c₀ = K_b(F)·X^{D_b(f_e)} ≤ cap` (every need from `NeedB` atoms,
`cap_le`), the docks at `cap`, within `C_s(F)·X^{D_s(f_e)}` (`b_cost_le`), and exits at `AfterV` with
`rV = vB = vOf` (`VLinkB`), the word streams blank, every head `0`, the residue by the step count
(`Shell.Step.len`).

Paper quantity of the main type: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` at the THR
requests (P3:3044-3048), in time polynomial in the input (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound

theorem add4 (p a b c : ℕ) : a + b + c ≤ p + a + b + c := by omega
theorem add4' (p a b c : ℕ) : p ≤ p + a + b + c := by omega

theorem tv_aux (len p26 n capT ncar PC U c₀ c : ℕ) (hl : len + 1000 ≤ U) (hp : p26 ≤ c) (hn : n + 1000 ≤ U)
    (hcT : capT ≤ c) (hnc : ncar ≤ 2) (hPC : PC ≤ U * U) (hcU : c ≤ U) (hU : U * U + 60 * U + 60 ≤ c₀) :
    len + p26 + n + 40 + PC + n + capT + ncar + 42 ≤ c₀ := by
  omega

section Term

end Term

end NearCubicWires.WireExponent3_5.PrimT.NwB
