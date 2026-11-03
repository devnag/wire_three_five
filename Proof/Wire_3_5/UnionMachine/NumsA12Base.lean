import Proof.Wire_3_5.UnionMachine.NumsA11Base

/-! # NW phase (a), part 12: the run at a SYM request and `phA3 x hx l : NumsPh3.PhA x l`

Composition of `width_run`, `tapes_run` (the word program `prepW`), `dockPost` (the docked data stage), and
`dockPost`'s unframe, `numsBank`, `fin_run` (the word program `postW`), from (c)'s exit `AfterC` to `AfterV` with
`V = vOf r` in `rV`, within `C_s·X^{D_s}` steps at every capacity `≥ K_n·X^{D_n}` (`X = |fpIn|+1`).

* `sumle`, `mfle`, **`aRun`**, **`phA3`**.

Paper quantity of the main type: `V = |E|·|FlatSeed|·Q` at the SYM requests (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g g_ne npow_le)

theorem sumle (U K0 K1 KTZ D0 n W e T : ℕ) (hU : 1 ≤ U) (hn : n ≤ U) (hW : W ≤ 27 * U) (he : e ≤ U)
    (hT : T ≤ KTZ * U) : 3 * W + n + e + T + 2 ≤ (2 * K0 + K1 + KTZ + 3 * D0 + 1000) * U := by
  have e1 : (2 * K0 + K1 + KTZ + 3 * D0 + 1000) * U = 2 * (K0 * U) + K1 * U + KTZ * U + 3 * (D0 * U) + 1000 * U := by
    ring
  rw [e1]; omega

theorem mfle (U K0 K1 KTZ D0 D3 cap₀ V Bh n e T F : ℕ) (hU : 1 ≤ U) (h0 : cap₀ ≤ K0 * U) (hV : V ≤ K0 * U)
    (hB : Bh ≤ K1 * U) (hT : T ≤ KTZ * U) (hn : n ≤ U) (he : e ≤ U) (hF : F ≤ U) (hD3 : D3 ≤ 3 * D0) :
    cap₀ + V + Bh + n + e + T + F + K1 + D3 + 2 ≤ 3 * ((2 * K0 + K1 + KTZ + 3 * D0 + 1000) * U) := by
  have e1 : (2 * K0 + K1 + KTZ + 3 * D0 + 1000) * U = 2 * (K0 * U) + K1 * U + KTZ * U + 3 * (D0 * U) + 1000 * U := by
    ring
  rw [e1]
  have a1 : K1 ≤ K1 * U := Nat.le_mul_of_pos_right _ hU
  have a2 : D0 ≤ D0 * U := Nat.le_mul_of_pos_right _ hU
  omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
