import Proof.Wire_3_5.UnionMachine.NumsA9Base
import Proof.Wire_3_5.UnionMachine.NumsA10
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base

/-! # NW phase (a) over the interface v3: `phA3 x hx l : NumsPh3.PhA x l`

P3:3044-3048, 3170-3181: at a SYM request, from (c)'s exit (`AfterC`: the roles, every stream but `sIn` blank):

1. `prepW` (a word program): the data stage's width `W = 3|fpIn| + 8(n+1)^{26} + 16` (`width_run`), its unary inputs
   and the role stash (`tapes_run`);
2. PA's data stage, docked (`dockPost`): the gate tables and the counts;
3. `postW` (a word program): the counts onto stream `113` (`unframeW`), the SYM numbers program on NW's bank
   (`numsBank`, at `cap₀ = K₀·X^{D₀}`, `X = |fpIn|+1`), the finish (`fin_run`: `rV := V`, the roles back, stream
   `113`'s head rewound by `K₁·X^{D₃} ≥ 3·10⁶(cap₀+2)³`).

The machine is `Composition.machine (Composition.machine prep dock) post`; capacity `K_n·X^{D_n}`, steps and residue
`C_s·X^{D_s}`, the exponents functions of `fe` alone.

* `K1a`, `D3a`, `Dua`, `Kua`, `DsA`, `CsA`, `capA`, `costA`, `prepW`, `postW`, `stOf`, `aM`, **`aRun`**, **`phA3`**.

Paper quantity of the main type: `V = |E|·|FlatSeed|·Q` at the SYM requests (the denominator's unshifted value). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g g_ne npow_le)

section Consts




end Consts

/-- The capacity's five needs. -/
theorem capA (U K0 K1 KTZ D0 cap₀ V Bh T W n e F cap : ℕ)
    (h0 : cap₀ ≤ K0 * U) (hV : V ≤ K0 * U) (hB : Bh ≤ K1 * U) (hT : T ≤ KTZ * U) (hW : W ≤ 27 * U) (hn : n ≤ U)
    (he : e ≤ U) (hF : F ≤ U) (hU : 1 ≤ U) (hcap : (2 * K0 + K1 + KTZ + 3 * D0 + 1000) * U ≤ cap) :
    W + 2 * F + n + 2 ≤ cap ∧ n + W + e + T ≤ cap ∧ 2 * W + 2 ≤ cap ∧ cap₀ ≤ cap ∧
      cap₀ + V + Bh + n + e + T + 2 * F + 2 ≤ cap := by
  have e1 : (2 * K0 + K1 + KTZ + 3 * D0 + 1000) * U = 2 * (K0 * U) + K1 * U + KTZ * U + 3 * (D0 * U) + 1000 * U := by
    ring
  rw [e1] at hcap
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The steps. -/
theorem costA (U XDs Z Ku S cw ct fd cu cn cf KuU K1U KuP : ℕ) (hU : 1 ≤ U) (hUX : U ≤ XDs)
    (hcw : cw ≤ 4000 * 2 ^ 27 * U) (hct : ct ≤ 100 * KuU) (hfd : fd ≤ S * Z) (hcu : cu ≤ 1100 * U) (hcn : cn ≤ K1U)
    (hcf : cf ≤ 5000 * (27 * KuP)) (hKuU : KuU ≤ KuP) (hK1U : K1U ≤ KuP) (hZ : S * Z ≤ S * XDs)
    (hKuP : KuP ≤ Ku ^ 3 * XDs) :
    cw + 1 + ct + 1 + fd + 1 + (cu + 1 + (cn + 1 + cf)) ≤ (10 ^ 12 + 200000 * Ku ^ 3 + S) * XDs := by
  have e1 : (10 ^ 12 + 200000 * Ku ^ 3 + S) * XDs = 10 ^ 12 * XDs + 200000 * (Ku ^ 3 * XDs) + S * XDs := by ring
  rw [e1]
  have e2 : 4000 * 2 ^ 27 * U = 536870912000 * U := by norm_num
  rw [e2] at hcw
  linarith

/-- The word programs around the data stage. -/
def prepW (x : ℕ) (hx : DataDock.DT + 3 ≤ x) : WM (LNS x) LNR := .seq (widthW x) (tapesW x hx)

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
