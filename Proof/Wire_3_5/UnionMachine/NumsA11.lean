import Lean
import Proof.Wire_3_5.UnionMachine.NumsA9Base
import Proof.Wire_3_5.UnionMachine.NumsA10
import Proof.Wire_3_5.UnionMachine.NumsC6Base
import Proof.Wire_3_5.UnionMachine.NumsPh3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.UnionMachine.NumsA4
import Proof.Wire_3_5.UnionMachine.NumsA11Base


noncomputable section
set_option maxRecDepth 4096


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
variable (l : Literals)

/-- The rewind bound's coefficient and degree: `3·10⁶(cap₀+2)³ ≤ K₁·X^{D₃}`. -/
noncomputable def K1a (F : GateFree l) : ℕ := 3000000 * (K0 l F + 2) ^ 3
noncomputable def D3a (fe : ℕ) : ℕ := 3 * D0 l fe

/-- The capacity's degree (a function of `fe`) and coefficient. -/
noncomputable def Dua (fe : ℕ) : ℕ := 3 * D0 l fe + FinalPass.Sd.R.ZTe l fe + 27
noncomputable def Kua (F : GateFree l) : ℕ :=
  2 * K0 l F + K1a l F + FinalPass.Sd.R.KT l F * 2 ^ FinalPass.Sd.R.ZT l F + 3 * D0 l F.filterErrDeg + 1000

/-- The steps' and residue's degree (a function of `fe`) and coefficient. -/
noncomputable def DsA (fe : ℕ) : ℕ := 3 * Dua l fe + 26 * Data.symDc
noncomputable def CsA (F : GateFree l) : ℕ := 10 ^ 12 + 200000 * Kua l F ^ 3 + Data.symCc * 82 ^ Data.symDc

end Consts

noncomputable def postW (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals) (F : GateFree l) : WM (LNS x) LNR :=
  .seq (unframeW (tOUT x hx) (sk x 113) (g 0) (g 1))
    (.seq ((numsP l F).liftW (fsN x) id) (finW x hx (K1a l F) (D3a l F.filterErrDeg)))

/-- **Phase (a)'s machine at a gate.** -/
noncomputable def aM (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals) (F : GateFree l) :=
  Composition.machine (Composition.machine (prepW x hx).toProg.compile (DataDock.dataDockM (nr := LNR) (tmapA x hx)))
    (postW x hx l F).toProg.compile

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
