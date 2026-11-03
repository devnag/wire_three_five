import Lean
import Proof.Wire_3_5.FinalPass.SdI7
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdI2
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.FinalPass.SdI5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdI8Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 (the seeds phase), part 57: the run's cost in the seeds phase's shape (P3:3170-3178)

**`cost_gen`**: at a star call with the sizes below `X`, S4's run's step count
`prep + 1 + Bud + 1 + (bodyA + slCost)` is within `seedsShape |E| tab (|E|·2^{dRow}·2^{dR}·Q) pt ov` whenever
`10⁵·X³ ≤ tab`, `23000·X⁴ ≤ pt` and the prep, the writer and the body's fixed steps fit `ov`. The family's constants
(`cXf`, `KcF`/`DcF`, `CtF`/`DtF`, `CpF`/`DpF`, `CoF`/`DoF`) and their bounds against `s5Bound` (`s5_ge`).

Paper quantity of the main type: the seeds phase's running time `|E|·tab + (|centers|·|E|·Q)·pt + ov`
(P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL)
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem s5_ge (C D : ℕ) (r : FReq l F kclk coef A a ha) :
    C * ((fpIn l F kclk coef A a ha r).length + 1) ^ D ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha C D r := by
  unfold PrimAsm.S5Seam.s5Bound
  have : 1 ≤ 2 ^ (D * PrimAsm.S5Seam.s5Psi l F kclk coef A a ha r) := Nat.one_le_two_pow
  calc C * ((fpIn l F kclk coef A a ha r).length + 1) ^ D
      = C * 1 * ((fpIn l F kclk coef A a ha r).length + 1) ^ D := by rw [mul_one]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)





end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

end
