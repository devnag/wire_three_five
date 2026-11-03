import Lean
import Proof.Wire_3_5.FinalPass.SdI10
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdI1
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.FinalPass.SdI5
import Proof.Wire_3_5.FinalPass.SdI8
import Proof.Wire_3_5.FinalPass.SdI9
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdI10Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 (the seeds phase), part 60: the seeds phase at the machine level (`SeedsWS2`, P3:3044-3048, 3170-3178)

**`seedsWS2Of`**: S4's machine-level seam `SeedsWS2` (BridgeT's input at `frontWordsW2`) for every call family, from
the tables writer's producers (the walk bank `W5`, the FILTER setup `F5`), the SYM evaluator `E` and the two size
polynomials (`SymSizeOK`: #124; `ThrSizeOK`: `ThrSz.thrSize_poly`): the layout `gLay E twF`, the machine `M4`, the
register capacity `KcF·(|fpIn|+1)^{DcF}`, the costs `tab = s5Bound CtF DtF`, `pt = CpF·(n+1)^{DpF}`,
`ov = s5Bound CoF DoF`, and the run (`sym_run`, `thr_run`; the numerator's width from `fpNum_le`). The constants
depend on the literals, the gate, `W5`, `F5`, `E` and the size polynomials only, not on `kclk, coef, A, a`.

Paper quantity of the main type: the printed numerator and denominator (P3:3044-3048) within the seeds phase's time
`|E|·tab + (|centers|·|E|·Q)·pt + ov` (P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

end
