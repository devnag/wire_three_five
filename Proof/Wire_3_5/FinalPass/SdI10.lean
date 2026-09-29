import Proof.Wire_3_5.FinalPass.SdI9

/-! # S4 (the seeds phase), part 59: the run at a star call of the family (P3:3044-3048, 3170-3178)

**`sym_run`**, **`thr_run`**: at a SYM (THR) star call of the family, from S4's internal entry `SdEntry2` (the front's
words, `Num = 0`, `Den = fpDen` in `W`-bit binary, `ptCount·vmax < 2^W`), the family's machine `M4` steps within
`seedsShape |E| (s5Bound CtF DtF) ptCount (CpF·(n+1)^{DpF}) (s5Bound CoF DoF)` at the register capacity
`KcF·(|fpIn|+1)^{DcF}` to a state with the printed numerator `fpNum` on the numerator's stream, the denominator's
stream untouched, every head and register `0`. (`run_symG`/`run_thrG` at the counters' width `Tf`, the entry read by
part 50, the sizes by parts 52-53, the writer by part 54, the cost by parts 55-58.)

Paper quantity of the main type: the printed numerator `fpNum` (P3:3044-3048) within the seeds phase's time. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Split NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR)
open NearCubicWires.WireExponent3_5.PrimT.WalkBank (WalkBankProducer)
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup (FiltSetupSpec5)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2 SdEntry2 symCallOf thrCallOf thrWords thrNums)

section Family

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

