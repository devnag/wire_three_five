import Lean
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.FinalPass.DigsIface
import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins
import Proof.Wire_3_5.FinalPass.FiltTabBlock
import Proof.Wire_3_5.Primitive.SeedFix.C4GeoV
import Proof.Wire_3_5.FinalPass.ListEvalBridge
import Proof.Wire_3_5.FinalPass.MaskRef
import Proof.Wire_3_5.Primitive.Writers.DataTabs
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SeamsProgBase


noncomputable section
set_option maxRecDepth 4096


/-! # The final pass's program types: S2 (THR per point) and S4 (the seeds phase), with their words

Consumer backward from the seams (`PtEvalW`, `FrontOut`, `NumDenOut`, `FitsRes`): the front (S5) must leave
exactly the words the per-point evaluators and the seeds phase read. This module fixes them.

* **`PtEvalFix`**: a per-point evaluator with its call words and numbers FIXED in the type (`toW` forgets them).
* **S2**: `thrWords` (7 words: the tuple's gate table, as ThrData's `tabS`; the four payloads, as `DigsIn`'s `Pay`;
  the primes up to the cutoff, as W6's port 17; stage 4's table `levelWord` at `L = |occs|`), `thrNums` (`a`, `|𝒢|`,
  `τ₀`, `|occs|`), **`ThrPtProg`** `:= PtEvalFix ThrCall … rsumThr 7 4 thrWords thrNums`. `thrCallOf`: the THR call
  data at a request (`den = thrCallDen`, `D` the fixed hash's lists, so the reporter is `thrCallReportBits`).
* **S4's own words** (`s4Core`, 8 words): X3's offset word `frameP (ofFn offset) ++ [false]`; the sampled pairs
  (`sampWord`: per pair both indices framed in `s·(r/2)`-bit binary, then `false`: stage 0's input); the carriers'
  mask tables (as ThrData's `sCar k 3`); stage 6's `tauWord`, `modWord`; stage 7's threshold `1^{thr} 0`; the small
  numbers `1` (the star flag), `b, s, r/2, hL, n−rb−hL, n−rb, dRow, dR, |mask gates X₀|, |mask gates X₁|, seed
  width, |carriers|` as one unary list.
* **`frontWordsOf`**: per request, S4's 8 words, then the THR evaluator's 7 words and its numbers (unary list), then
  the SYM evaluator's words (`E3.words`) and its numbers; the other mode's slots and every slot off the star
  hypotheses are blank.
* **`SeedsProg`** (S4's type): one machine for the family; from every front exit meeting `FrontOut` at these words,
  `Num = 0`, `Den = denOf` in `W`-bit binary (`W` the front's choice with `ptCount·vmax < 2^W`), and S4's register tapes
  blank of length `Kc·(|fpIn|+1)^Dc + 1`, it reaches `NumDenOut` within `seedsShape`. `SeedsProg.phase` is
  `FpPhases.seeds`, `SeedsProg.numDen` its exit.

Paper quantities: the per-point sum `Σ_{g,p} R̂_{g,p}` (S2), the printed numerator and denominator (S4). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## A per-point evaluator with fixed words -/

/-! ## S2: the THR per-point evaluator's words -/

section Req

end Req

/-! ## S4's own words -/

section Req2

end Req2

/-! ## S4's program type -/

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (E3 : SymPtEval)

/-- The largest per-point value at a request of the family. -/
noncomputable abbrev vmax (r : FReq l F kclk coef A a ha) : ℕ :=
  vmaxOf (callInputs l F kclk coef A a ha) (gate0 l F).alg r.1

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams

end
