import Lean
import Proof.Wire_3_5.FinalPass.SdI1
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SdI2Base


noncomputable section
set_option maxRecDepth 4096


/-! # S4 (the seeds phase), part 51: the numbers' width, polynomial in `n` (P3:2994-3000, 3044-3048)

The printed numerator is at most `ptCount·vmax = |centers|·|E|·Q·vmax` (`fpNum_le`), and each factor is `2^{poly(n)}`:
`|centers| = 2^{n−k}`, `|E| ≤ (n+2)^{gapZ}`, `vmax ≤ 2(n+2)^{ZV}`, and the sample count
`Q ≤ 2^{⌊(6kh+3)/4⌋}·n^{13 + C + 2D} ≤ 2^{2n²+1+n(13+C+2D)}` (`Sampler.sampleCount_le` at the index bound
`callIndex_le_sym/thr`). **`ptv_lt`**: `ptCount·vmax < 2^{Tf r}` at the width `Tf r = KT·(n+2)^{ZT}` (the constants
from the literals and the gate only). S4's counters run at this width; the front's `W` may be it.

Paper quantity of the main type: the width of the printed numerator (`fpNum < 2^{Tf}`, P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Split

section Family
variable (l : Literals) (F : GateFree l)

/-- The per-point values' exponent (both modes). -/
noncomputable def ZV : ℕ := PrimAsm.CallIndex.flatZ l F + 14 * PrimAsm.CallIndex.algX l + 32

/-- The width's exponent. -/
noncomputable def ZT : ℕ := PrimAsm.CallIndex.gapZ l F + ZV l F + 2

/-- The sample count's exponent's coefficient, both modes. -/
noncomputable def C1m : ℕ := 13 + 2 * (PrimAsm.CallIndex.symZ l F + PrimAsm.CallIndex.thrZ l F) + 2 * (gate0 l F).D

/-- The width's coefficient. -/
noncomputable def KT : ℕ := C1m l F + 8

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Sd

end
