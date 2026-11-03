import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.FinalPass.SeamsUni
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base


noncomputable section
set_option maxRecDepth 4096


/-! # T: the THR per-call data stage, v4 — v3 with the W6 room (types only)

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (the THR call's numbers, computed once per call) and P3:3083-3086 (the
named carriers), P3:3425-3430 (the THR filter's cap `B_T`): v3 (`ThrDataStage3`) fixes its second machine's tapes
at `DS + 2 + DR + 1`, but W6's numbers machine (`numsW6 alg D : NumsPort4 alg D`) runs the request split on its own
layout and the decomposition algorithm's native machine on `4·(Ta alg − 1)` tapes (`|𝒢| = |Sel|` needs the algorithm's
children), `10176 + 4·(Ta alg − 1)` scratch tapes in all. v4 is v3 with `x3` extra scratch tapes after v3's tapes:

* **`ThrDataStage4 alg Dexp capT`**: `ThrDataStage2` plus `x3`, `M3 : Machine (DS + 2 + DR + 1 + x3) s3` (v3's tapes
  first, the extra tapes blank at the start, their final contents `J` bounded by `cost3`), and every other field of v3
  verbatim (`cost3`, `cost3_le`, `need`, `need_le`, `run3`'s hypotheses, the data word `hashNums ++ thrCounts`);
* **`ThrStage4U l`**: `ThrDataStage4` at the gate's call families, uniform constants (StageU order, as `ThrStage3U`).

Paper quantities of the main type: the data word `dataWord (hashNums … ++ thrCounts Cs carriers)` (`|carriers|`,
`capT`, the fourteen THR numbers, the slice lengths), its cost and W6's capacity need, both polynomial. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.Shared

open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan in
/-- **The v4 data stage at the gate's call families, uniform constants** (StageU order; `ThrStage3U` over v4). -/
abbrev ThrStage4U (l : Literals) : Type :=
  FinalPass.Seams.StageU l
    (fun F kclk coef A a ha => ThrDataStage4 (gate0 l F).alg (callInputs l F kclk coef A a ha).D
      (fun n => ((callInputs l F kclk coef A a ha).filterParams .thr n).cap))
    (fun S => max S.Dc3 S.Dn) (fun S => S.Cc3 + S.Kn)

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData

end
