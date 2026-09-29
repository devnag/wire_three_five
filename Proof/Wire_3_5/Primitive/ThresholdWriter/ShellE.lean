import Proof.Wire_3_5.Primitive.ThresholdWriter.Shell2
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface2

/-! # THR: the THR shell types with the empty tuple (`a' = 0`) included

P3:3068 (lem:primitive): "Fix a polynomial description envelope, a tuple arity at most four, and an accuracy exponent
`D>0`." Arity at most four includes the empty tuple: `PrimitiveInputs.Call` has no lower bound on `a`, and both THR
writer targets (`ThrWriterAtJ`, `HashWriterAtJ`) quantify over `a' ≤ 4`. At `a' = 0` the tuple has no gates
(`tupleG Cs = []`), the THR pool is the carriers' mask gates, and `thrCounts` ends in `0`; the THR entries still exist
(one empty selection, every prime row, empty digit populations). v1's `ThrDataOK` (hence `ThrShellRun`, `ThrShellX2`)
carries `ha1 : 1 ≤ a'` and runs over `ThrDataStage` (which needs `1 ≤ a'`). This file restates them over PA's
`ThrDataStage2`, which has no lower bound:

* **`toV1 S`**: a `ThrDataStage2` is a `ThrDataStage` (same machine, table stream and cost; at `1 ≤ a'` its table is
  `gatesW …`), so the v1 machines (`Shell.shellMT`) are reused unchanged;
* **`ThrDataOK2`**: `ThrDataOK` without `ha1`; `ok2_of_ok`, `ThrDataOK2.toOK`;
* **`ThrShellRun2 S x U …`**: v1's run TYPE for every `a' ≤ 4`, over `S : ThrDataStage2`; `ThrShellRun2.toV1`;
* **`ThrShellX2b S x U … KL`**: `ThrShellX2` for every `a' ≤ 4`, over `S : ThrDataStage2`; `ThrShellX2b.toX2`,
  `ThrShellX2b.stage`.

Paper quantities of the main types: the THR request word, the call's slice lengths `ThrData.thrCounts` (ending in `0`
at the empty tuple), and the writer's output tape `(List.range b).flatMap emit ++ [false]`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.ShellE
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.CellLoop
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimThrW.Shell
open NearCubicWires.WireExponent3_5.PrimThrW.Shell2

/-- **A v2 data stage is a v1 data stage** (same machine, table stream and cost; at `1 ≤ a'` the v2 table is
`gatesW (tabH (tupleG Cs)) (tupleG Cs)`). -/
def toV1 (S : ThrData.ThrDataStage2) : ThrData.ThrDataStage where
  s := S.s
  M := S.M
  tabS := S.tabS
  cost := S.cost
  Cc := S.Cc
  Dc := S.Dc
  cost_le := fun Cs carriers L W K _ ha hk hL hX hK hK2 h2 => S.cost_le Cs carriers L W K ha hk hL hX hK hK2 h2
  run := fun Cs carriers tl L W ha1 ha hk hL hX h2 hN hA hK hx hy hu => by
    obtain ⟨tout, m, hs, h1, h2', h3, h4, h5⟩ := S.run Cs carriers tl L W ha hk hL hX h2 hN hA hK hx hy hu
    refine ⟨tout, m, hs, h1, h2', ?_, h4, h5⟩
    rw [h3, if_neg (by omega)]

/-- **The THR data stage's size hypotheses at width `V`, every `a' ≤ 4`** (`ThrDataOK` without `ha1`). -/
structure ThrDataOK2 {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (V : ℕ) : Prop where
  ha : a' ≤ 4
  hk : carriers.length ≤ 2
  hL : ∀ i, (Cs i).descriptionBits ≤ V
  hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ V
  h2 : 2 ≤ n + V
  hcN : natBitLength n + 1 ≤ 2 * V + 2
  hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2
  hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * V + 2
  hcx : ∀ y ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2
  hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2
  hcu : 2 * (Data.unaryList (ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * V + 2

end NearCubicWires.WireExponent3_5.PrimThrW.ShellE
