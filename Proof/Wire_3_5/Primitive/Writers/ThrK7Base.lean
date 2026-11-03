import Proof.Wire_3_5.Primitive.Writers.ThrEAt3
import Proof.Wire_3_5.Primitive.Writers.ThrCap3Base
import Proof.Wire_3_5.Primitive.Writers.CallSizeBase

/-! # PA2 c4 THR block, piece 7 part 1: the THR free numbers' contract, v7 (v6 + the strip's premises)

The THR twin of the `C4SymW.SymFreeOk6` (the v6 shapes, root's ruling to build ThrEAt/ThrFreeOk at them) with the
per-call strip field approved in #162: the THR stage's C3 sub-stage (`ThrStrip.thrC3`, M53) runs the strip
(`stripW_spec`) at the capacity `2·pr + 2` of the free program's `pr`, so its premises (`thr_hc3`'s `c1`–`c7`, `cw`,
with the code bound `Kb = kbT n`) are a field of the contract, discharged by the builder at `pr = d_P(n+1)^{e_P}`.
* `kbT` (the codes' bit bound at the gate's description degree 26), **`ThrStripAt`** (the strip's premises at one
  call), **`ThrFreeOk7`**, **`ThrFreeOkB7`** (the builder: for every `fe`, the load floor and the constants before `F`).

Paper quantities of the main types: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of the THR stage (P3:2929-2941,
3011-3016, 3094-3107) and the THR request word with the fixed hash's framed bits (P3:2238-2251). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- **The codes' bit bound** at the gate's description degree `26` (circuit codes and carrier codes). -/
noncomputable def kbT (n : ℕ) : ℕ :=
  CallSize.circBits (CallSize.codeParam 26 26 n) + CallSize.carrierBits (CallSize.codeParam 26 26 n)

/-- **The strip's premises at one THR call** (`thr_hc3`'s `c1`–`c7`, `cw` at `Kb = kbT n`), at the capacity
`2·pr + 2`, for the THR writer's input `req.word ++ hbF`. -/
def ThrStripAt (pr : ℕ) {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ) (hbF : List Bool) : Prop :=
  natBitLength n + 1 ≤ 2 * pr + 2 ∧
    2 ^ (natBitLength (ReqBridge.thrCodes Cs).length + 1) ≤ 2 * pr + 2 ∧
    2 ^ (natBitLength (carriers.map Carrier.code).length + 1) ≤ 2 * pr + 2 ∧
    kbT n + 1 ≤ 2 * pr + 2 ∧ (ReqBridge.thrCodes Cs).length ≤ 2 * pr + 2 ∧
    (carriers.map Carrier.code).length ≤ 2 * pr + 2 ∧
    8 * translation.length + 2 * (RepairRepresentation.natListWord translation).length + 16 ≤ 2 * pr + 2 ∧
    ((thrReq n a ha Cs carriers translation).word ++ hbF).length ≤ 2 * pr + 2

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
