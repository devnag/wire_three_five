import Lean
import Proof.Wire_3_5.FinalPass.HashFree
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.HashFreeBase


noncomputable section
set_option maxRecDepth 4096


/-! # The HASH free numbers' contract, amended: `HashFreeOk2`

`filt:soft`, P3:2253-2290: the HASH child rebuilds its free-bit ruler `1^{2tℓ₀ − |p|}` from the kept pad `1^{c_C}`, which
needs `2·t·ℓ₀ ≤ c_C` at every THR call's HASH stage (`s_h = 2tℓ₀` decisions, P3:2238-2251; the Hb capacities are the
uniform `capsOf (Cap)`). The `HashFreeOk` is kept unchanged; `HashFreeOk2` adds this one field.

* **`HashFreeOk2`** (`HashFreeOk` + `caps_ge`).

Paper quantities of the main type: the HASH stage's free numbers and the seed length `s_h = 2tℓ₀` under the Hb
capacity. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **The free numbers of the HASH stage, with the ruler's capacity** (`2·t·ℓ₀ ≤ Cap` at every THR call). -/
structure HashFreeOk2 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ) :
    Type extends HashFreeOk l F wa K3 D3 Kp Dp where
  /-- **The ruler's capacity**: `s_h = 2·t·ℓ₀ ≤ c_C = Cap` at every THR call's HASH stage. -/
  caps_ge : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      2 * (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.t *
          (PrimT.C4H.hashDataOf (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers).MP.ell0 ≤
        Fp.val (hashX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 1

end NearCubicWires.WireExponent3_5.FinalPass.HashFr

end
