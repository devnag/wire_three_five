import Lean
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.EndpointBase
import Proof.Wire_3_5.Primitive.Writers.CallIndexBase
import Proof.Wire_3_5.Primitive.Writers.StarNums
import Proof.Wire_3_5.Primitive.Writers.UnaryArith
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Primitive.Writers.PlanBase


noncomputable section
set_option maxRecDepth 4096


/-! # The producer of leaf P's nested reduce (PA)

The reduce replaces the open leaf `∀ l, PrimitiveLeafF l` by the primitive leaf's enclosing application
(`Plan.leafP`) with the endpoint exponent filled (`Endpoint.endpointLeaf`) and three children:
`ComposeLeaf` (PA.compose), `SeedFixLeaf` (C4) and `FinalPassLeaf` (C5), each `∀ l`. This module exists so that the
producer's import closure contains `WireExponent3_5PrimAsmLibrary`, which ships PA's verified library as ancestor context
of the three children.

Paper quantity of the main type: `lem:primitive` at the gate (`Split.PrimitiveLeafF`, P3:3066-3116). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Reduce
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **The nested reduce's producer**: leaf P from its four residuals (`leafP`). -/
noncomputable def leafPR (g7 : ∀ l, EndpointLeaf l) (cmp : ∀ l, ComposeLeaf l) (s4 : ∀ l, SeedFixLeaf l)
    (s5 : ∀ l, FinalPassLeaf l) : ∀ l, PrimitiveLeafF l :=
  leafP g7 cmp s4 s5

end NearCubicWires.WireExponent3_5.PrimAsm.Reduce

end
