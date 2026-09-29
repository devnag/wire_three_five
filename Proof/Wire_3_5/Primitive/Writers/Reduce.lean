import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.Primitive.Writers.StarNums

/-! # The producer of leaf P's nested reduce (PA)

The reduce replaces the open leaf `∀ l, PrimitiveLeafF l` by leaf P's enclosing application (`Plan.leafP`; checked c82bb7…) with the endpoint exponent filled (`Endpoint.endpointLeaf`) and three children:
`ComposeLeaf` (PA.compose), `SeedFixLeaf` (C4) and `FinalPassLeaf` (C5), each `∀ l`. This module exists so that the
producer's import closure contains `Proof.Wire_3_5.Primitive.Writers.Library`, which ships PA's verified library as ancestor context
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
