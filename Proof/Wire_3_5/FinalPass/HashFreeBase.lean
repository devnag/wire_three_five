import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB4
import Proof.Wire_3_5.Primitive.Writers.ThrFam2

/-! # The HASH free numbers' contract (#160/#161, the draft for the review): `HashFreeOk`

`filt:soft`, P3:2221-2336 at a THR call's HASH stage, with the free numbers of the SYM precedent (C4SymKB7): C1b's
free program `Fp` on the HASH input `hashX` (THR's `thrX` with the moment count `t` in the arity slot, so that
`m = 1 + 2t` is a free number: every printed term has `1 + 2t` factors, `hashTermsM_uniform`), the degree bound `dF`
(no machine reads it), the Hb printer's uniform capacities `capsOf (Cap)` (every `HbCaps` field the capacity slot's
value), the Hb cell bound `Kc` and the child bound `Kch`, the pad and the C3 load at constants fixed before `F`, and
`C4H.HashEAt` at every THR call at the call's compiler request `thrR0 … h Q' 0 m d pr 0` (PA2's, the THR pool),
the call's data `hashDataOf` and the seed length `s_h = 2t·ℓ₀`.

* `hashX`, `capsOf`, **`HashFreeOk`**.

Paper quantities of the main type: the HASH stage's free numbers `Q', h, m, pr, ρ`, the Hb capacities and bounds. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- **The HASH input**: THR's `thrX` with the moment count `t` in the arity slot. -/
noncomputable def hashX {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
    (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (hs : I.StarAt n) : FreeIn :=
  { ThrFam.thrX I alg Cs carriers hs with a := thrCallT alg I hs Cs carriers }

/-- The Hb printer's uniform capacities. -/
def capsOf (v : ℕ) : PrimT.C4H.HbCaps := ⟨v, v, v, v, v, v, v, v, v, v, v, v⟩

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
