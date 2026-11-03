import Proof.Wire_3_5.UnionMachine.FrontOutRefBase
import Proof.Wire_3_5.UnionMachine.FrontTWBridge5
import Proof.Wire_3_5.Transfer.TransferUnionCompleteBase

/-! # C6 front, the callOk bridge: a call's admissibility is its circuits' and carriers' envelope bits

The table writer conjoins, per emitted call, the envelope bits of its four circuits and its named carriers
(`FrontTW.okT fD fE`); its semantics (`FrontTW.twSem`) takes `hokV`/`hokM`: for every tuple of the factors'
supports, `callOkI` (`[I.Call r]`) is that conjunction. Past the onset (`I.StarAt q`, `B.FitsAt q`, two names)
the other conjuncts of `PrimitiveInputs.Call` hold (P3:3083-3094: every tuple's gates lie in the named carriers, the
translation is well formed): **`callOk_V`**, **`callOk_Mu`** at `fD C = [descriptionBits C ≤ (q+1)^descDeg]`,
`fE X = [X.WithinEnvelope carrierDeg]`.

Paper quantity: the per-call hypothesis `PrimitiveInputs.Call` (P3:3083-3094). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCallOk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 {z : BitInput N}

/-- The circuits' envelope bit. -/
noncomputable def fDI (m : Mode) (q : ℕ) (C : m.Circuit q) : Bool := decide (m.descriptionBits C ≤ (q + 1) ^ I.descDeg)
open Classical in
/-- The carriers' envelope bit. -/
noncomputable def fEI {q : ℕ} (X : Stars.Carrier q) : Bool := decide (X.WithinEnvelope I.carrierDeg)

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCallOk
