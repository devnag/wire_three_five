import Proof.Wire_3_5.Recovery.CaseTwoPadBlock
import Proof.CaseAnalysis.CaseTwoWholeBlockReset

/-! # One whole padded block: source and occurrence (P3:3761-3763; D1.6, Case 2 of the hybrid)

Realizes one copy's honest proof bit of the padded Case 2 ("each honest proof bit is computed by the deterministic
PCPP algorithm", P3:3762-3763), restating base's `CloseoutCaseTwo.WholeBlock` on the padded source block
(`WireExponent3_5CaseTwoPadBlock`): base's `Occurrence` machine, generic in the request, reads the padded request's
clause cache, its framed input and the retained address, and writes the unsigned honest assignment bit of the padded
request at the addressed block; a paid rewind (`wresetMachine`) restores all heads.

Paper quantity: one honest proof bit of the padded request; **`wmachine`** / **`wblock_run`** and
**`wresetMachine`** / **`wreset_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock

noncomputable section

/-! ## The padded source block's interface -/


/-! ## The whole block's layout -/




/-! ## With a paid head reset -/


end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole
