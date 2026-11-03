import Proof.Wire_3_5.Recovery.CaseTwoPadSource
import Proof.CaseAnalysis.CaseTwoSourceBlock

/-! # One padded source block (P3:3761-3763; D1.6, Case 2 of the hybrid)

Realizes the per-copy source step of the padded Case 2 ("each honest proof bit is computed by the deterministic PCPP
algorithm", P3:3762-3763), restating base's `CloseoutCaseTwo.SourceBlock` with the padded source of
`WireExponent3_5CaseTwoPadSource`: base's `CompoundInput` pairs the retained hierarchy and oracle frames, and the padded
source runs on the pair and on `1^q` (one extra input tape, `sold 8`), leaving the clause data and framed input of the
padded request and keeping the three retained frames.

Paper quantity: the padded request's PCPP output per block; **`smachine`** and **`sblock_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource

noncomputable section




end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock
