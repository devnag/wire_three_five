import Proof.Wire_3_5.Recovery.CaseTwoFoldRun
import Proof.Wire_3_5.Recovery.CaseTwoParamScan
import Proof.Wire_3_5.Recovery.CaseTwoParamWidth
import Proof.CaseAnalysis.CaseTwoPreparedFrames
import Proof.CaseAnalysis.Capacity
import Proof.Amplification.RecoveryCaseOneBooleanOutput
import Proof.MachineModel.UWalkArithmetic

/-! # The hybrid Case-2 execution (P3:3729-3733, 3758-3763; D1.6 A3c)

Realizes the Case-2 half of "The resulting slice is computable in `E^NP` [...] In the yes case, prefix self-reduction
recovers the first eligible description, after which each honest proof bit is computed by the deterministic PCPP
algorithm" (P3:3758-3763) for the hybrid slice, with the growing XOR schedule (P3:3729-3733, 3818-3822): from the five
cold words of base's Case-2 dispatch (the hierarchy word, the recovered oracle description, the framed address `x`,
`1^R`, `1^B`) one fixed machine
1. prepares the frames (base `CloseoutCaseTwo.PreparedFrames`: the oracle's descriptor from its canonical description);
2. recomputes the slice parameters from `x` (A3a: the index `S`, the schedule `t`; A3b: `1^{q(2^S)}` and the block
   width `1^w`, `w = q + 1 + ⌈D log₂(q+2)⌉`), the copy count `t + 1` as a counter word (base `DimensionTemplate`), and the
   bank capacity `1^{C}` (base `CloseoutCapacity`);
3. initializes the fold's bank (the width `1^q`, base `RecoveryScratchErase` on the scratch, the offset and the width,
   the width `1^w` (base `PCPUnaryCopy`), the accumulator `[false]`);
4. runs A2's uniform fold over `t + 1` blocks of `x`;
5. frames the accumulator bit (base `RecoveryCaseOneBooleanOutput`).

This module fixes the machine's tape layout (`G` tapes: the frames' 140, then the blocks of each stage). -/

set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Transfer.CertPrefixPrep NearCubicWires.WireExponent3_5.Transfer.CertPrefixBounds
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
open NearCubicWires.RepairSource.ProjectionNormalization (HierarchySourceInput.hierarchyInput)
open NearCubicWires.RecoveryPipeline (padCore)

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm) (k D : ℕ)

/-! ## The layout -/



/-! ## The stages' slots -/

/-- Close a value goal of the layout (needs the layout facts in context). -/
macro "ex_tac" : tactic => `(tactic| (first | omega | (simp only [Fin.val_mk] at * <;> omega)))


/-! ## Injectivity -/


/-! ## The machine -/

section Machine

end Machine

/-! ## The preparation -/

section Pre

end Pre

/-! ## The fold's bank initialization -/

section Init

end Init

/-! ## The fold and the framed bit -/

section Post

end Post

/-! ## The whole execution -/

section Whole

end Whole

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoExec
