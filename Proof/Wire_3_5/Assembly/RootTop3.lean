import Lean
import Proof.Wire_3_5.Foundations.Skeleton
import Proof.Wire_3_5.Assembly.Ok
import Proof.Wire_3_5.Assembly.FreeRecoveryOk
import Proof.Wire_3_5.Recovery.HybridProgCertificate
import Proof.Wire_3_5.UnionMachine.PlanW4
import Proof.Wire_3_5.UnionMachine.PreProof
import Proof.Wire_3_5.Selection.Plan
import Proof.Wire_3_5.Selection.CosFill
import Proof.Wire_3_5.Primitive.Writers.Reduce
import Proof.Wire_3_5.Primitive.Writers.Endpoint
import Proof.Wire_3_5.Primitive.Writers.Compose
import Proof.Wire_3_5.Primitive.Writers.ComposeGlue
import Proof.Wire_3_5.Primitive.Writers.ComposeEnv
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTop2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.UnionMachine.PlanW3
import Proof.Amplification.RecoveryCaseOnePaddedBitInput
import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual
import Proof.CaseAnalysis.CaseOneHeaderLive
import Proof.CaseAnalysis.CaseTwoDirect
import Proof.CaseAnalysis.CaseTwoDirectInput
import Proof.CaseAnalysis.CaseTwoSelectedDescription
import Proof.CaseAnalysis.CommonPortBankAt
import Proof.CaseAnalysis.CommonPrefixFields
import Proof.CaseAnalysis.CommonPrefixProgram
import Proof.CaseAnalysis.CommonPrefixSelected
import Proof.CaseAnalysis.CommonPrepareBudget
import Proof.CaseAnalysis.CommonQueryBudget
import Proof.CaseAnalysis.NativeWidthStep
import Proof.CaseAnalysis.RecoveryCapacitySource
import Proof.CaseAnalysis.RecoveryMeaning
import Proof.CaseAnalysis.RecoverySharedInput
import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.Hierarchy.HierarchyFixedWord
import Proof.MachineModel.OrdinaryOracleComposeInitial
import Proof.MachineModel.OrdinaryOracleComposeReadyAt
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Foundations.SkeletonBase
import Proof.Wire_3_5.Recovery.CaseTwoCost
import Proof.Wire_3_5.Recovery.CertRefuter
import Proof.Wire_3_5.Recovery.HybridAssembly
import Proof.Wire_3_5.Primitive.Writers.CallIndexBase
import Proof.Wire_3_5.Primitive.Writers.ComposeBase
import Proof.Wire_3_5.Primitive.Writers.ComposeEnvBase
import Proof.Wire_3_5.Primitive.Writers.EndpointBase
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.PreLinkBase
import Proof.Wire_3_5.Primitive.Writers.StarNums
import Proof.Wire_3_5.Primitive.Writers.UnaryArith
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTopBase
import Proof.Wire_3_5.Recovery.RecoveryEventualBase
import Proof.Wire_3_5.Recovery.RecoveryFamily
import Proof.Wire_3_5.Recovery.RecoveryLeaf
import Proof.Wire_3_5.Assembly.FreeBase
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.Transfer.TransferUnionCompleteBase
import Proof.Wire_3_5.UnionMachine.UnionCallCountBase
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.Decision
import Proof.Wire_3_5.UnionMachine.PlanW2Base
import Proof.Wire_3_5.UnionMachine.PreProofBase
import Proof.Wire_3_5.UnionMachine.SetupFactsBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule


noncomputable section
set_option maxRecDepth 120000


/-!
# The top-level producer with the atom test

"The weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid sum for each distinct PCPP
variable. It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid"
(P3:3669-3671). Case 2 uses completeness only at the guess it constructs from the bounded sums of `tr:xor`
(P3:3711-3716), whose atoms pass that test (`Transfer.exists_unionAccepts_ok`).

`rowB_root3` is the accepted proof of `Literals → rowB` with the split of `Split.lean` replaced by `SplitOk.lean`
(union completeness at atom-OK accepting guesses). Every other piece is the accepted application, by name:
* the root chain `literals_rowB_of_parts` over the parts split (`Split.literals_parts_of_leavesF2`);
* leaf P: `PrimAsm.Reduce.leafPR` with the endpoint leaf, `Compose.composeLeaf glue envPack`, the seed-fix reduce
  `SeedFixTop2.seedFixLeaf_of2` over the writers join `WritersJoin.writerLeafJ2_of` at `PreProof.preLink`;
* leaf U: `PlanW4.union_planW4` at C1 = `SelectionMachine.Plan.c1Impl_of` with the `Cos` fills;
* leaf R: `Split.recoveryLeafF2_of_certGen` at `HybridProgram.certGen`.
Its six arguments are the open leaves: the SYM, THR and hash writers, C4, the final pass, and the fronts at
`PlanW3.FrontsFWE3`.

Paper quantity of the main type: `rowB` (the tradeoff theorem at row B).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SplitRootTop3

open NearCubicWires.WireExponent3_5

/-- **The root producer with the atom test**: row B from the six open leaves. -/
theorem rowB_root3
    (sym : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.SymLeafJ2 l)
    (thr : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.ThrLeafJ2 l)
    (hash : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l → PrimAsm.WritersJoin.HashLeafJ2 l)
    (c4 : ∀ l : Literals, PrimT.SeedFixTypes.C4Leaf l)
    (s5 : ∀ l : Literals, PrimAsm.Plan.FinalPassLeaf l)
    (fronts : ∀ l : Literals, Σ e : ℕ, ∀ F : Split.GateFree l, Split.GateFreeOK l F →
      UnionMachine.PlanW3.FrontsFWE3 e l F) :
    Literals → rowB :=
  let pre : ∀ l : Literals, PrimAsm.PreLink.PreLinkT l := fun l => UnionMachine.PreProof.preLink l
  let w : ∀ l : Literals, PrimAsm.PreLink.WriterLeafJ2 l := fun l =>
    PrimAsm.WritersJoin.writerLeafJ2_of l (sym l (pre l)) (thr l (pre l)) (hash l (pre l))
  let s4 : ∀ l : Literals, PrimAsm.Plan.SeedFixLeaf l := fun l => PrimT.SeedFixTop2.seedFixLeaf_of2 l (w l) (c4 l)
  let cmp : ∀ l : Literals, PrimAsm.Plan.ComposeLeaf l :=
    PrimAsm.Compose.composeLeaf PrimAsm.ComposeGlue.glue PrimAsm.ComposeEnv.envPack
  let p : ∀ l : Literals, Split.PrimitiveLeafF l :=
    PrimAsm.Reduce.leafPR (fun l => PrimAsm.Endpoint.endpointLeaf l) cmp s4 s5
  let c1 : UnionMachine.Plan.C1Impl :=
    SelectionMachine.Plan.c1Impl_of SelectionMachine.Cos.selM SelectionMachine.Cos.selHt SelectionMachine.Cos.selO
      SelectionMachine.Cos.selHo SelectionMachine.Cos.selCost SelectionMachine.Cos.selRunF SelectionMachine.Cos.selEnv
      SelectionMachine.Cos.selCoef SelectionMachine.Cos.selWithinF
  let u : ∀ l : Literals, Split.UnionLeafF2 l := UnionMachine.PlanW4.union_planW4 c1 fronts
  let r : ∀ l : Literals, Split.RecoveryLeafF2 l := fun l =>
    Split.recoveryLeafF2_of_certGen l (NearCubicWires.RepairSource.HybridProgram.certGen l)
  literals_rowB_of_parts (Split.literals_parts_of_leavesF2 p u r)

end NearCubicWires.WireExponent3_5.SplitRootTop3

end
