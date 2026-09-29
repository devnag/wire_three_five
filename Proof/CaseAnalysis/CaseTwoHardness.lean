import Proof.CaseAnalysis.Xor
import Proof.CaseAnalysis.Language
import Proof.Amplification.XorResourcesProjection

/-! The exact canonical Case-2 core consumes the two local farness facts.
The unchanged XOR source uses the sharper checked coefficient policy and
the original constant mass cap; both physical classes keep the same table. -/
namespace NearCubicWires.RepairSource.CloseoutLanguage
open SourceInterfaces RepairRepresentation RepairOrdinary RepairXor CircuitRestriction
open RecoveryPipeline ComponentwiseTransfer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem core_case_two {M : TimedDecisionMachine} {T : Nat→Nat} {c d n : Nat}
    (pcp : ProjectionPCP M T) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n)
    (copies clauseBits target : Nat) (hsmall : RecoveryChoice.SmallOracle pcp d input) :
    let oracle:=(RecoveryChoice.oracleSelector pcp d input hsmall).circuit
    let request:=PCPPSubstitution.sourceRequest a oracle (pcp.queryAddressBits input)
      (pcp.decision input (fun _=>false))
    let pcpp:=a.output request
    ∀ (hc : pcpp.clauseBits ≤ clauseBits) (hfit : copies*(request.arity+clauseBits+1) ≤ target),
      core pcp a amplifier input copies clauseBits target=
        padCore (xorPower (paddedUnsigned pcpp hc) copies) hfit := by
  intro oracle request pcpp hc hfit
  dsimp only [oracle,request,pcpp] at hc hfit
  simp only [core,dif_pos hsmall,dif_pos hc,dif_pos hfit]
  rfl

end
end NearCubicWires.RepairSource.CloseoutLanguage
