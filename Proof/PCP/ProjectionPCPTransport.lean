import Proof.Foundations.OuterPCPRecovery

/-! Pull back one selected source PCP along a length-indexed input encoding.
This keeps its exact random bits, proof addresses and decision predicates.
It is a semantic transport into the production outer-case consumer, not an
ordinary implementation of the encoding or a uniform PCP source factory.
The inherited constructionSteps field counts only the source construction;
the ordinary constructor must separately pay for producing the encoded input.
-/
namespace NearCubicWires.RepairOrdinary.PCPTransport
open SourceInterfaces OuterPCPRecovery RecoveryPipeline
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pullback {sourceMachine : TimedDecisionMachine} {sourceTime : ℕ → ℕ}
    (pcp : ProjectionPCP sourceMachine sourceTime)
    (targetMachine : TimedDecisionMachine) (targetTime length : ℕ → ℕ)
    (encode : {n : ℕ} → BitInput n → BitInput (length n)) :
    ProjectionPCP targetMachine targetTime where
  nativeWidth n := pcp.nativeWidth (length n)
  queryCount n := pcp.queryCount (length n)
  queryAddressBits input := pcp.queryAddressBits (encode input)
  decision input := pcp.decision (encode input)
  constructionSteps n := pcp.constructionSteps (length n)

variable {sourceMachine targetMachine : TimedDecisionMachine}
  {sourceTime targetTime length : ℕ → ℕ}
  (pcp : ProjectionPCP sourceMachine sourceTime)
  (encode : {n : ℕ} → BitInput n → BitInput (length n))

@[simp] theorem accepts_eq {n : ℕ} (input : BitInput n) (proof randomness) :
    (pullback pcp targetMachine targetTime length encode).accepts input proof randomness =
      pcp.accepts (encode input) proof randomness := rfl

@[simp] theorem fraction_eq {n : ℕ} (input : BitInput n) (proof) :
    (pullback pcp targetMachine targetTime length encode).acceptanceFraction input proof =
      pcp.acceptanceFraction (encode input) proof := rfl

end NearCubicWires.RepairOrdinary.PCPTransport
