import Proof.Amplification.RecoveryPrefixColdBudget

/-! The checked cold search at the two actual canonical recovery formulas.
The existing balanced payload is its input; the remaining emitter must
produce this input from the retained normalized PCP word. All decoding,
formula-size guards, and full canonical-output identities are discharged. -/
namespace NearCubicWires.RepairSource.RecoveryFormulaPrefix
open RepairOrdinary CanonicalBinary CanonicalRecoveryLanguage
open CanonicalSATSelfReduction BoundedOracleStructuralCircuit TseitinCNF
open BalancedCNFSATEncoding CircuitInputCNF SourceInterfaces OuterPCPRecovery
open RecoveryScheduleEnvelope RecoveryChoice RecoveryQuery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def payload (formula : EncodedCNF) := balancedCNFPayload formula

theorem payload_decodes (formula : EncodedCNF) : PayloadDecodes true (payload formula) formula := by
  simp [PayloadDecodes,payload,balancedCNFPayload]

def proofCount {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (n : Nat) := 2^pcp.nativeWidth n

def oracleCount {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d n : Nat) :=
  descriptionWidth (pcp.nativeWidth n) (oracleSizeBound d (pcp.nativeWidth n))

theorem proof_range {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) {n : Nat} (input : BitInput n) :
    proofCount pcp n ≤ natBitLength (Encodable.encode (outerProofRecoveryFormula pcp input)) :=
  (outerProofVariables_le_formula_length pcp input).trans (list_length_le_encoded_bitLength _)

theorem oracle_range {machine : TimedDecisionMachine} {timeBound : Nat→Nat}
    (pcp : ProjectionPCP machine timeBound) (d : Nat) {n : Nat} (input : BitInput n) :
    oracleCount pcp d n ≤ natBitLength (Encodable.encode
      (boundedOracleRecoveryFormula pcp input (oracleSizeBound d (pcp.nativeWidth n)))) := by
  let verifier := boundedOracleVerifierCircuit pcp input (oracleSizeBound d (pcp.nativeWidth n))
  have hv : oracleCount pcp d n ≤ (circuitInputFormula verifier).length :=
    (Nat.le_add_right _ verifier.nodes.length).trans (circuitInputVariables_le_formula_length verifier)
  exact hv.trans (list_length_le_encoded_bitLength _)

end NearCubicWires.RepairSource.RecoveryFormulaPrefix
