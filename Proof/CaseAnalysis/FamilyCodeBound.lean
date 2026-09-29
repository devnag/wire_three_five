import Proof.CaseAnalysis.WitnessAliases

/-! The exact V-sum third payload is charged as a balanced family, using the
existing checked per-sum codec bounds. No single-sum witness bound is reused
as though it already included the family. -/
namespace NearCubicWires.RepairSource.CloseoutFamilyCode
open RepairOrdinary CloseoutWitness CanonicalWitnessCodec RecoveryWitnessPolicy
open SourceInterfaces CanonicalBinary ExecutableInterfaces
open PolynomialSchedule
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem component_bounds (limits : RecoveryWitnessLimits) :
    let p:=recoveryWitnessCodeParameter limits
    canonicalBooleanCircuitCodeBitBound p ≤ recoveryWitnessCodeBitBound limits ∧
      canonicalLegalSumCodeBitBound p (canonicalSymmetricCircuitCodeBitBound p) ≤ recoveryWitnessCodeBitBound limits ∧
      canonicalLegalSumCodeBitBound p (canonicalThresholdCircuitCodeBitBound p) ≤ recoveryWitnessCodeBitBound limits := by
  dsimp only
  have hs:=Nat.le_max_left
    (canonicalLegalSumCodeBitBound (recoveryWitnessCodeParameter limits)
      (canonicalSymmetricCircuitCodeBitBound (recoveryWitnessCodeParameter limits)))
    (canonicalLegalSumCodeBitBound (recoveryWitnessCodeParameter limits)
      (canonicalThresholdCircuitCodeBitBound (recoveryWitnessCodeParameter limits)))
  have ht:=Nat.le_max_right
    (canonicalLegalSumCodeBitBound (recoveryWitnessCodeParameter limits)
      (canonicalSymmetricCircuitCodeBitBound (recoveryWitnessCodeParameter limits)))
    (canonicalLegalSumCodeBitBound (recoveryWitnessCodeParameter limits)
      (canonicalThresholdCircuitCodeBitBound (recoveryWitnessCodeParameter limits)))
  unfold recoveryWitnessCodeBitBound
  simp only [taggedListBitBound]
  omega

def bound (limits : RecoveryWitnessLimits) (V : Nat) :=
  let S:=recoveryWitnessCodeBitBound limits
  taggedListBitBound [2,S,1+2*V^4*(V*S+1)]

theorem code_bound {limits : RecoveryWitnessLimits}
    {variableCount : BooleanCircuit limits.oracleArity→Nat}
    (w : FamilyWitness limits variableCount) (V : Nat) (hV : variableCount w.oracle ≤ V) :
    natBitLength w.code ≤ bound limits V := by
  let S:=recoveryWitnessCodeBitBound limits
  obtain ⟨hbool,hsym,hthr⟩:=component_bounds limits
  obtain ⟨hp,ha,hsize,_⟩:=recoveryWitnessCodeParameter_bounds limits
  have hc : w.oracle.size ≤ limits.oracleSizeCap := by
    cases w with
    | symmetric c h _=>exact h
    | threshold c h _=>exact h
  have ho : natBitLength (encodeBooleanCircuit w.oracle) ≤ S :=
    (encodeBooleanCircuit_bits_le_parameter w.oracle hp ha (hc.trans hsize)).trans hbool
  have hf : natBitLength w.payload ≤ 1+2*V^4*(V*S+1) := by
    cases w with
    | symmetric c h sums=>
      change variableCount c ≤ V at hV
      apply (sums.code_bits symmetricCircuitCodec S (fun s _=>
        (symmetricCheckedLegalCircuitSum_code_bits_le s).trans hsym)).trans
      gcongr
    | threshold c h sums=>
      change variableCount c ≤ V at hV
      apply (sums.code_bits thresholdCircuitCodec S (fun s _=>
        (thresholdCheckedLegalCircuitSum_code_bits_le s).trans hthr)).trans
      gcongr
  exact w.code_bits S _ ho hf

end NearCubicWires.RepairSource.CloseoutFamilyCode
