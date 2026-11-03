import Proof.SourceAssembly.SourcePoolDrivers
import Proof.Supplier.RowCachedEquationMeaning

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolAdmissions
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline SupplierEstimator CompilerSemantics RepairSource.VerifierDecoding
open CloseoutRowsOriginalClause (index negative)
open PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ6e421fabe2aa4155_SourceSingletonRequest (request)
noncomputable section

theorem magnitude {q B : Nat} (g : SupportedNormalizedGate q)
    (hb : (CloseoutRowsCircuitBottom.nativeWord g).length≤B) :
    (g.gate.threshold-1).natAbs+(∑i,(g.gate.weight i).natAbs)<2^(B+q+1) := by
  let e : ExactThresholdGate q:=⟨g.gate.weight,g.gate.threshold-1⟩
  have hm:=RowCachedEquation.equation_magnitude e
  have hm' : (g.gate.threshold-1).natAbs+(∑i,(g.gate.weight i).natAbs)<2^(exactWord e).length := by
    simpa only [SupplierPrime.equationMagnitudeBound,RowCachedEquation.equation,e,Nat.add_comm] using hm
  apply hm'.trans_le
  apply Nat.pow_le_pow_right (by decide)
  have he : natWord q++exactWord e=CloseoutRowsCircuitBottom.nativeWord g := by
    simp [e,exactWord,CloseoutRowsCircuitBottom.nativeWord,thresholdWord,
      CloseoutRowsGateSource.request,nonStrictAsStrict,List.append_assoc]
  have hl:=congrArg List.length he
  simp only [List.length_append] at hl
  omega

end
end PCJ6e421fabe2aa4155_SourcePoolAdmissions
