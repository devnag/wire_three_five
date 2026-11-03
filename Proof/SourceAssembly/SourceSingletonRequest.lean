import Proof.SourceAssembly.SourceCircuitFrame

/- First actual complete Request native/support family: the carried systematic
singleton. Fixed L/target are paid finite-code words, q/circuit read from cache. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSingletonRequest
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline SupplierEstimator
open CloseoutRowsOriginalClause (index negative)
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

def request {q : Nat} (S : Finset (Fin q)) (L target : Nat) : Request:=
  .thr ⟨q,[normalizedThresholdParityCircuit S]⟩ (by simp) L target

theorem support_eq {q : Nat} (S : Finset (Fin q)) (L target : Nat) (a : DecompositionAlgorithm) :
    CloseoutRowsTupleSeek.supportWord (PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates q S.card
      (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))=(request S L target).supportWord a := by
  unfold Request.supportWord request Request.family PCJ9eff70d512234a4c_Fixed.Packets.thrFamily
  simp only [thresholdFourfoldOccurrences,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change _=(List.ofFn (fun i : Fin (normalizedThresholdParityCircuit S).top.support.card=>
    (normalizedThresholdParityCircuit S).bottom (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
      (fun g=>frame (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap g.support))
  rw [show (List.ofFn (fun i : Fin (normalizedThresholdParityCircuit S).top.support.card=>
      (normalizedThresholdParityCircuit S).bottom (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
        (fun g=>frame (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap g.support))=
      (List.ofFn (fun _ : Fin (normalizedThresholdParityCircuit S).top.support.card=>
        frame (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S))).flatten by
    simp only [List.ofFn_eq_map,List.flatMap_map];rfl]
  rw [PCJ6e421fabe2aa4155_SourceThresholdCanonical.ofFn_range _ (fun _=>frame (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)),
    PCJ6e421fabe2aa4155_SourceThresholdCanonical.card_eq]
  simp only [CloseoutRowsTupleSeek.supportWord,PCJ6e421fabe2aa4155_SourceThresholdPhysical.gates,List.flatMap_map]
  rfl

def circuit (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2^(a.output r).clauseBits))
    (hk : index ((a.output r).clauses ci).left < (a.output r).systematicBits):=
  normalizedThresholdParityCircuit ((a.output r).systematicSupport ⟨index ((a.output r).clauses ci).left,hk⟩)


end
end PCJ6e421fabe2aa4155_SourceSingletonRequest
