import Proof.SourceAssembly.SourceThresholdPhysical

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceThresholdCanonical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline CompilerSemantics
open CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceThresholdPhysical
noncomputable section

theorem card_eq {q : Nat} (S : Finset (Fin q)) :
    (normalizedThresholdParityCircuit S).top.support.card=S.card := by
  simp [normalizedThresholdParityCircuit,thresholdParityTopGate]

theorem index_val {q : Nat} (S : Finset (Fin q))
    (i : Fin (normalizedThresholdParityCircuit S).top.support.card) :
    (retainedTopIndex (normalizedThresholdParityCircuit S) i).val=i.val := by
  have hc : (Finset.univ : Finset (Fin S.card)).card=S.card := by simp
  have he := Finset.orderEmbOfFin_unique (s:=(Finset.univ : Finset (Fin S.card))) rfl
    (f:=Fin.cast hc) (fun _=>Finset.mem_univ _) (Fin.cast_strictMono hc)
  exact (congrArg Fin.val (congrFun he i)).symm

theorem ofFn_range {α : Type} (n : Nat) (f : Nat→α) :
    List.ofFn (fun i : Fin n=>f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem signed_eq (j : Nat) :
    intWord (if Even j then (1 : Int) else -1)=[Alternating.flag j,true,false,true] := by
  rw [Alternating.flag_odd]
  rcases Nat.even_or_odd j with he | ho
  · simp only [he,if_true,decide_eq_false (Nat.not_odd_iff_even.mpr he)];rfl
  · simp only [Nat.not_even_iff_odd.mpr ho,if_false,decide_eq_true ho];rfl

theorem top_eq {q : Nat} (S : Finset (Fin q)) :
    thresholdWord (nonStrictAsStrict (retainedTopGate (normalizedThresholdParityCircuit S)))=
      PCJ6e421fabe2aa4155_SourceThresholdTop.payload S.card := by
  change natWord _ ++ (List.ofFn (fun i=>if Even (retainedTopIndex (normalizedThresholdParityCircuit S) i).val
      then (1 : Int) else -1)).flatMap intWord ++ intWord (1-1) = _
  simp only [index_val]
  rw [ofFn_range _ (fun j=>if Even j then (1 : Int) else -1),card_eq]
  simp only [List.flatMap_map]
  unfold PCJ6e421fabe2aa4155_SourceThresholdTop.payload
  simp only [signed_eq]
  rfl


theorem bottom_eq {q : Nat} (S : Finset (Fin q))
    (i : Fin (normalizedThresholdParityCircuit S).top.support.card) :
    PCJd4d1d9d7d1fa4313_Production.bottomWord
      ((normalizedThresholdParityCircuit S).bottom (retainedTopIndex (normalizedThresholdParityCircuit S) i))=
      natWord q++weights (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)++false::natWord i.val := by
  change CloseoutRowsCircuitBottom.nativeWord (thresholdParityBottomGate S _)=_
  rw [staircase_native,index_val]
  simp only [bottomWord,CloseoutRowsGateSupport.gateMembers,List.length_ofFn]
  rfl

theorem bottoms_eq {q : Nat} (S : Finset (Fin q)) :
    (List.ofFn (fun i=>(normalizedThresholdParityCircuit S).bottom
      (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
        (fun g=>frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g))=
      CloseoutRowsTupleSeek.nativeWord (gates q S.card
        (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)) := by
  rw [show (List.ofFn (fun i=>(normalizedThresholdParityCircuit S).bottom
      (retainedTopIndex (normalizedThresholdParityCircuit S) i))).flatMap
        (fun g=>frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g))=
      (List.ofFn (fun i : Fin (normalizedThresholdParityCircuit S).top.support.card=>
        frame (natWord q++weights (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)++false::natWord i.val))).flatten by
    simp only [List.ofFn_eq_map,List.flatMap_map]
    apply List.flatMap_congr
    intro i _
    rw [bottom_eq]]
  rw [ofFn_range _ (fun j=>frame (natWord q++weights (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)++false::natWord j)),card_eq]
  simp only [CloseoutRowsTupleSeek.nativeWord,gates,List.flatMap_map]
  rfl

theorem bytes_eq {q : Nat} (S : Finset (Fin q)) :
    native q S.card (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)=
      PCJd4d1d9d7d1fa4313_Production.thrWord (normalizedThresholdParityCircuit S) := by
  unfold native PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.prefixWord
    PCJd4d1d9d7d1fa4313_Production.thrWord
  rw [gates_length,top_eq,bottoms_eq]
  have hw : (normalizedThresholdParityCircuit S).top.wireCount=S.card := card_eq S
  rw [hw]


end
end PCJ6e421fabe2aa4155_SourceThresholdCanonical
