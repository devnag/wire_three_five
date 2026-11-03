import Proof.SourceAssembly.SourceSymmetricPhysical

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceSymmetricCanonical
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline
open CloseoutRowsOriginalClause (index negative)
open PCJ6e421fabe2aa4155_SourceSymmetricPhysical
noncomputable section

theorem top_eq {q : Nat} (S : Finset (Fin q)) :
    PCJ6e421fabe2aa4155_SourceSymmetricTop.table S.card=List.ofFn (normalizedParityCircuit S).top := by
  apply congrArg List.ofFn
  funext i
  exact Alternating.flag_odd i.val

theorem bytes_eq {q : Nat} (S : Finset (Fin q)) (C : Nat) :
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord
      (PCJ6e421fabe2aa4155_SourceSymmetricTop.table
        (PCJ6e421fabe2aa4155_SourceSymmetricScan.selected (ZeroPadding.pad C
          (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)) q).length)
      (gates q (ZeroPadding.pad C (PCJ6e421fabe2aa4155_SourceSymmetricMeaning.bitmap S)))=
        PCJd4d1d9d7d1fa4313_Production.symWord (normalizedParityCircuit S) := by
  unfold PCJ6e421fabe2aa4155_SourceSymmetricAssemble.circuitWord
    PCJ6e421fabe2aa4155_SourceSymmetricAssemble.prefixWord
  rw [gates_length,PCJ6e421fabe2aa4155_SourceSymmetricMeaning.count_eq,top_eq,
    gates_native,PCJ6e421fabe2aa4155_SourceSymmetricMeaning.native_eq]
  rfl

end
end PCJ6e421fabe2aa4155_SourceSymmetricCanonical
