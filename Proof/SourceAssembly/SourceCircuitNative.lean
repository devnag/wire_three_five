import Proof.SourceAssembly.SourceTopNative

/- Execute the original compact-circuit parser and native supplier. A one-bit
paid boot handles its arity sentinel; recorded execution rewinds the actual
native append cursor without a separately supplied length driver. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceCircuitNative
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryExecution SupplierPipeline CanonicalWitnessCodec RadixSemantics
open PCJd4d1d9d7d1fa4313_Production
noncomputable section
attribute [local irreducible] CloseoutRowsSupportStream.Threshold.machine CloseoutRowsSupportStream.Threshold.program

theorem empty_heads (i : Fin 1704) :
    CloseoutRowsSupportStream.Threshold.heads [] [] i=(if i.val=1674 then 1 else 0) := by
  refine Fin.addCases (m:=1703) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simp only [CloseoutRowsSupportStream.Threshold.heads,Fin.addCases_left,Fin.val_castAdd,
      CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads,List.length_nil]
    by_cases h : j=1688
    · subst j; decide
    · simp [h]
  · simp [CloseoutRowsSupportStream.Threshold.heads]



end
end PCJ6e421fabe2aa4155_SourceCircuitNative
