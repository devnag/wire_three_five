import Proof.SourceAssembly.SourceThresholdRetained

/- The actual full THR circuit is framed at its measured logical append head.
The native and declared-support streams remain available in their old ports. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourceCircuitFrame
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound CloseoutRowsEstimatorParity SupplierPipeline CompilerSemantics
open RepairSource.ProjectionNormalization
open CloseoutRowsOriginalClause (index negative)
noncomputable section

theorem fresh_forward {t s extra : Nat} (p : Machine t s) (i : Fin extra) :
    CursorRestore.NoLeft (TapeEmbedding.machine extra p) (i.natAdd t) := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩:=Option.map_eq_some_iff.mp ha
  subst a
  simp only [TapeEmbedding.action,Fin.addCases_right]
  decide

theorem frame_forward : CursorRestore.NoLeft (CloseoutRowsTupleSeek.frameMachine true) 1 := by
  intro q bs a ha
  fin_cases q <;> simp [CloseoutRowsTupleSeek.frameMachine,CloseoutRowsTouching.FrameStream.machine] at ha
  all_goals subst a;simp

theorem pair_forward : CursorRestore.NoLeft (CloseoutRowsTupleSeek.pairMachine true) 1 :=
  CursorRestore.composition_forward _ _ _
    (EquationRowCuts.embedded_forward 2 _ 1 frame_forward)
    (EquationRowCuts.unselected_forward _ _ 1 (by decide))

theorem assembler_forward : CursorRestore.NoLeft PCJ6e421fabe2aa4155_SourceSymmetricAssemble.machine 5 :=
  CursorRestore.composition_forward _ _ _
    (CursorRestore.focus_forward _ (by decide) _ 2 EquationRowRaw.header_field_forward)
    (CursorRestore.composition_forward _ _ _
      (CursorRestore.focus_forward _ (by decide) _ 1 frame_forward)
      (CursorRestore.focus_forward _ (by decide) _ 1 (CursorRestore.repeat_forward _ _ 1 pair_forward)))

end
end PCJ6e421fabe2aa4155_SourceCircuitFrame
