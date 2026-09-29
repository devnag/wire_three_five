import Proof.MachineModel.OrdinaryMatrixVariableProduct

/-! The indexed Williams call pays a return of every local work head while
retaining the external bit-offset cursor. The log is an actual extra tape. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableReset
open LocalBitMultitape MatrixScoreBatch MatrixWilliamsProduct RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selected (a : WilliamsAlgorithm) (i : Fin (MatrixVariableProduct.tapes a)) : Bool :=
  decide (i.val≠424)
noncomputable def input (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) :=
  Rewind.recording (MatrixVariableProduct.input a r bit) 0

theorem input_head (a : WilliamsAlgorithm) (r : Request) (bit : ℕ)
    (i : Fin (MatrixVariableProduct.tapes a)) (hi : selected a i=true) :
    (MatrixVariableProduct.input a r bit).heads i=0 := by
  revert hi
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi
    change (Fin.addCases (m := 425) (n := (source a).program.tapeCount)
      (motive := fun _ => ℕ) (MatrixVariableInput.input r bit).heads (fun _ => 0)) (j.castAdd (source a).program.tapeCount)=0
    rw [Fin.addCases_left]
    change (MatrixVariablePlane.input r bit).heads j=0
    rw [MatrixVariablePlane.input_heads]
    have hn : j≠424 := by
      intro he
      subst j
      simp [selected] at hi
    simp [hn]
  · intro _
    change (Fin.addCases (m := 425) (n := (source a).program.tapeCount)
      (motive := fun _ => ℕ) (MatrixVariableInput.input r bit).heads (fun _ => 0)) (j.natAdd 425)=0
    rw [Fin.addCases_right]

end NearCubicWires.RepairOrdinary.MatrixVariableReset
