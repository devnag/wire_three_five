import Proof.MachineModel.OrdinaryMatrixVariableReset

/-! Finite workspace for the actual indexed source call and paid reset.
The enclosing scheduler must physically supply this capacity; after a call,
every local tape has exactly that bounded support and can be erased together. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariableWorkspace
open LocalBitMultitape MatrixScoreBatch RepairRepresentation MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem add_bound {m n : ℕ} {f : Fin m → ℕ} {g : Fin n → ℕ} {bound : ℕ}
    (hf : ∀ i,f i≤bound) (hg : ∀ i,g i≤bound) (i : Fin (m+n)) :
    Fin.addCases f g i≤bound := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left] using hf j
  · simpa only [Fin.addCases_right] using hg j

theorem add_length_bound {m n : ℕ} {f : Fin m → List Bool} {g : Fin n → List Bool} {bound : ℕ}
    (hf : ∀ i,(f i).length≤bound) (hg : ∀ i,(g i).length≤bound) (i : Fin (m+n)) :
    (Fin.addCases (motive := fun _ => List Bool) f g i).length≤bound := by
  refine Fin.addCases (motive := fun i => (Fin.addCases (motive := fun _ => List Bool) f g i).length≤bound) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left] using hf j
  · simpa only [Fin.addCases_right] using hg j

theorem entry_bounds (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) :
    (∀ i,(MatrixVariableReset.input a r bit).heads i≤1) ∧
    (∀ i,((MatrixVariableReset.input a r bit).tapes i).length≤(physicalInput r).length+2*bit+2) := by
  have hp (i : Fin 425) : (MatrixVariableInput.input r bit).heads i≤1 := by
    change (MatrixVariablePlane.input r bit).heads i≤1
    rw [MatrixVariablePlane.input_heads]
    split <;> omega
  have ht (i : Fin 425) : ((MatrixVariableInput.input r bit).tapes i).length≤(physicalInput r).length+2*bit+2 := by
    change ((MatrixVariablePlane.input r bit).tapes i).length≤_
    rw [MatrixVariablePlane.input_tapes]
    split
    · omega
    · split
      · rw [UnaryTemplate.tape_length]; omega
      · simp
  constructor
  · intro i
    change Fin.addCases (MatrixVariableProduct.input a r bit).heads (fun _ : Fin 1 => 0) i≤1
    apply add_bound (hg := by intro j; omega)
    intro j
    change Fin.addCases (MatrixVariableInput.input r bit).heads
      (fun _ : Fin (source a).program.tapeCount => 0) j≤1
    exact add_bound hp (by intro k; omega) j
  · intro i
    change (Fin.addCases (motive := fun _ => List Bool) (MatrixVariableProduct.input a r bit).tapes (fun _ : Fin 1 => [] ) i).length≤_
    apply add_length_bound (hg := by intro j; simp)
    intro j
    change (Fin.addCases (motive := fun _ => List Bool) (MatrixVariableInput.input r bit).tapes
      (fun _ : Fin (source a).program.tapeCount => []) j).length≤_
    exact add_length_bound ht (by intro k; simp) j

end NearCubicWires.RepairOrdinary.MatrixVariableWorkspace
