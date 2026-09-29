import Proof.MachineModel.OrdinaryMatrixWilliamsInput

/-! The actual ordinary producer now calls the corrected Williams source
wrapper and pays a complete return scan. Native count cells retain their
original row-major order and exact natural values. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsProduct
open LocalBitMultitape MatrixScoreBatch RepairRepresentation ExecutableInterfaces
open WilliamsLoaderForms WilliamsProductCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def request (r : Request) (negative : Bool) (bit : ℕ) : RectangularProductRequest where
  dimension := r.U
  left := fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit
  right := booleanRight r
noncomputable def source (a : WilliamsAlgorithm) := (WilliamsCall.realization a).wrapper.reset
noncomputable def sourceBudget (a : WilliamsAlgorithm) (r : Request) := 2*WilliamsCall.budget a (request r false 0)+2

theorem source_run (a : WilliamsAlgorithm) (r : Request) (negative : Bool) (bit : ℕ) : ∃ actual,
    run (source a).program.machine (sourceBudget a r)
      ((source a).program.inputTapes (RepairRepresentation.natWord r.U++MatrixSignedPlane.plane r negative bit++MatrixRightPlaneNative.plane r))=some actual ∧
    actual.final.tapes (source a).program.outputTape=planeCounts r negative bit ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps≤ sourceBudget a r := by
  obtain ⟨actual,ha,ho⟩ := (source a).realizes (request r negative bit)
  have hh := (source a).headsReset (request r negative bit) actual ha
  exact ⟨actual,ha,ho,hh,runFrom_steps_le _ _ _ _ ha⟩


noncomputable def budget (a : WilliamsAlgorithm) (r : Request) := MatrixWilliamsInput.budget r+1+sourceBudget a r

theorem initial_join {t e s v : ℕ} (p : Machine t s) (q : Machine (t+e) v) (ts : Fin t → List Bool) :
    Composition.leftConfig v (TapeEmbedding.config (fun _ : Fin e => 0) (fun _ : Fin e => []) (initialConfiguration p ts))=
      initialConfiguration (Composition.machine (TapeEmbedding.machine e p) q)
        (Fin.addCases (m := t) (n := e) (motive := fun _ => List Bool) ts (fun _ => [])) := by
  apply configuration_ext
  · rfl
  · funext i
    change (Fin.addCases (m := t) (n := e) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0)) i=0
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.addCases_left,Fin.addCases_right]
  · rfl

end NearCubicWires.RepairOrdinary.MatrixWilliamsProduct
