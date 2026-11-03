import Proof.CaseAnalysis.RowsEstimatorPaidDriverReady
import Proof.CaseAnalysis.RowsEstimatorPreparedRun

/-! Actual D production hands the literal bank to the paid reusable Warm consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def Returned (p : Program) (D : ℕ) (word : List Bool) (fields : Fin 7 → List Bool)
    (A : Fin (WarmPrepare.tapes p) → List Bool) : Prop :=
  A (WarmPrepare.spare p)=word ∧
    (∀ i,A (WarmPrepare.work p i)=List.replicate D false) ∧
    A (WarmPrepare.driver p)=List.replicate D true ∧ A (WarmPrepare.log p)=List.replicate (D+1) false ∧
    (∀ i,A (WarmPrepare.source p i)=fields i)

theorem prepare_config {t s u : ℕ} (first : Machine t s) (second : Machine t u)
    (H : Fin t → ℕ) (A : Fin t → List Bool) :
    WarmPrepared.startWith first second H A=(⟨(Composition.machine first second).start,H,A⟩ : Configuration t (s+u)) := rfl

theorem heads_eq (a : WilliamsAlgorithm) (p : Program) (out : List Bool) :
    heads a p out=Fin.addCases (WarmPrepare.heads p out) (fun _ : Fin (ScannedClean.tapes a)=>0) := rfl

theorem restart_embed {n e s t : ℕ} (c : Configuration (n+e) s) (worker : Machine n t)
    (H : Fin n → ℕ) (A : Fin n → List Bool) (extra : Fin e → List Bool)
    (hh : c.heads=Fin.addCases H (fun _=>0)) (ht : c.tapes=Fin.addCases A extra) :
    Composition.restart c (TapeEmbedding.machine e worker).start=
      TapeEmbedding.config (fun _ : Fin e=>0) extra (⟨worker.start,H,A⟩ : Configuration n t) := by
  apply configuration_ext
  · rfl
  · exact hh
  · exact ht

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
