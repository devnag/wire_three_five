import Proof.Supplier.RowOccurrenceReusable

/-! The fixed ordinary loop consumes an ordered list of actual cached-child
occurrences and assembles one signed coefficient. Indices are never deduplicated.
The physical counter and every call/return/rewind are included in the run. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowOccurrenceReusable.machine (fun _ _=>true)
def word {N : ℕ} (indices : List (Fin N)) := indices.flatMap (fun i=>RowIndexField.word i.val)

theorem cfg_eq {t s : ℕ} (phase : Fin 5) (a b : Configuration t s) (total driver : ℕ)
    (hh : a.heads=b.heads) (ht : a.tapes=b.tapes) :
    RepeatMachine.cfg phase a total driver=RepeatMachine.cfg phase b total driver := by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh,ht]

end NearCubicWires.RepairOrdinary.RowOccurrenceLoop
