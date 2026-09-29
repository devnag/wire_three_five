import Proof.MachineModel.OrdinaryRecordCell

/-! Complete cell evaluation on the actual annotated-record encoding. The
fixed controller consumes the table itself; every local rank extraction,
reset and output append is charged by the accepted record body. -/
namespace NearCubicWires.RepairOrdinary.RecordLoop
open LocalBitMultitape SignedSortKey
open RecordCell (config)
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


@[simp] theorem config_cells {s : ℕ} (state : Fin s) (width a b rank : ℕ)
    (upper recordBack cloneBack : List Bool) (mask : Bool) (source : List Bool) (pos : ℕ) (out : List Bool) :
    (config state width a b rank upper recordBack cloneBack mask source pos out).tapeCells =
      source.length + out.length + upper.length + recordBack.length + cloneBack.length + 52 * width + 31 := by
  simp [config, TapeEmbedding.config, CellEmit.config, LocalCell.input, LocalCell.raw,
    RecordCell.recordTapes, Configuration.tapeCells, Fin.sum_univ_succ, Fin.addCases]
  omega

end NearCubicWires.RepairOrdinary.RecordLoop
