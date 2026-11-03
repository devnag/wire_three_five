import Proof.Packets.DenseAtomInitialize
import Proof.Packets.DenseAtomMaterialize

/-! First dense atom pass: actual zero-table allocation followed by the
complete resident-cache materializer. All entries begin as physically
written zero packets; no dense bank is supplied at entry. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open DenseAtomMaterialize (H A)
open DenseAtomProgram (table codes)
noncomputable def boot :=  TapeEmbedding.machine 1 DenseAtomInitialize.machine
noncomputable def machine := Composition.machine boot DenseAtomMaterialize.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomCold
