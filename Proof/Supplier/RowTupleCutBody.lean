import Proof.Supplier.RowTupleCutAppend

/-! The actual tuple consumer emits the complete signed cut: all equation
coordinates, its threshold, then the cached binLift coefficient. The cache
is retained at head zero while the row append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCutBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 RowTupleFramedBody.machine
noncomputable def machine := Composition.machine first RowTupleCutAppend.machine


end NearCubicWires.RepairOrdinary.RowTupleCutBody
