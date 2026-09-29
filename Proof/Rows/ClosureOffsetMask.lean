import Proof.Rows.FinalCellComparator

/-! A.3's fixed-column comparison scan with ONE retained target tuple.
The source stream is consumed once. The target is physically rewound after
each cell; no table-sized repeated-target word is an input. The complete
four-tape body and five-tape loop exits are specified. Actual offset source
production is upstream, not asserted by this theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetMask
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairSource.VerifierDecoding RepairSource.CloseoutFinal



end NearCubicWires.P1Closure.OffsetMask
