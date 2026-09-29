import Proof.MachineModel.OrdinaryMatrixBatchGateCopy
import Proof.MachineModel.OrdinaryMatrixBatchWidthSetup

/-! Exact physical layout of the cold 166-tape batch entry and its native
49-tape all-gates consumer. Existing header and native fields are reused.

With `φ` (paper3 `alg:pullback`, P3:1623-1671) the width setup (`MatrixBatchWidthSetup`) parses the weight
count and the columns of `φ` on 24 of the 34 blank tapes `132..165` (its word is tape 1, its frame counter
`UnaryTemplate.tape d` tape 92). Its outputs hold the width-dependent per-gate fields: native 1 (the zero
assignment) on 151, native 17 (the weight-count sentinel, head 1) on 146, native 28 (the retained zero) on
155 and native 42 (the columns) on 142. The gate scratch (30 native tapes, erased by every gate before use)
is hosted by the remaining blank tapes, the linear front end's `d`-fields 92, 95 and 99, eight short work
tapes of the width setup, and twelve work tapes of the zero/driver initializer
(`MatrixBatchNativeFields.setup_run_dead`); every host has its head at cell 0. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchGateLayout
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
open MatrixScoreReusableRanks (D)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The width setup's 26 local tapes. -/
def widthSlots : Fin 26 → Fin 166 := ![1,132,133,134,135,136,137,138,139,140,141,92,142,143,144,145,146,148,149,150,151,152,153,154,155,156]
theorem width_injective : Function.Injective widthSlots := by decide
/-- The native loop's 49 tapes. -/
def slots : Fin 49 → Fin 166 := ![157,151,158,159,160,161,49,163,165,92,95,99,144,145,149,77,107,146,61,65,153,150,147,32,154,106,152,39,155,156,23,90,91,93,28,94,96,97,98,100,101,162,142,103,130,164,1,102,89]
theorem slots_injective : Function.Injective slots := by decide

end NearCubicWires.RepairOrdinary.MatrixBatchGateLayout
