import Proof.CaseAnalysis.RowsCircuitBottomErase

namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportSideStream
open LocalBitMultitape CanonicalWitnessCodec SupplierPipeline RadixSemantics
open CloseoutRowsGatePairHeads CloseoutRowsGateSupport ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 1060 := ![994,1059,1057]
theorem slots_injective : Function.Injective slots := by decide

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportSideStream
