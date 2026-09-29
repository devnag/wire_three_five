import Proof.CaseAnalysis.FinalOriginalFrame
import Proof.CaseAnalysis.FinalPrologueBlankBand
import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.CaseAnalysis.FinalSiteRoundPorts
import Proof.CaseAnalysis.RowsEstimatorParityCounter

/-! The actual admitted cold/prologue/count/append entry on the selected tape layout.
All local frames are supplied by the same physical executions; the counter stays
parked at head 1. The caller still pays its control branches and loop/suffix. -/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry

open NearCubicWires LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation
open ProjectionNormalization CloseoutWitness CloseoutFinal ExtDecompositionBatch CanonicalWitnessCodec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section









attribute [local irreducible] BoundedFamily.workspace CloseoutFinalC10SeedEngine.tapesOf
  CloseoutFinalC10ColdCacheAtAdmission.cacheSlot


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10AdmittedEntry
