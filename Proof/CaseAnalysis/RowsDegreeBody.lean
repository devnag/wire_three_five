import Proof.CaseAnalysis.RowsLoopInterface

/-! One executed degree transition: print and clean the positional cuts,
advance the retained counters, and reload six short templates. The joined
receipt has exactly the next degree's entry configuration. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsDegreeBody
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary CloseoutRowsLoopInterface
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine callee CloseoutRowsDegreeNext.machine
noncomputable def machine {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine (first callee) CloseoutRowsMetadataReload.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsDegreeBody
