import Proof.CaseAnalysis.RowsModeElementaryLayout

/-! The actual cold elementary run is recorded, returned, and physically
cleared. Only the appended raw monomials survive in its work bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReuse
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open CloseoutRowsModeElementaryLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first : Σ s,Machine 52 s:=
  ⟨_,TapeEmbedding.machine 6 (CloseoutRowsModeElementaryReset.machine CloseoutRowsModeElementary.machine)⟩
noncomputable def machine:=Composition.machine first.2 CloseoutRowsModeElementaryClear.machine

end NearCubicWires.RepairOrdinary.CloseoutRowsModeElementaryReuse
