import Proof.Packets.SubstitutionOuterStep

/-! The outer reverse monomial loop of substitution. Its physical count driver
is retained, and the source cursor returns to the start of the flattened bank. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)


end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
