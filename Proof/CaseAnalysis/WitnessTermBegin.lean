import Proof.CaseAnalysis.WitnessTermExit

/-! The actual canonical term stream enters the shared term/mass bank.
The same rational fields and circuit payload remain live for the circuit
worker; the mass store and compact output are untouched by this read. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermBegin
open LocalBitMultitape RecoveryRootRound CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RecoveryFocus.machine TermCommit.eraseSlots TermRead.machine

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermBegin
