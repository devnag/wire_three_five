import Proof.Amplification.RecoveryValuationSetup

/-! Execute the first certificate parser after its paid setup, retaining
the literal Boolean parse result on global tape30 at head0. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def entryMachine := Composition.machine setupMachine parserMachine

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
