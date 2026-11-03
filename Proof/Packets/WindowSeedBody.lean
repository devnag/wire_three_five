import Proof.Packets.WindowSeedFinish

/-! The fixed window initialization program physically constructs every
private scalar and loop driver from seven retained numeric metadata tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open SignedSortKey
noncomputable section


def body := Composition.machine (copyAt 67 46) (Composition.machine (rawAt 67 49) (Composition.machine (rawAt 66 59) (Composition.machine (zeroAt 65 53) (Composition.machine (copyAt 53 54) (Composition.machine (copyAt 53 57) (Composition.machine (copyAt 62 52) (Composition.machine (copyAt 64 58) (Composition.machine (zeroAt 67 47) (Composition.machine (copyAt 66 60) (Composition.machine (predAt 60) (Composition.machine (valueAt 60 47) (Composition.machine (clearOneAt 60) (widthAt)))))))))))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowSeed
