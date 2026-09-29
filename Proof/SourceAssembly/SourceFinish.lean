import Proof.Assembly.Assembly
import Proof.MachineModel.RuntimeShape
import Proof.SourceAssembly.SourceClearBound
import Proof.SourceAssembly.SourceLiveCount

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding
open RepairRepresentation SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
namespace NearCubicWires.SourceConstruction.Finish
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

/-! ## 1. The initializer's two tape groups -/

/-! ## 2. The docked, padded initializer -/

/-! ## 3. The `Prepared` side: the rewound source port is the initializer's padded `D` -/

/-! ## 4. The budget class of the core -/

end
end NearCubicWires.SourceConstruction.Finish
end
