import Proof.SourceAssembly.SourceRowConst
import Proof.SourceAssembly.SourceFinish

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
namespace NearCubicWires.SourceConstruction.FinishCycle
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

def machine (a : WilliamsAlgorithm) {U : ℕ} (cs : Fin 16 → Fin U) (fam : Fin (r_tapes a) → Fin U)
    (drv : Fin 7 → Fin U) :=
  Composition.machine (RecoveryFocus.machine cs RowWidth.machine)
    (RecoveryFocus.machine (Finish.joinSlots a fam drv) (PCJ34388a2fbfa9464b_.machine a))

end
end NearCubicWires.SourceConstruction.FinishCycle
end
