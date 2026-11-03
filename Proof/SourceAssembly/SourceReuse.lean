import Proof.SourceAssembly.SourceBundle

/- Same ordinary source programs on retained backing.  No allocation or erasure
is inferred from these representation identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ6e421fabe2aa4155_SourceReuse
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairOrdinary.RecoveryExecution RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
noncomputable section

theorem pad_install {t u : Nat} (slots : Fin t → Fin u)
    (R : Fin u → Nat) (ambient : Fin u → List Bool) (bank : Fin t → List Bool) :
    (fun i => ZeroPadding.pad (R i) (install slots ambient bank i)) =
    install slots (fun i => ZeroPadding.pad (R i) (ambient i))
      (fun j => ZeroPadding.pad (R (slots j)) (bank j)) := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp [install, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slots hp
    simp only [install, hp]
    rw [he]

def haltMachine (T : Nat) : Machine T 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

def identityTail {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) : MaskSeedCode mask packet U :=
  { c with tailStates := 1, tail := haltMachine U }

end
end PCJ6e421fabe2aa4155_SourceReuse
