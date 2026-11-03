import Proof.SourceAssembly.SLoadCore

/-! Deliverable 1: the physical `lead` machine of `MaskSeedCode`.

`lead` is four docked calls of two fixed local programs. It reads four
retained framed source fields, which live outside the mask producer's slots,
and physically installs the mask worker's four live input tapes: the bare
support stream and three unary sentinels. Every dimension is read off a
physical framed word (`w.length`), never off a Lean-level parameter, and
every head is physically restored to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Lead
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
noncomputable section

/-- Retained framed source, mask input target, shared reset log. -/
def ports {U : Nat} (src dst log : Fin U) : Fin 3 → Fin U := ![src, dst, log]

/-- The docked unframing producer: five states. -/
noncomputable def bareStage {U : Nat} (src dst log : Fin U) : Machine U 5 :=
  RecoveryFocus.machine (ports src dst log) Streaming.machine

/-- The docked unary-width producer: eight states. -/
noncomputable def widthStage {U : Nat} (src dst log : Fin U) : Machine U 8 :=
  RecoveryFocus.machine (ports src dst log) RecoveryFieldCopy.widthMachine

/-- The fixed prefix program: one unframing call and three width calls,
twenty-nine states, chosen with no request in scope. -/
noncomputable def machine {U : Nat} (ret mslot : Fin 4 → Fin U) (log : Fin U) : Machine U 29 :=
  Composition.machine (bareStage (ret 0) (mslot 0) log)
    (Composition.machine (widthStage (ret 1) (mslot 1) log)
      (Composition.machine (widthStage (ret 2) (mslot 2) log)
        (widthStage (ret 3) (mslot 3) log)))

/-- Fuel for the prefix, in the four actual retained field lengths. -/
def cost (s q k m : Nat) : Nat := 4 * s + 8 * (q + k + m) + 29


end
end SLoad.Lead
