import Proof.SourceAssembly.SLoadLead

/-! The first conjunct of `MaskSeedCode.Ready`.

`Ready` demands, for the chosen prefix program,
`Step c.lead prefixFuel H A (dockH c.maskSlots maskH 0)
  (install c.maskSlots maskA (fun i => ZeroPadding.pad (maskReserve i)
    ((maskData a r).input mask.work i)))`.
This module discharges exactly that statement from the physical prefix run,
with `maskH := H`, `maskA := A`, and a `maskReserve` that is zero on the four
live input tapes and the ambient allocation on the worker's private tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.MaskInput
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding SupplierEstimator
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The four live mask input tapes, inside the worker's slot family. -/
def live {U work : Nat} (maskSlots : Fin (5 + work) → Fin U) : Fin 4 → Fin U :=
  fun j => maskSlots ⟨j.val, by omega⟩

end
end SLoad.MaskInput
