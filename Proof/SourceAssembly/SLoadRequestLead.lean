import Proof.SourceAssembly.SLoadMaskInput
import Proof.SourceAssembly.SLoadRequestFrames

/-! Deliverable 1 on an actual request: the first conjunct of
`MaskSeedCode.Ready`, discharged for the supplied mask producer, with
`maskH := H`, `maskA := A`, `maskReserve := MaskInput.reserve blank` and
`prefixFuel := Lead.cost ...`. The support field the prefix unframes is the
SAME retained copy the packet input is framed from (`support_eq`). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.RequestLead
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The prefix fuel, in the request's own physical dimensions. -/
def prefixFuel (a : DecompositionAlgorithm) (r : Request) : Nat :=
  Lead.cost (r.supportWord a).length r.q (normalizedLiveCount r.q r.liveScale)
    (r.family a).occurrences.length

end
end SLoad.RequestLead
