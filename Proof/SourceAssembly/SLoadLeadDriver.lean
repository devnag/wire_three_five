import Proof.SourceAssembly.SLoadRequestLead

/-! The one open input obligation of the accepted second conjunct.

`RequestFrames.request_frames_step` consumes the suffix's unary domain driver
as a BARE word, `A drv = ZeroPadding.pad capD (List.replicate (B 4).length true)`,
while every retained ambient field of this loader family is framed. The gap is
paid on the LEAD side, by one extra call of the already docked unframing
producer `SLoad.Lead.bareStage` (`Streaming.machine`, all heads zero in and
out) against a retained `frame (List.replicate r.q true)`. No new machine and
no new local program: the prefix simply gains a fifth stage, and its fuel the
corresponding `4 * r.q + 2 + 1`.

The physical length of the driver is read off the retained framed word, and
`(maskData a r).word.length = r.q` (`word_length`) is what makes it the
driver the framing pass demands. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.LeadDriver
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The extended prefix: the retained unary domain driver is unframed onto the
suffix's driver slot, then the accepted four-stage mask input load runs. -/
noncomputable def machine {U work : Nat} (retDrv drv : Fin U) (ret : Fin 4 → Fin U)
    (maskSlots : Fin (5 + work) → Fin U) (log : Fin U) : Machine U 34 :=
  Composition.machine (Lead.bareStage retDrv drv log)
    (Lead.machine ret (MaskInput.live maskSlots) log)

/-- Fuel for the extended prefix. -/
def prefixFuel (a : DecompositionAlgorithm) (r : Request) : Nat :=
  4 * r.q + 2 + 1 + RequestLead.prefixFuel a r


end
end SLoad.LeadDriver
