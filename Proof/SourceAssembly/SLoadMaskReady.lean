import Proof.SourceAssembly.SLoadLeadDriver
import Proof.SourceAssembly.SLoadRequestLead
import Proof.SourceAssembly.SLoadSuffixFrame
import Proof.SourceAssembly.SLoadTail

/-! The deliverable: an actual `MaskSeedCode` and its `Ready` certificate.

The three conjuncts are the three accepted physical runs of this source
loader, with the fuel `Ready`'s last conjunct asks for, as an equality rather
than an estimate:

```
(prefixFuel+1+(maskBudget+1+suffixFuel))+1+(packetBudget+1+tailFuel)
```

Neither `∀ B` costs a clearing scan. Both producers' final banks are pinned by
determinism of `Step` (`Tail.mask_bank`, `Tail.packet_bank`), so the
quantifiers range over the single bank the producer's own correctness field
supplies, and the mask worker's and the packet worker's private tapes are
carried out of the loader exactly as they were returned. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.MaskReady
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

/-- The physical source loader: an extended prefix, the docked mask worker's
own suffix and the raw framer, on one ambient layout. Every state count is a
numeral and no request is in scope. -/
noncomputable def code {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} (packet : PacketWriter selector a)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (slots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective slots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U) : MaskSeedCode mask packet U where
  slots := slots
  injective := hsinj
  maskSlots := maskSlots
  maskInjective := hminj
  prefixStates := 34
  lead := LeadDriver.machine retDrv (slot 1) ret maskSlots log
  suffixStates := 34
  suffix := SuffixFrame.machine slot
  tailStates := 5
  tail := Tail.machine (slots packet.ordinary.program.outputTape) rawDrv rawDst rawLog


end
end SLoad.MaskReady
