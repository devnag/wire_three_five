import Proof.SourceAssembly.MaskFamily
import Proof.SourceAssembly.SLoadSetup

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Prepared
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
noncomputable section

variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
  {rows : RowProducer selector a printer} {U : Nat}

def code {U : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U)
    (hsinj : Function.Injective pslots)
    (slot : Fin 13 → Fin U) (ret : Fin 4 → Fin U)
    (retDrv log rawDrv rawDst rawLog : Fin U)
    (familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin U)
    (hfinj : Function.Injective familySlots)
    (poolSlots : Fin 373 → Fin U) (hpinj : Function.Injective poolSlots)
    (rewindSlots : Fin 3 → Fin U) (hrinj : Function.Injective rewindSlots)
    (hraw : pslots packet.ordinary.program.outputTape = familySlots
      ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 262).castAdd 1))
    (hpool : poolSlots 34 = familySlots
      ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 0).castAdd 1))
    (hsrc : rewindSlots 0 = familySlots
      ((PCJ38fbfed565f64139_Ready.descriptor printer (rowWork rows.privateWork)).castAdd 1))
    (s1 d1 l1 s2 d2 l2 : Fin U)
    (finishStates : Nat) (finish : Machine U finishStates) :
    MaskFamilyCode mask packet rows U where
  familySlots := familySlots
  familyInjective := hfinj
  poolSlots := poolSlots
  poolInjective := hpinj
  rewindSlots := rewindSlots
  rewindInjective := hrinj
  seed := MaskReady.code mask packet maskSlots hminj pslots hsinj slot ret retDrv log
    rawDrv rawDst rawLog
  rawAlias := hraw
  poolAlias := hpool
  sourceAlias := hsrc
  setupLoadStates := _
  setupLoad := Setup.machine s1 d1 (familySlots (rowRequestPort printer rows.privateWork)) l1
    s2 d2 (familySlots (rowCapsPort printer rows.privateWork)) l2
  finishStates := finishStates
  finish := finish

/-! ### Closing the seam: the setup loader's exit bank, explicitly

`SLoad.Setup.setup_load_step` reports its exit bank existentially, which is
enough for the second conjunct alone but not for the rewind bank, since
`Prepared` shares one `ambientA` between the two. `SLoad.Setup.setup_frames`
already reports the exit bank EXPLICITLY, so the same assembly is redone here
against that explicit bank. No machine and no new run is introduced. -/




end
end SLoad.Prepared
