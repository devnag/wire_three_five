import Proof.SourceAssembly.SourceFinishCycle
import Proof.SourceAssembly.SourceRequestConsumer

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding SourceInterfaces
open PCJ1fef9807c6954e94_Native PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open SupplierEstimator SupplierPipeline NearCubicWires.P1Closure
namespace NearCubicWires.SourceConstruction.Cycle
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

def Free {U tc w m : Nat} (slot : Fin 13 → Fin U) (maskSlots : Fin (5 + w) → Fin U)
    (pslots : Fin tc → Fin U) (poolSlots : Fin 373 → Fin U) (familySlots : Fin m → Fin U)
    (rewindSlots : Fin 3 → Fin U) (x : Fin U) : Prop :=
  SourceRequest.Outside slot maskSlots pslots poolSlots x ∧ (∀ i, familySlots i ≠ x) ∧
    (∀ i, rewindSlots i ≠ x)

def cycleCode {U s : Nat} (mask : MaskProducer) {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
    (maskSlots : Fin (5 + mask.work) → Fin U) (hminj : Function.Injective maskSlots)
    (pslots : Fin packet.ordinary.program.tapeCount → Fin U) (hsinj : Function.Injective pslots)
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
    (s1 d1 l1 s2 d2 l2 : Fin U) (pre : Machine U s)
    (cs : Fin 16 → Fin U) (fam : Fin (r_tapes printer) → Fin U) (drv : Fin 7 → Fin U) :
    MaskFamilyCode mask packet rows U :=
  { SLoad.Prepared.code mask packet rows maskSlots hminj pslots hsinj slot ret retDrv log rawDrv
      rawDst rawLog familySlots hfinj poolSlots hpinj rewindSlots hrinj hraw hpool hsrc
      s1 d1 l1 s2 d2 l2 _ (FinishCycle.machine printer cs fam drv) with
    seed := PCJ6e421fabe2aa4155_SourceRefill.prepend
      (SourceRequest.seedCode mask packet maskSlots hminj pslots hsinj slot ret retDrv log rawDrv
        rawDst rawLog) pre }

end
end NearCubicWires.SourceConstruction.Cycle
end
