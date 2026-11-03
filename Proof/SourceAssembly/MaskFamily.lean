import Proof.SourceAssembly.MaskLoad

/-! Joint physical layout: the packet output IS the raw Header source, the
ColdRun pool output IS Header's pool port, and descriptors are appended on
the final loader source. Only paid public-word loaders/final joins remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJc4297ab269d8423a_Source
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

structure MaskFamilyCode (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a)
    (rows : RowProducer selector a printer) (U : Nat) where
  familySlots : Fin (rowTapes printer rows.privateWork+1) → Fin U
  familyInjective : Function.Injective familySlots
  poolSlots : Fin 373 → Fin U
  poolInjective : Function.Injective poolSlots
  rewindSlots : Fin 3 → Fin U
  rewindInjective : Function.Injective rewindSlots
  seed : MaskSeedCode mask packet U
  rawAlias : seed.slots packet.ordinary.program.outputTape = familySlots
    ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 262).castAdd 1)
  poolAlias : poolSlots 34 = familySlots
    ((PCJ38fbfed565f64139_Ready.headerSlots printer (rowWork rows.privateWork) 0).castAdd 1)
  sourceAlias : rewindSlots 0 = familySlots
    ((PCJ38fbfed565f64139_Ready.descriptor printer (rowWork rows.privateWork)).castAdd 1)
  setupLoadStates : Nat
  setupLoad : Machine U setupLoadStates
  finishStates : Nat
  finish : Machine U finishStates

def MaskFamilyCode.base {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    {packet : PacketWriter selector a} {rows : RowProducer selector a printer} {U : Nat}
    (p : MaskFamilyCode mask packet rows U) : FamilyCode packet rows U where
  familySlots := p.familySlots
  familyInjective := p.familyInjective
  poolSlots := p.poolSlots
  poolInjective := p.poolInjective
  rewindSlots := p.rewindSlots
  rewindInjective := p.rewindInjective
  seed := p.seed.base
  rawAlias := p.rawAlias
  poolAlias := p.poolAlias
  sourceAlias := p.sourceAlias
  setupLoadStates := p.setupLoadStates
  setupLoad := p.setupLoad
  finishStates := p.finishStates
  finish := p.finish

/-- Runtime certificate for the public word producers. Its remaining Steps
are precisely source loading and final joins, with the fixed shared programs.
The existing pool, initializer, row loop, framing and rewind are inserted by
`FamilyCode.project`, rather than requested again as physical premises. -/
def MaskFamilyCode.Prepared {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
    {rows : RowProducer selector a printer} {U : Nat} (p : MaskFamilyCode mask packet rows U)
    (ds : List P1TopDownPaidReusable.Datum) (fuel : Nat)
    (H H' : Fin U → Nat) (A A' : Fin U → List Bool) : Prop :=
  ∃ (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows,
      Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps),
  RowCaps.Good selector a printer r layout facts caps ∧
  ds=dataList a (r.family a) (geometryOf selector a r) layout facts ∧
  ∃ (poolReserve : Fin 373 → Nat)
    (familyReserve : Fin (rowTapes printer rows.privateWork+1) → Nat)
    (poolH : Fin U → Nat) (poolA : Fin U → List Bool)
    (ambientH : Fin U → Nat) (ambientA : Fin U → List Bool)
    (seedFuel setupLoadFuel finishFuel rewindCap descriptorReserve : Nat),
  let s := rows.state r layout facts caps
  let final := PCJ38fbfed565f64139_Family.exit printer
    (PCJ38fbfed565f64139_Ready.code rows.program) a (r.family a)
    (geometryOf selector a r) layout facts s
  let finalH := dockH p.familySlots ambientH final.heads
  let finalA := install p.familySlots ambientA
    (fun i => ZeroPadding.pad (familyReserve i) (final.tapes i))
  let pos := (PCJ38fbfed565f64139_Cached.descriptorWord printer ds).length
  let word := ZeroPadding.pad descriptorReserve
    (PCJ38fbfed565f64139_Cached.descriptorWord printer ds)
  let rewindReserve : Fin 3 → Nat := ![0,0,rewindCap]
  p.seed.Ready r seedFuel H
    (dockH p.poolSlots poolH (fun _ => 0)) A
    (install p.poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.input (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) i))) ∧
  Step p.setupLoad setupLoadFuel
    (dockH p.poolSlots poolH (fun _ => 0))
    (install p.poolSlots poolA (fun i => ZeroPadding.pad (poolReserve i)
      (BinaryCacheColdRun.output (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) i)))
    (dockH p.familySlots ambientH (fun _ => 0))
    (install p.familySlots ambientA (fun i => ZeroPadding.pad (familyReserve i)
      (rowPublicInput selector a printer rows.privateWork r layout caps i))) ∧
  pos ≤ rewindCap ∧
  (∀ i, finalH (p.rewindSlots i)=
    (CompetitorRecordRewind.cfg 0 word pos rewindCap 0 0 []).heads i) ∧
  (∀ i, finalA (p.rewindSlots i)=ZeroPadding.pad (rewindReserve i)
    ((CompetitorRecordRewind.cfg 0 word pos rewindCap 0 0 []).tapes i)) ∧
  Step p.finish finishFuel
    (dockH p.rewindSlots finalH
      (CompetitorRecordRewind.cfg 2 word 0 rewindCap 0 0 (List.replicate rewindCap false)).heads)
    (install p.rewindSlots finalA (fun i => ZeroPadding.pad (rewindReserve i)
      ((CompetitorRecordRewind.cfg 2 word 0 rewindCap 0 0 (List.replicate rewindCap false)).tapes i)))
    H' A' ∧
  seedFuel+1+(BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a))+1+
    (setupLoadFuel+1+rowInitBudget a rows.coefficient rows.degree r layout.w layout.degree layout.C caps))+1+
    (PCJ38fbfed565f64139_Family.budget printer (r.family a) s+1+
      (2*rewindCap+2+1+finishFuel)) ≤ fuel

end
end PCJc4297ab269d8423a_Source
