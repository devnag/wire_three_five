import Proof.Assembly.RowProduction

/-! Joint physical layout: the packet output IS the raw Header source, the
ColdRun pool output IS Header's pool port, and descriptors are appended on
the final loader source. Only paid public-word loaders/final joins remain. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJd4d1d9d7d1fa4313_Production
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

structure FamilyCode {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a)
    (rows : RowProducer selector a printer) (U : Nat) where
  familySlots : Fin (rowTapes printer rows.privateWork+1) → Fin U
  familyInjective : Function.Injective familySlots
  poolSlots : Fin 373 → Fin U
  poolInjective : Function.Injective poolSlots
  rewindSlots : Fin 3 → Fin U
  rewindInjective : Function.Injective rewindSlots
  seed : SeedCode packet U
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

def FamilyCode.cached {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} {packet : PacketWriter selector a}
    {rows : RowProducer selector a printer} {U : Nat} (p : FamilyCode packet rows U) :
    PCJ38fbfed565f64139_Cached.Program rows.program U where
  familySlots := p.familySlots
  familyInjective := p.familyInjective
  poolSlots := p.poolSlots
  poolInjective := p.poolInjective
  rewindSlots := p.rewindSlots
  rewindInjective := p.rewindInjective
  directSource := p.sourceAlias
  seedStates := _
  seed := p.seed.machine
  setupStates := _
  setup := Composition.machine p.setupLoad
    (RecoveryFocus.machine p.familySlots rows.initializer)
  finishStates := p.finishStates
  finish := p.finish

end
end PCJd4d1d9d7d1fa4313_Production
