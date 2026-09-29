import Proof.Assembly.FramingSpec
import Proof.Assembly.Header

/-! A fixed physical row transaction. The header writer and complete descriptor
framer are closed programs. The three remaining stages are shared ordinary
machines, with explicit full-bank joins and their own paid fuel. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ38fbfed565f64139_Row
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section
namespace Frame
abbrev fields := PCJeb9c0f0306e9481c_FramingSpec.datumFields
abbrev heads := PCJeb9c0f0306e9481c_FramingSpec.heads
abbrev bank {t : Nat} := @PCJeb9c0f0306e9481c_FramingSpec.paddedBank t
abbrev machine := PCJeb9c0f0306e9481c_FramingSpec.datumMachine
abbrev budget := PCJeb9c0f0306e9481c_FramingSpec.datumBudget
def targetReserve (t reserve : Nat) (i : Fin (t+2)) : Nat :=
  if i.val=t then reserve else 0
end Frame

/-- Chosen with the source-global ordinary code, before every row/input. -/
structure Code (printer : WilliamsAlgorithm) (t : Nat) where
  prepareStates : Nat
  prepare : Machine t prepareStates
  completeStates : Nat
  complete : Machine t completeStates
  cleanupStates : Nat
  cleanup : Machine t cleanupStates
  headerSlots : Fin 440 → Fin t
  headerInjective : Function.Injective headerSlots
  frameSlots : Fin (P1TopDownPaidPayload.tapes printer+2) → Fin t
  frameInjective : Function.Injective frameSlots

def machine {printer : WilliamsAlgorithm} {t : Nat} (c : Code printer t) :=
  Composition.machine c.prepare
    (Composition.machine (RecoveryFocus.machine c.headerSlots PCJcc051fd4c1bd4540_Header.machine)
      (Composition.machine c.complete
        (Composition.machine (RecoveryFocus.machine c.frameSlots (Frame.machine printer)) c.cleanup)))

/-- Full states at the joins; these are specified by the enclosing runtime input.
They are not precomputed advice: Ready requires the actual producing Steps. -/
structure Banks (printer : WilliamsAlgorithm) (t : Nat) where
  entryH : Fin t → Nat
  entryA : Fin t → List Bool
  headerReserve : Fin 440 → Nat
  descriptorReserve : Nat
  headerH : Fin t → Nat
  headerA : Fin t → List Bool
  frameH : Fin t → Nat
  frameA : Fin t → List Bool
  fieldReserve : Fin (P1TopDownPaidPayload.tapes printer) → Nat
  copyCap : Nat
  exitH : Fin t → Nat
  exitA : Fin t → List Bool
  prepareFuel : Nat
  completeFuel : Nat
  cleanupFuel : Nat

variable {q L t : Nat} (printer : WilliamsAlgorithm) (c : Code printer t)
  (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g) (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
  (facts : Packets.PacketFacts a F g r) (b : Banks printer t) (out pre tail : List Bool)

def headerInH := dockH c.headerSlots b.headerH (CompactColdFamily.ambientH [] pre)
def headerInA := install c.headerSlots b.headerA (fun i => ZeroPadding.pad (b.headerReserve i) (PCJcc051fd4c1bd4540_Header.input a F g layout r [] pre tail i))
def headerOutH := dockH c.headerSlots b.headerH (PCJcc051fd4c1bd4540_Header.finalHeads a F g layout r [] pre tail)
def headerOutA := install c.headerSlots b.headerA (fun i => ZeroPadding.pad (b.headerReserve i) (PCJcc051fd4c1bd4540_Header.finalTapes a F g layout r [] pre tail i))
def frameInH := dockH c.frameSlots b.frameH (Frame.heads _ out)
def frameInA := install c.frameSlots b.frameA
  (fun i => ZeroPadding.pad (Frame.targetReserve (P1TopDownPaidPayload.tapes printer) b.descriptorReserve i)
    (Frame.bank b.fieldReserve (Frame.fields printer (Packets.datum a F g layout r hr facts)) out b.copyCap i))
def frameOutH := dockH c.frameSlots b.frameH
  (Frame.heads _ (out++(Packets.datum a F g layout r hr facts).word printer))
def frameOutA := install c.frameSlots b.frameA
  (fun i => ZeroPadding.pad (Frame.targetReserve (P1TopDownPaidPayload.tapes printer) b.descriptorReserve i)
    (Frame.bank b.fieldReserve (Frame.fields printer (Packets.datum a F g layout r hr facts))
      (out++(Packets.datum a F g layout r hr facts).word printer) b.copyCap i))

def budget := b.prepareFuel+1+(PCJcc051fd4c1bd4540_Header.budget a F g layout r+1+
  (b.completeFuel+1+(Frame.budget printer (Packets.datum a F g layout r hr facts)+1+b.cleanupFuel)))

end
end PCJ38fbfed565f64139_Row
