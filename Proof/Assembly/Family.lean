import Proof.Assembly.Row

/-! The exact external-row family, with one fixed row body and a paid runtime
repeat driver. Each normalized packet family is consumed once; the descriptor
only grows. The terminal and zero-row cases use the existing driver rewind. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ38fbfed565f64139_Family
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed
attribute [local irreducible] P1TopDownPaidPayload.tapes
namespace Row
abbrev Code := PCJ38fbfed565f64139_Row.Code
abbrev Banks := PCJ38fbfed565f64139_Row.Banks
end Row
noncomputable section

variable {q L t : Nat} (printer : WilliamsAlgorithm) (c : Row.Code printer t)
  (a : DecompositionAlgorithm) (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g) (facts : ∀ r ∈ F.rows, Packets.PacketFacts a F g r)

def rawWord (r : Packets.Row F.occurrences L) :=
  (Packets.packets a F g r).flatMap P1CompactNativeFamily.rawWord

def rawBefore (j : Nat) := (F.rows.take j).flatMap (rawWord a F g)
def rawAfter (j : Nat) := (F.rows.drop (j+1)).flatMap (rawWord a F g)

def words := (dataList a F g layout facts).map (P1TopDownPaidReusable.Datum.word printer)
def emit (j : Nat) := (words printer a F g layout facts).getD j []

def rowAt (j : Fin F.rows.attach.length) := F.rows.attach[j.val]

/-- Runtime bank fields, all bound to one family and row index. Code remains in c. -/
structure State where
  heads : Nat → List Bool → Fin t → Nat
  tapes : Nat → List Bool → Fin t → List Bool
  headerReserve : Nat → Fin 440 → Nat
  descriptorReserve : Nat → Nat
  headerHeads : Nat → List Bool → Fin t → Nat
  headerTapes : Nat → List Bool → Fin t → List Bool
  frameHeads : Nat → List Bool → Fin t → Nat
  frameTapes : Nat → List Bool → Fin t → List Bool
  fieldReserve : Nat → Fin (P1TopDownPaidPayload.tapes printer) → Nat
  copyCap : Nat → Nat
  prepareFuel : Nat → Nat
  completeFuel : Nat → Nat
  cleanupFuel : Nat → Nat
  rowFuel : Nat

variable (s : State (t:=t) printer)

def rowBanks (j : Nat) (out : List Bool) : Row.Banks printer t where
  entryH := s.heads j out
  entryA := s.tapes j out
  headerReserve := s.headerReserve j
  descriptorReserve := s.descriptorReserve j
  headerH := s.headerHeads j out
  headerA := s.headerTapes j out
  frameH := s.frameHeads j out
  frameA := s.frameTapes j out
  fieldReserve := s.fieldReserve j
  copyCap := s.copyCap j
  exitH := s.heads (j+1) (out++emit printer a F g layout facts j)
  exitA := s.tapes (j+1) (out++emit printer a F g layout facts j)
  prepareFuel := s.prepareFuel j
  completeFuel := s.completeFuel j
  cleanupFuel := s.cleanupFuel j

def rowConfig (j : Nat) (out : List Bool) :=
  (⟨(PCJ38fbfed565f64139_Row.machine c).start,s.heads j out,s.tapes j out⟩ : Configuration t _)

def entry := RepeatMachine.cfg 0 (rowConfig printer c s 0 []) F.rows.attach.length 1

end
end PCJ38fbfed565f64139_Family
