import Proof.Assembly.Parent
import Proof.MachineModel.ClosureCompactFamily

/-! The actual normalized packets through the fixed cold header writer.
Every cache, dimension word and raw packet byte is an entry requirement.
The theorem pays the complete metadata and family writer budget, specifies
all final heads/tapes, and identifies the actual Datum header port. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJcc051fd4c1bd4540_Header
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtIncidence NearCubicWires.ExtDecompositionBatch
open NearCubicWires.P1Closure NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed
noncomputable section

variable {q L : Nat} (a : DecompositionAlgorithm) (F : Packets.Family q L)
  (g : Packets.Geometry F) (layout : Packets.Layout a F g)
  (r : Packets.Row F.occurrences L) (hr : r ∈ F.rows)
  (facts : Packets.PacketFacts a F g r)

abbrev machine := CompactColdFamily.machine

abbrev radix := Packets.radix a F g layout

noncomputable def input (out pre tail : List Bool) : Fin 440 → List Bool :=
  letI := radix a F g layout
  CompactNativeInitialize.input (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r).length
    (pre++(Packets.packets a F g r).flatMap P1CompactNativeFamily.rawWord++tail) out

noncomputable def finalHeads (out pre tail : List Bool) : Fin 440 → Nat :=
  letI := radix a F g layout
  CompactColdFamily.finalHeads (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r) out pre tail

noncomputable def finalTapes (out pre tail : List Bool) : Fin 440 → List Bool :=
  letI := radix a F g layout
  CompactColdFamily.finalTapes (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r) out pre tail

noncomputable def budget : Nat :=
  letI := radix a F g layout
  CompactColdFamily.budget (Packets.pool a F g) ((Packets.live F).card+1)
    layout.w (Packets.packets a F g r)

end
end PCJcc051fd4c1bd4540_Header
