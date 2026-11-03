import Proof.Packets.PacketsXWindowSeedEmit
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Tactic
import Proof.CaseAnalysis.RowsModeWindowBinomial
import Proof.Packets.PacketsXDescendingWindowLoop
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Supplier.RowTupleSubsets
import Proof.Packets.WindowProviderPorts

/-! The actual cold/reentry seed and nested window emitter in the fixed
256-tape provider. All metadata comes from its retained numeric masters. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

def seedPorts : Fin 69→Fin 256 := Fin.addCases (m:=62) (n:=7) windowPorts ![180,181,182,183,184,185,152]

attribute [local irreducible] WindowSeed.complete
noncomputable def seedEmit := RecoveryFocus.machine seedPorts WindowSeed.complete

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
