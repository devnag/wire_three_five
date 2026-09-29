import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Std.Tactic
import Proof.Packets.CyclePaletteReserve
import Proof.Packets.MaskSelect
import Proof.Packets.NativeMaskCount
import Proof.Packets.PacketsWriterPlan
import Proof.Packets.PacketsXModeCacheReady
import Proof.Packets.PacketsXNormalizedDegreeCore
import Proof.Packets.PacketsXWalkSeedCleanup
import Proof.Packets.PacketsXWalkTimeLoop
import Proof.Packets.PhysicalStepSupport

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsSeed
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierWalk NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.SupplierListSchedule
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsConstruction

/-! ## Framed words, cell by cell -/

/-! ## The seed field splits into labels, `y`, `x` -/

section Family

end Family

section Ready

end Ready

end NearCubicWires.PacketsSeed
