import Mathlib.Tactic
import Proof.CaseAnalysis.RowsEstimatorSubstitutionMonomial
import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterRun
import Proof.CaseAnalysis.RowsFamilyBudget
import Proof.MachineModel.CanonicalFourfoldRowProgram
import Proof.Packets.CycleCommonReserve
import Proof.Packets.NativeNormalized
import Proof.Packets.NormalizedAdditionData
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.PacketsXCycleSerializedCost
import Proof.Packets.PacketsXLiteralCache
import Proof.Packets.PacketsXWindowPositionalSupport
import Proof.Packets.PacketsXWindowProviderPolynomial
import Proof.Packets.PacketsXWindowRawMeaning
import Proof.Packets.WindowSourceClose

/-! Close the actual emitted window, physically rewind it, run the exact
bounded polynomial pipeline and return the outer-loop driver to head zero. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.CanonicalFourfoldRowProgram
open CloseoutRowsRawPairSeek (cacheWord)
open NormalizedFiniteTransport WindowNativeOrder SubstitutionCensus Theorem25Completion.CycleBounds

noncomputable def lower := PhysicalIndexReload.move (95 : Fin 256) .left

attribute [local irreducible] closeSource polynomial lower

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
