import Mathlib.Data.List.GetD
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerCold
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizedRing
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Packets.SubstitutionOuterData
import Proof.Packets.SubstitutionScan
import Proof.Packets.PacketsXLiteralAlphabet
import Proof.Packets.NormalizedAdditionData
import Proof.Packets.PacketsXCycleSerializedCost

/-! Semantic bounds at the actual substitution scan boundaries. All selected
indices come from bits physically read in the original monomial mask; distinct
selected codes form a subset of that monomial. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCensus
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport Theorem25Completion.CycleBounds

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCensus
