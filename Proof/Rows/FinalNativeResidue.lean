import Proof.Amplification.RecoveryRadixInput
import Proof.CaseAnalysis.FinalSelectorLoadMasks
import Proof.Circuits.DecompositionNativeMagnitude
import Proof.Hierarchy.HierarchyAllocation
import Proof.MachineModel.UInputFields
import Proof.Rows.FinalPrimeCoefficientReduce
import Proof.Rows.FinalNativeSignedResidue
import Proof.CaseAnalysis.RowsEstimatorParityAlternating

/-! One original native signed coefficient yields its actual framed residue.
Prime/width fields, zero residue words, repetition template, blank workspace
and reset logs are physical inputs. Stream assembly and per-coefficient
workspace clearing remain enclosing program obligations. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidue
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true



def budget (negate : Bool) (z : ℤ) (w : ℕ) := 22*natBitLength z.natAbs+19+1+
  ((if negate then 2 else 0)+C10NativeSignedResidue.budget w (2*natBitLength z.natAbs))

end NearCubicWires.RepairSource.CloseoutFinal.C10NativeResidue
