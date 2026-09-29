import Proof.Foundations.PhysicalHardness
import Proof.Foundations.ThresholdDAGCompilation

/-!
# Boolean-hard-core recovery for the two physical threshold families

The recovery dichotomy produces hardness against ordinary Boolean circuits.
This module applies the verified shared-DAG simulations once, for both physical
families, and then reuses the unique factor-27 padding theorem.  The remaining
premises are explicit numeric comparisons between the Boolean size cap and the
two desired physical wire caps; no semantic or headline witness is accepted.
-/

namespace NearCubicWires.PhysicalRecovery

open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.PhysicalHardness
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.ThresholdDAGSimulation
open NearCubicWires.WireScaleTransfer

theorem symmetricAverageHard_of_boolean
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily) (wireCap : ℕ)
    (hsize :
      40 * (core.arity + wireCap + 2) ^ 4 ≤ core.size) :
    AverageHardAt symmetricWireFamily core.function
      wireCap core.advantage := by
  intro candidate hcandidate
  rcases hcandidate with ⟨source, hwires, heval⟩
  rcases simulateSymmetricThresholdCircuit normalization source with
    ⟨circuit, hcircuitEval, hcircuitSize⟩
  apply core.hard candidate
  refine ⟨circuit, ?_, ?_⟩
  · apply hcircuitSize.trans
    apply hsize.trans'
    gcongr
  · exact hcircuitEval.trans heval

theorem thresholdAverageHard_of_boolean
    (normalization : ThresholdNormalizationContract)
    (core : HardCore booleanCircuitFamily) (wireCap : ℕ)
    (hsize :
      50 * (core.arity + wireCap + 2) ^ 4 ≤ core.size) :
    AverageHardAt thresholdWireFamily core.function
      wireCap core.advantage := by
  intro candidate hcandidate
  rcases hcandidate with ⟨source, hwires, heval⟩
  rcases simulateThresholdThresholdCircuit normalization source with
    ⟨circuit, hcircuitEval, hcircuitSize⟩
  apply core.hard candidate
  refine ⟨circuit, ?_, ?_⟩
  · apply hcircuitSize.trans
    apply hsize.trans'
    gcongr
  · exact hcircuitEval.trans heval

end NearCubicWires.PhysicalRecovery
