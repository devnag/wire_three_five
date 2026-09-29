import Proof.Rows.RowsPoolMinimumPaper

/-! The missing X/C frozen-gate computation: retain the original arity,
zero live weights and shift the strict threshold by the minimum live score.
Only original fields, membership and bounded workspace are inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGate
open LocalBitMultitape RepairOrdinary RecoveryRootRound RecoveryExecution ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal VerifierDecoding
open SupplierPipeline CloseoutRowsPoolWeight

noncomputable def score := C10NaturalHardwireScoreInputs.negative
noncomputable def scoreTarget := Composition.machine score (TapeEmbedding.machine 5 C10NaturalHardwireTarget.machine)

def data (xs : List Item) (z : Int) (tail backing out : List Bool) (w C D E : Nat) : Fin 48 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool)
    (C10NaturalHardwireScoreInputs.data (word xs++intWord z++tail) (mask xs) out w C D xs.length 0 0)
    (HardwireChild.extra backing (mask xs) xs.length E)
noncomputable def weights := RecoveryFocus.machine HardwireChild.weightSlots
  (MaskedReset.machine CloseoutRowsPoolWeight.loop HardwireChild.resetWeights)
noncomputable def machine := Composition.machine weights (TapeEmbedding.machine 4 scoreTarget)

end NearCubicWires.P1Closure.ConstantGate
