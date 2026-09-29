import Proof.CaseAnalysis.RowsCircuitPadding
import Proof.CaseAnalysis.RowsCircuitSymmetricRun
import Proof.CaseAnalysis.RowsCircuitThresholdRun
import Proof.CaseAnalysis.WitnessTermLoopData
import Proof.CaseAnalysis.WitnessTermRoundAll

/-! Both actual circuit programs supply the existing counted term/family
consumer, with original decoder guards and no circuit serialization. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermSupplier
open LocalBitMultitape CloseoutWitness CanonicalWitnessCodec RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def symmetricFlag (core W L : ℕ) (bits : List Bool) : Bool:=
  match decodeNormalizedSymmetricThresholdCircuit core (value (TermCoefficient.circuitCode bits)) with
  | none=>false
  | some c=>decide (c.wireCount ≤ W ∧ c.descriptionBits ≤ L)
noncomputable def thresholdFlag (core W L : ℕ) (bits : List Bool) : Bool:=
  match decodeNormalizedThresholdThresholdCircuit core (value (TermCoefficient.circuitCode bits)) with
  | none=>false
  | some c=>decide (c.wireCount ≤ W ∧ c.descriptionBits ≤ L)

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTermSupplier
