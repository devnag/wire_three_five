import Mathlib.Algebra.Order.Floor.Semifield
import Proof.CaseAnalysis.RawRowsThresholdAccuracy
import Proof.CaseAnalysis.WitnessSelectedSourceRequest
import Proof.MachineModel.CappedConsumer

/-! Paper C.10's honest typed witnesses pass the actual bounded cold flag.
Both modes use the same frozen positive denominator, so the paper may choose
its wire coefficient after choosing the saving constants. A fixed outer onset absorbs the native guard
and padded-arity cutoffs; it does not change the earlier cold cutoff.
This proves admission, not the remaining physical worker/continuation run. -/
namespace NearCubicWires.P1Independent.CappedLegalAdmission
open RepairSource RepairSource.CloseoutFinal
open RepairOrdinary RepairOrdinary.CloseoutWitness SourceInterfaces RepairRepresentation
open SelectedRecoveryIntegration CanonicalWitnessCodec SupplierPipeline
open CloseoutLanguage CompetitorRationalGap CappedConsumer C10TotalDecode
open CloseoutWitness.SelectedSource

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) {gamma : ℝ} (p : Parameters sources gamma) (W : WorkerData)

/-- Exactly the boolean retained by bounded_cache and bounded_zero. -/
def passed (coldCutoff : ℕ) (n : ℕ) (x : BitInput n) (bits : List Bool) : Bool :=
  BoundedFamily.passed (fixedProjection sources) (selectedPCPP sources) W.k
    (hierarchy sources W.k W.clock).coefficient (padding sources W.k W.clock)
    coldCutoff p.clauseDegree p.degree p.copies W.den W.den (zeta (constantsOf sources))
    (code sources W.k W.clock) x bits (Nat.le_max_right _ _)

end
end NearCubicWires.P1Independent.CappedLegalAdmission
