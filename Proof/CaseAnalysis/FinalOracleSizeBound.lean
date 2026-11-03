import Proof.CaseAnalysis.FinalStageContracts
import Proof.CaseAnalysis.FinalEncoder
import Proof.CaseAnalysis.SelectedClauses
import Proof.CaseAnalysis.NativeWidthPolynomial
import Proof.Hierarchy.CompetitorWitnessTripleSemantics
import Proof.MachineModel.OrdinarySignedSortKey
import Proof.Foundations.BooleanCircuitSizePadding

namespace NearCubicWires.RepairSource.CloseoutFinal.C10OracleSizeBound

open SourceInterfaces RepairRepresentation RepairOrdinary
open RepairOrdinary.CloseoutWitness CanonicalWitnessCodec ExecutableInterfaces
open SupplierPipeline CircuitRestriction
open RecoveryScheduleEnvelope SelectedRecoveryIntegration CloseoutLanguage
open PolynomialSchedule

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §0  The raw decoder, and the gate unfolded once -/

/-- **The RAW decoder, made total.**  `decodeBooleanCircuit`
(`Proof/Circuits/CanonicalWitnessCodec.lean`) with the same total fallback the
pre-gate `oracleOf` used.  It carries NO size test: the paper's "size-\(q^G\)"
guard is a property of the GUESS the machine accepts, not of the codec.  Every
negative in §2 is about THIS function. -/
def decodedOracle (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (n : ℕ) (bits : List Bool) :
    BooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n) :=
  (decodeBooleanCircuit ((outer sources k clock).result.pcp.nativeWidth n)
    (RadixSemantics.value (BoundedFields.oracle bits))).getD
      (C10TotalDecode.trivialCircuit ((outer sources k clock).result.pcp.nativeWidth n))

/-- **The gate, unfolded once.**  `oracleOf`
(`Proof/CaseAnalysis/FinalTotalDecode.lean`) is the raw decoder followed by the
machine's own size test, `paper.tex:4292`: "It deterministically rejects a branch
if ... it fails the fixed general-circuit size bound." -/
theorem oracleOf_eq_if (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) (bits : List Bool) :
    C10TotalDecode.oracleOf sources k clock oracleDegree n bits =
      (if (decodedOracle sources k clock n bits).size ≤
            oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)
        then decodedOracle sources k clock n bits
        else C10TotalDecode.trivialCircuit ((outer sources k clock).result.pcp.nativeWidth n)) :=
  rfl

/-! ## §1  A decodable circuit above any cap -/

/-! ## §2  The refutation, at the object it is about: the raw decoder -/

/-! ## §3  What the gate buys: the pinned branch, and then the cap outright -/

/-- **The cap, for EVERY witness.**  Both branches of the gate are inside it: the
accepted one by the test itself, the rejected one because `trivialCircuit` has
size `1` and `oracleSizeBound` is `pairClock`
(`Proof/Foundations/RecoveryScheduleEnvelope.lean`), positive at positive width by
`pairClock_positive` (`Proof/Foundations/PolynomialClock.lean`).  A positive native
width is the whole residual. -/
theorem oracleOf_size_le_cap (sources : EightSources) (k : ℕ)
    (clock : OrdinaryClock (fun n => n^(k+2))) (oracleDegree n : ℕ) (bits : List Bool)
    (hwidth : 0 < (outer sources k clock).result.pcp.nativeWidth n) :
    (C10TotalDecode.oracleOf sources k clock oracleDegree n bits).size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n) := by
  by_cases hle : (decodedOracle sources k clock n bits).size ≤
      oracleSizeBound oracleDegree ((outer sources k clock).result.pcp.nativeWidth n)
  · rw [oracleOf_eq_if, if_pos hle]
    exact hle
  · rw [oracleOf_eq_if, if_neg hle]
    have hone : (C10TotalDecode.trivialCircuit
        ((outer sources k clock).result.pcp.nativeWidth n)).size = 1 := rfl
    rw [hone]
    exact PolynomialClock.pairClock_positive _ _ hwidth

/-! ## §4  The payoff, at the live `pcppOf` -/

/-! ## §5  The completeness branch, with no residual premise -/

end
end NearCubicWires.RepairSource.CloseoutFinal.C10OracleSizeBound
