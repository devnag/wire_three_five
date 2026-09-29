import Proof.CaseAnalysis.FinalTailCompose
import Proof.CaseAnalysis.FinalVerdict

/-! # T3(ii) — the two field-level bridges `Verdict` needs from the composition

`C10Verdict.Verdict` wants its three `Realizes` **at the composed machine's own
run**.  Every field of `Realizes` except `heads`, `exit`, `run` and `hencoded` is
a statement about the paper's expansion and says nothing about which machine
produced it (`Realizes`, P2): `transport` is that observation, so the semantic
work (S2's `realizes_of_stage`, W1's `worker_realizes`) is done once, at
whatever machine is convenient, and re-hung on the composition's `Step`.

`bound_penalty` / `bound_moment` / `bound_clause` are the other bridge: T2's
`tail_step` states its verdict over `ℚ` with `CompetitorThresholdDecision.estimate`,
while `Verdict.accepts_iff` states it over `ℝ` with `Estimate.value` and
`C10Verdict.bound`.  The two are the same statement — `Estimate.value` IS
`estimate a.positive a.negative a.denominator` definitionally — and these three
lemmas say so, so `accepts_iff` is `verdict_run_of_records` verbatim. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeVerdict

open LocalBitMultitape ExtDecompositionBatch
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces
open CloseoutRowsOriginalSchedule (Phase)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- **The machine-independent half of `Realizes`, re-hung on another run.**
`ι index coefficient circuits estimate failure mass hfailure hexpansion hpoint
hmass hbudget result hvalid hvaluesum` mention no machine; only
`heads exit run hencoded` do. -/
def transport {t s t' s' : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    {source : PointwisePCPPAlgorithm} {ph : Phase} {constants : Constants source}
    {pcpp : PointwisePCPP circuit}
    {proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes ph constants pcpp proofValue evaluate p budget hin tin port width)
    {p' : Machine t' s'} {budget' : ℕ} {hin' : Fin t' → ℕ} {tin' : Fin t' → List Bool}
    {port' : Fin t'} (heads' : Fin t' → ℕ) (exit' : Fin t' → List Bool)
    (run' : Step p' budget' hin' tin' heads' exit')
    (hencoded' : exit' port' =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord width R.result 1 1) :
    Realizes ph constants pcpp proofValue evaluate p' budget' hin' tin' port' width where
  ι := R.ι
  index := R.index
  coefficient := R.coefficient
  circuits := R.circuits
  estimate := R.estimate
  failure := R.failure
  mass := R.mass
  hfailure := R.hfailure
  hexpansion := R.hexpansion
  hpoint := R.hpoint
  hmass := R.hmass
  hbudget := R.hbudget
  heads := heads'
  exit := exit'
  run := run'
  result := R.result
  hvalid := R.hvalid
  hencoded := hencoded'
  hvaluesum := R.hvaluesum

/-- The transported `Realizes` keeps the estimate, so `Verdict.hestimate` is
`rfl` and `Verdict.hshared` is `rfl`. -/
@[simp] theorem transport_result {t s t' s' : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm} {ph : Phase}
    {constants : Constants source} {pcpp : PointwisePCPP circuit}
    {proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes ph constants pcpp proofValue evaluate p budget hin tin port width)
    {p' : Machine t' s'} {budget' : ℕ} {hin' : Fin t' → ℕ} {tin' : Fin t' → List Bool}
    {port' : Fin t'} (heads' : Fin t' → ℕ) (exit' : Fin t' → List Bool)
    (run' : Step p' budget' hin' tin' heads' exit')
    (hencoded' : exit' port' =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord width R.result 1 1) :
    (transport R heads' exit' run' hencoded').result = R.result := rfl

@[simp] theorem transport_exit {t s t' s' : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm} {ph : Phase}
    {constants : Constants source} {pcpp : PointwisePCPP circuit}
    {proofValue : BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes ph constants pcpp proofValue evaluate p budget hin tin port width)
    {p' : Machine t' s'} {budget' : ℕ} {hin' : Fin t' → ℕ} {tin' : Fin t' → List Bool}
    {port' : Fin t'} (heads' : Fin t' → ℕ) (exit' : Fin t' → List Bool)
    (run' : Step p' budget' hin' tin' heads' exit')
    (hencoded' : exit' port' =
      CloseoutRowsEstimatorCoefficients.Stream.recordWord width R.result 1 1) :
    (transport R heads' exit' run' hencoded').exit = exit' := rfl

/-! ## The three thresholds: T2's `ℚ` verdict IS `Verdict`'s `ℝ` verdict -/

end
end NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeVerdict
