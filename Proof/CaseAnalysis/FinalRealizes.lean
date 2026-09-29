import Proof.CaseAnalysis.FinalStability

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairRepresentation
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- **One phase of the C.10 weak machine, realized by one run of one machine.**
The estimation ledger and the physical receipt are FUSED: a correct-but-
detached half cannot typecheck, because `hvaluesum` forces the encoded output
to be the expansion's estimated value and `hexpansion` forces the expansion to
be the paper's grouped phase mean. -/
structure Realizes {t s : ℕ} {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    {source : PointwisePCPPAlgorithm}
    (ph : CloseoutRowsOriginalSchedule.Phase) (constants : Constants source)
    (pcpp : PointwisePCPP circuit)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (evaluate : Atom → BitInput n → Bool)
    (p : Machine t s) (budget : ℕ) (hin : Fin t → ℕ) (tin : Fin t → List Bool)
    (port : Fin t) (width : ℕ) where
  /-- The expansion's index type -- the monomial positions. -/
  ι : Type
  index : Finset ι
  coefficient : ι → ℝ
  circuits : ι → List Atom
  estimate : ι → ℝ
  failure : ℝ
  mass : ℝ
  hfailure : 0 ≤ failure
  /-- **The paper's grouped phase mean IS this finite AND-four expansion.** -/
  hexpansion :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      ∑ i ∈ index, coefficient i * conjunctionProbability evaluate (circuits i)
  /-- The supplier answers every call within `failure`. -/
  hpoint : ∀ i ∈ index,
    |estimate i - conjunctionProbability evaluate (circuits i)| ≤ failure
  /-- The coefficient-mass ledger. -/
  hmass : (∑ i ∈ index, |coefficient i|) ≤ mass
  /-- Paper C.10.2: the propagated estimation error is below `eps_est`. -/
  hbudget :
    failure * mass ≤ ((estimationTolerance constants (zeta constants) : ℚ) : ℝ)
  heads : Fin t → ℕ
  exit : Fin t → List Bool
  /-- The physical receipt: ONE run, at this budget, from these tapes. -/
  run : Step p budget hin tin heads exit
  result : CompetitorValidity.Estimate
  hvalid : result.Valid width
  /-- The machine's OUTPUT, pinned by the corpus's own ENCODER. -/
  hencoded :
    exit port = CloseoutRowsEstimatorCoefficients.Stream.recordWord width result 1 1
  /-- The encoded output IS the expansion's estimated value. -/
  hvaluesum :
    ((result.value : ℚ) : ℝ) = ∑ i ∈ index, coefficient i * estimate i

theorem accurate_of_realizes {t s : ℕ} {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} {source : PointwisePCPPAlgorithm}
    {ph : CloseoutRowsOriginalSchedule.Phase} {constants : Constants source}
    {pcpp : PointwisePCPP circuit}
    {proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ}
    {evaluate : Atom → BitInput n → Bool}
    {p : Machine t s} {budget : ℕ} {hin : Fin t → ℕ} {tin : Fin t → List Bool}
    {port : Fin t} {width : ℕ}
    (R : Realizes ph constants pcpp proofValue evaluate p budget hin tin port
      width) :
    |((R.result.value : ℚ) : ℝ) -
        CloseoutRowsOriginalSchedule.mean ph pcpp proofValue| ≤
      ((estimationTolerance constants (zeta constants) : ℚ) : ℝ) := by
  rw [R.hvaluesum, R.hexpansion]
  exact le_trans
    (componentwise_real_error R.index R.coefficient
      (fun i => conjunctionProbability evaluate (R.circuits i)) R.estimate
      R.failure R.mass R.hfailure R.hpoint R.hmass)
    R.hbudget

/-! ## The three `Exposes` conjuncts -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
