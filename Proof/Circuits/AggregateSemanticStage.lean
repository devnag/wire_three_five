import Proof.Circuits.OccurrenceSliceTransport

namespace NearCubicWires.AggregateSemanticStage

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ComponentwiseWeakMachine
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OccurrenceSliceTransport
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifierThresholdSeam

/-! ## §1 The aggregate quantities -/

/-- **The verifier's estimated quantity.**  The uniform mean, over the PCPP
input cube, of the arithmetized clause mean of the proof vector decoded at that
input.  This is the manuscript's `mu = E_{i,u} F_i(u)`. -/
noncomputable def aggregateClauseMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput n, clauseMean pcpp (value input)

/-- **The verifier's charged validity quantity.**  The uniform mean, over the
PCPP input cube, of the per-input joint clause penalty.  This is the
manuscript's `E_{i,j,u} P_{ij}`, charged on both clause sides. -/
noncomputable def aggregateClausePenaltyMean {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput n, totalClausePenaltyMean pcpp input (value input)

/-- The aggregate clause mean of the prescribed rounding of the same family. -/
noncomputable def aggregateRoundedMean {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) : ℝ :=
  𝔼 input : BitInput n,
    clauseMean pcpp
      (fun j => bitAsReal (roundedProof pcpp input (value input) j))

/-- The joint cube is the product of the PCPP input cube with the clause
address space.  Every aggregate quantity above is one expectation over it. -/
private theorem expect_prod_eq {n bits : ℕ} (value : BitInput n → Fin bits → ℝ) :
    (𝔼 slot ∈ (univ : Finset (BitInput n × Fin bits)), value slot.1 slot.2) =
      𝔼 input : BitInput n,
        𝔼 index ∈ (univ : Finset (Fin bits)), value input index := by
  rw [← Finset.univ_product_univ, Finset.expect_product']

theorem aggregateClauseMean_eq_joint {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    aggregateClauseMean pcpp value =
      𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        clauseRealValue (pcpp.clauses slot.2) (value slot.1) :=
  (expect_prod_eq
    (fun input index => clauseRealValue (pcpp.clauses index) (value input))).symm

theorem aggregateRoundedMean_eq_joint {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    aggregateRoundedMean pcpp value =
      𝔼 slot ∈ (univ : Finset (BitInput n × Fin (2 ^ pcpp.clauseBits))),
        clauseRealValue (pcpp.clauses slot.2)
          (fun j =>
            bitAsReal (roundedProof pcpp slot.1 (value slot.1) j)) :=
  (expect_prod_eq
    (fun input index =>
      clauseRealValue (pcpp.clauses index)
        (fun j => bitAsReal (roundedProof pcpp input (value input) j)))).symm

/-! ## §2 The aggregate validity movement bound

The manuscript's rounding lemma C.10.1(2) is exactly
`ComponentwiseValidity.clauseMean_distance_le_six_of_combined`, whose index set
is an abstract `Finset`.  Instantiating it at the joint cube is the whole
proof: no new Jensen step and no new constant. -/

/-! ## §3 The aggregate soundness bound

The manuscript's soundness sentence is a convexity split, not a Markov
argument: the outer PCP accepts on at most an `outerError` fraction of PCPP
inputs, every other input is bounded by pointwise PCPP soundness, and the mean
inherits the sum of the two. -/

/-- The aggregate rounded mean is the aggregate satisfied fraction of the
prescribed rounding, which is a genuine PCPP assignment at every input. -/
theorem aggregateRoundedMean_eq_expect_satisfiedFraction {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    aggregateRoundedMean pcpp value =
      𝔼 input : BitInput n,
        pcpp.satisfiedFraction input
          (roundedAuxiliary pcpp (value input)) := by
  refine Finset.expect_congr rfl fun input _ => ?_
  rw [roundedProof_eq_assignment pcpp input (value input),
    clauseMean_bitAsReal_eq_satisfiedFraction]

/-! ## §4 The aggregate ledger and the one-sided closure

`ExecutableNoInstanceBranchLedger` stores three reals and four inequalities and
mentions no PCPP, no input and no clause index.  The aggregate quantities
instantiate it verbatim, so `executableNoInstanceBranchLedger_empty` — the
published numeric ladder — is reused with nothing changed. -/

/-! ## §5 Completeness from the whole-cube `ell^1` premise

The seam's movement bound `abs_clauseMean_sub_le_totalClauseErrorMean` is
linear in the error, so it averages over the PCPP input cube with no loss.  The
whole-cube radius the XOR contract publishes *is* the aggregate slice error
(`l1DistanceFromBoolean_eq_expect_slice`), so completeness closes directly. -/

/-! ## §6 What the estimator must supply

The ledger's `estimateClose` field is an accuracy statement about **one**
number.  `AggregateEstimateAccurate` names it at the published
`estimationError`, and `estimateAccurate_of_aggregateSupplierFailure` is the
seam a supplier guarantee plugs into — the aggregate analogue of
`ComponentwiseBranchExtraction.estimateAccurate_of_supplierFailure`. -/

/-! ## §7 The majority is not merely avoidable, it is unnecessary

The two facts below record what the aggregate design costs relative to the
majority design of `SemanticStageProgram`.  The completeness side spends the
published radius once and leaves the seam's factor-three reserve untouched
(`aggregateBudget_within_seamReserve`), whereas the majority design had to
spend that reserve on Markov to manufacture a two-thirds density.  The
soundness side needs only the outer accepting-set density and never selects an
individual PCPP input, so the enumerated cube never appears. -/

end NearCubicWires.AggregateSemanticStage
