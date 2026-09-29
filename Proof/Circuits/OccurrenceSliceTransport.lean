import Proof.CaseAnalysis.CaseTwoWitnessCompleteness

/-!
# The occurrence-slice transport of the Case-2 approximation radius

The Case-2 completeness chain of
[`CaseTwoWitnessCompleteness`](Proof/CaseAnalysis/CaseTwoWitnessCompleteness.lean)
delivers exactly one semantic fact about the guessed witness:

```lean
RecoveryWitnessApproximates seed (publishedRecoveryDelta contracts) witness
```

i.e. `l1DistanceFromBoolean seed value ≤ delta` for the scheduled Case-2 seed
`seed = caseTwoSeed …`, which is the honest *occurrence* table of the padded
pointwise PCPP.  The verifier seam of
[`VerifierThresholdSeam`](Proof/PCP/VerifierThresholdSeam.lean) consumes a
different quantity, `clauseOccurrenceErrorMean pcpp value reference`, and that
quantity is charged *at one fixed PCPP input*.

This module is the transport between the two.  It settles the question with an
exact identity and an exact obstruction.

## §0 The answer

The seed's cube is the product

```text
BitInput (inputArity + clauseBits + 1)  ≅
  (PCPP input) × (clause address) × (left/right position)
```

and `l1DistanceFromBoolean` is the uniform mean over *all three* blocks, while
`clauseOccurrenceErrorMean` is the uniform mean over the last two blocks only,
with the first block frozen at one input.  Consequently:

* **`§3` (positive, exact).**  For every fixed PCPP input the two quantities
  agree *exactly*, once the guessed occurrence values are read back to proof
  coordinates by the occurrence-fiber average of their sign-adjusted values:
  `clauseOccurrenceErrorMean_recoveredProofValue`.  Neither the two-occurrence
  aliasing of a shared coordinate nor the literal polarity costs anything —
  the identity is an equality, not an inequality.
* **`§2` (positive, exact).**  The whole-cube distance is the uniform mean of
  the per-input slice distances: `l1DistanceFromBoolean_eq_expect_slice`.
* **`§5` (negative).**  An average over the input block does not bound an
  individual slice: `slice_not_le_of_l1Distance` exhibits a PCPP at one and
  the same radius `1 / 2` for which the whole-cube premise holds and the
  per-input premise fails, and
  `exists_slice_gt_factor_mul_l1Distance` shows the loss factor is the whole
  size `2 ^ inputArity` of the PCPP input space, so no constant rescaling of
  the published radius repairs the transport.
* **`§4` (the repair).**  Markov's inequality on the slice distribution is
  free here, because the seam already runs at a factor-three reserve
  (`threshold_le_estimate_of_occurrenceDelta` closes at `delta ≤ 3 * zeta`
  while the published radius is `repairedRecoveryDelta parameters = zeta`).
  At least *two thirds* of all PCPP inputs satisfy the seam premise:
  `two_thirds_le_card_seamInputs`, and at the published radius
  `two_thirds_le_card_seamInputs_of_repairedDelta`.
* **`§6` (the consequence).**  `threshold_le_estimate_of_sliceInput` is the
  seam with its `hclose` premise discharged at one admissible PCPP input.
  Together with `§4` and `§5` it says what a *per-input* semantic test can and
  cannot be charged: not at every PCPP input (`§5`), and — if a per-input test
  is insisted on — only on a majority of them (`§4`).

  **That reading is superseded, and the reader should not follow it into a
  majority design.**  `§5` is a genuine obstruction to the `∀`-input test and
  stands.  The inference from it to a *majority* test does not: it silently
  assumes the stage must reach a per-input verdict at all.  The manuscript's
  componentwise verifier (Appendix C.10) reaches no per-input verdict.  It
  estimates the single global average `mu = E_{i,u} F_i(u)` over the joint
  cube and compares that one number against the one threshold.  The transport
  of `§2` is then not an obstruction but exactly the tool the aggregate
  design needs: `l1DistanceFromBoolean_eq_expect_slice` says the published
  whole-cube radius *is* the aggregate slice error, so the completeness
  premise transports with no loss and with no Markov step.
  `AggregateSemanticStage` builds that design; `§4` is retained as correct
  mathematics but is not on its critical path.

  The majority reading is also unaffordable, which is the practical reason it
  must not be followed: charging a per-input test at every enumerated PCPP
  input costs `2 ^ scheduledWidth`, a polynomial of degree
  `ProjectionWidthEnvelope.widthLinearCoefficient outer 1`, and that degree
  carries the factor `2 ^ clockDepth` while `PublishedRecoveryClosure` pins
  `clockDepth = machine.verifier.degree + 1`.  The resulting fixed-point
  demand `degree ≥ 2 ^ (degree + 2)` has no numeral solution.

* **`§7` (the scheduled seed).**  `caseTwoSeed` is
  `PCPPClausePadding.fullyPaddedHonestOccurrenceFunction`, the honest
  occurrence table of `padClauses` extended along two ignored axes.  The
  clause-address padding is already a genuine `PointwisePCPP`, and the
  input-axis padding moves through the slice by `prefixBits`, so the transport
  holds verbatim at the scheduled seed:
  `clauseOccurrenceErrorMean_recoveredProofValue_fullyPadded`.

Nothing in `§1`–`§5` mentions a schedule, a machine, or an executable
program: the whole transport is finite measure bookkeeping on the occurrence
cube.
-/

namespace NearCubicWires.OccurrenceSliceTransport

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifierThresholdSeam

/-! ## §1 Coordinates of the occurrence cube

`occurrenceInput`, `occurrenceClauseAddress` and `occurrencePosition` of
`OuterPCPRecovery` project an occurrence address onto its three blocks.  The
assembler below is their common section, so the three projections are jointly
an equivalence. -/

/-- Assemble one occurrence address from a PCPP input, a clause address and a
left/right position bit. -/
def occurrenceAddress {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) : BitInput (inputArity + clauseBits + 1) :=
  fun index =>
    if hinput : index.val < inputArity then input ⟨index.val, hinput⟩
    else if hclause : index.val < inputArity + clauseBits then
      clause ⟨index.val - inputArity, by omega⟩
    else position

@[simp] theorem occurrenceInput_occurrenceAddress {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) :
    occurrenceInput (occurrenceAddress input clause position) = input := by
  funext index
  simp [occurrenceInput, occurrenceAddress, index.isLt]

@[simp] theorem occurrenceClauseAddress_occurrenceAddress
    {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) :
    occurrenceClauseAddress (occurrenceAddress input clause position) =
      clause := by
  funext index
  have hbound := index.isLt
  have hlow : ¬inputArity + index.val < inputArity := by omega
  have hhigh : inputArity + index.val < inputArity + clauseBits := by omega
  have hval : inputArity + index.val - inputArity = index.val := by omega
  simp only [occurrenceClauseAddress, occurrenceAddress, hlow, hhigh, dif_pos]
  exact congrArg clause (Fin.ext hval)

@[simp] theorem occurrencePosition_occurrenceAddress
    {inputArity clauseBits : ℕ}
    (input : BitInput inputArity) (clause : BitInput clauseBits)
    (position : Bool) :
    occurrencePosition (occurrenceAddress input clause position) =
      position := by
  have hlow : ¬inputArity + clauseBits < inputArity := by omega
  simp [occurrencePosition, occurrenceAddress, hlow]

theorem occurrenceAddress_projections {inputArity clauseBits : ℕ}
    (address : BitInput (inputArity + clauseBits + 1)) :
    occurrenceAddress (occurrenceInput address)
        (occurrenceClauseAddress address) (occurrencePosition address) =
      address := by
  funext index
  have hbound := index.isLt
  unfold occurrenceAddress occurrenceInput occurrenceClauseAddress
    occurrencePosition
  by_cases hinput : index.val < inputArity
  · simp only [hinput, dif_pos]
  · by_cases hclause : index.val < inputArity + clauseBits
    · have hval : inputArity + (index.val - inputArity) = index.val := by omega
      simp only [hinput, hclause, dif_neg, dif_pos, not_false_iff]
      exact congrArg address (Fin.ext hval)
    · have hval : inputArity + clauseBits = index.val := by omega
      simp only [hinput, hclause, dif_neg, not_false_iff]
      exact congrArg address (Fin.ext hval)

/-- The three occurrence blocks are jointly an equivalence with the cube. -/
def occurrenceCubeEquiv (inputArity clauseBits : ℕ) :
    BitInput inputArity × BitInput clauseBits × Bool ≃
      BitInput (inputArity + clauseBits + 1) where
  toFun parts := occurrenceAddress parts.1 parts.2.1 parts.2.2
  invFun address :=
    (occurrenceInput address, occurrenceClauseAddress address,
      occurrencePosition address)
  left_inv := by
    rintro ⟨input, clause, position⟩
    simp
  right_inv := occurrenceAddress_projections

/-- Little-endian enumeration of the clause-address block.  This is the exact
bijection `honestOccurrenceFunction` uses to turn address bits into a clause
index, so no second addressing convention is introduced. -/
private def clauseAddressBits (bits : ℕ) : Fin (2 ^ bits) ≃ BitInput bits where
  toFun index := fun bit => index.val.testBit bit.val
  invFun := binaryAddress
  left_inv index := binaryAddress_testBit index.isLt
  right_inv input := by
    funext bit
    change (binaryAddress input).val.testBit bit.val = input bit
    rw [binaryAddress_val_eq_ofBits]
    exact Nat.testBit_ofBits_lt input bit.val bit.isLt

private theorem card_bitInputCube (bits : ℕ) :
    Fintype.card (BitInput bits) = 2 ^ bits := by
  rw [Fintype.card_fun]
  simp

/-! ## §2 The whole-cube distance is the mean of the input slices

`l1DistanceFromBoolean` is the uniform mean over the *whole* occurrence cube.
Slicing the cube along its first block exhibits it as the uniform mean, over
PCPP inputs, of the per-input occurrence error.  This is the exact statement
of the average-versus-slice obstruction: nothing is lost, and nothing is
gained. -/

/-- Mean `ℓ¹` error of a guess against a Boolean occurrence table on the slice
above one fixed PCPP input. -/
noncomputable def occurrenceSliceDistance {inputArity clauseBits : ℕ}
    (table : BoolFunction (inputArity + clauseBits + 1))
    (guess : BitInput (inputArity + clauseBits + 1) → ℝ)
    (input : BitInput inputArity) : ℝ :=
  𝔼 slot : BitInput clauseBits × Bool,
    |guess (occurrenceAddress input slot.1 slot.2) -
      bitAsReal (table (occurrenceAddress input slot.1 slot.2))|

/-- **Cube slicing.**  The published approximation radius controls exactly the
*average* of the per-input occurrence errors. -/
theorem l1DistanceFromBoolean_eq_expect_slice {inputArity clauseBits : ℕ}
    (table : BoolFunction (inputArity + clauseBits + 1))
    (guess : BitInput (inputArity + clauseBits + 1) → ℝ) :
    l1DistanceFromBoolean table guess =
      𝔼 input : BitInput inputArity,
        occurrenceSliceDistance table guess input := by
  classical
  have hsum :
      (∑ address : BitInput (inputArity + clauseBits + 1),
          |guess address - bitAsReal (table address)|) =
        ∑ input : BitInput inputArity,
          ∑ slot : BitInput clauseBits × Bool,
            |guess (occurrenceAddress input slot.1 slot.2) -
              bitAsReal (table (occurrenceAddress input slot.1 slot.2))| := by
    rw [← (occurrenceCubeEquiv inputArity clauseBits).sum_comp
      (fun address => |guess address - bitAsReal (table address)|)]
    exact Fintype.sum_prod_type _
  rw [l1DistanceFromBoolean, hsum, Finset.expect_eq_sum_div_card]
  simp only [occurrenceSliceDistance, Finset.expect_eq_sum_div_card,
    Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    card_bitInputCube, ← Finset.sum_div, div_div]
  congr 1
  push_cast
  ring

/-! ## §3 The exact per-input transport

At one fixed PCPP input the two averages agree *exactly*.  The two structural
worries are both discharged by an identity rather than an inequality:

* a proof coordinate named by several occurrences is read back by the
  occurrence-fiber average, and `occurrenceAveraging_preserves_distance` shows
  that averaging over a fiber whose Boolean target is constant costs nothing;
* the honest occurrence table stores the *signed* literal value, so a negative
  literal is read back complemented, and complementation is an isometry. -/

/-- The literal one clause occurrence names.  `position = true` selects the
right literal, matching `honestOccurrenceFunction`. -/
def occurrenceLiteral {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    Literal (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  if slot.2 then (pcpp.clauses slot.1).right else (pcpp.clauses slot.1).left

/-- The proof coordinate one clause occurrence reads. -/
def occurrenceVariable {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) :
    Fin (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  literalIndex (occurrenceLiteral pcpp slot)

private theorem expect_slot_eq_sides {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (value : Fin (2 ^ pcpp.clauseBits) × Bool → ℝ) :
    (𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool, value slot) =
      ((𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))), value (i, false)) +
          𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
            value (i, true)) / 2 := by
  have hpositive : (0 : ℝ) < (2 ^ pcpp.clauseBits : ℕ) := by positivity
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
    Fintype.sum_prod_type, Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  field_simp
  push_cast
  ring

/-- The verifier's occurrence-uniform error is the uniform mean over clause
occurrences, in the `(clause index, position)` presentation. -/
theorem clauseOccurrenceErrorMean_eq_expect_slot {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (value reference :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    clauseOccurrenceErrorMean pcpp value reference =
      𝔼 slot : Fin (2 ^ pcpp.clauseBits) × Bool,
        |value (occurrenceVariable pcpp slot) -
          reference (occurrenceVariable pcpp slot)| := by
  rw [expect_slot_eq_sides]
  rfl

/-! ### The transport at the honest occurrence table -/

/-- The restriction of a guessed occurrence table to the slice above one PCPP
input, in the `(clause index, position)` presentation. -/
noncomputable def sliceGuess {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit)
    (guess : BitInput (n + pcpp.clauseBits + 1) → ℝ) (input : BitInput n)
    (slot : Fin (2 ^ pcpp.clauseBits) × Bool) : ℝ :=
  guess (occurrenceAddress input
    (clauseAddressBits pcpp.clauseBits slot.1) slot.2)

/-! ## §4 Markov: a two-thirds density of admissible PCPP inputs

The seam of `VerifierThresholdSeam` closes at `delta ≤ 3 * zeta`
(`threshold_le_estimate_of_occurrenceDelta`) while the published radius is
`repairedRecoveryDelta parameters = zeta`.  That factor-three reserve is
exactly what makes Markov's inequality usable: at radius `zeta` at most one
third of the PCPP inputs can carry a slice above `3 * zeta`. -/

/-! ## §5 The per-input transport genuinely fails

The identity of `§2` is sharp, so an average over `2 ^ inputArity` inputs
cannot bound one slice.  The family below realizes the whole loss: its honest
occurrence table is supported on a single PCPP input, so the constant-zero
guess is at whole-cube distance `1 / 2 ^ inputArity` while its slice above
that one input equals `1`.  Consequently no constant rescaling of the
published radius turns the whole-cube premise into the per-input premise. -/

/-! ## §6 What a *per-input* semantic test can charge

`§3` plus `§4` say what a per-input componentwise test can afford: the test at
*one* PCPP input is discharged by the transport whenever that input's slice is
inside the seam's `3 * zeta` budget, and at least two thirds of all PCPP inputs
are of that kind.  `§5` says such a test cannot be demanded at *every* PCPP
input.

**These are facts about per-input tests, not a specification of the verifier.**
The manuscript's componentwise verifier performs no per-input test: it
estimates one global average over the joint cube and compares it once.  See
`AggregateSemanticStage` for that design and for why the majority reading of
this section is both unnecessary and unaffordable.  The results below remain
correct and are kept because `threshold_le_estimate_of_sliceInput` is the
sharpest statement of the per-input seam, and because
`two_thirds_le_card_seamInputs_of_repairedDelta` records what the published
radius buys pointwise. -/

/-! ## §7 The transport at the scheduled Case-2 seed

`caseTwoSeed` is `fullyPaddedHonestOccurrenceFunction`, i.e. the honest
occurrence table of `padClauses` extended along the two ignored axes.  The
clause-address padding is already the honest occurrence table of a genuine
`PointwisePCPP` (`PCPPClausePadding.honestOccurrenceFunction_padClauses`), so
only the input-axis padding has to be moved through the slice, and it moves by
`prefixBits`.  Nothing in `§2`–`§4` changes. -/

end NearCubicWires.OccurrenceSliceTransport
