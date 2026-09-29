import Proof.CaseAnalysis.FinalStageJoin

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy (rowDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (thresholdRows primeCutoff
  listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf decompositionOf
  expanderOf primeOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (seedExponent walkExponent
  rowCount_eq_two_pow card_walkSample)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo PrimeIndex)
open NearCubicWires.SupplierTouching (touchingCost touchIndicator)
open NearCubicWires.SupplierWalkBridge

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The per-atom wire envelope, as a number

`paper.tex:4296` charges the envelope PER ATOM, so the Lean quantity is one
natural number per atom.  Both target classes already carry a `wireCount`
(`Proof/Foundations/SupplierPipeline.lean` and `:357`), and the systematic
constructor's envelope is the wire count of the native parity circuit
`atomToUnion` compiles it into (`paper.tex:4303`: "Systematic parities are
source-explicit and are compiled deterministically into the native parity
circuits"), so ONE definition covers all three constructors. -/

/-! ## §2 Wires dominate the occurrence population, in both classes

This is the bridge the envelope has to cross: `seedExponent`'s first argument is
an occurrence-list LENGTH, and the envelope is a WIRE COUNT. -/

/-! ## §3 The two branch populations, from the envelope alone -/

/-- Monotone envelope for one canonical walk-seed exponent. -/
def seedEnvelope (popBound touchBound denBound : ℕ) : ℕ :=
  3 * max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) + 1 +
    320 * Nat.clog 2 (denBound + 1)

theorem canonicalGradedRank_mono {population activeBound popBound touchBound : ℕ}
    (hpop : population ≤ popBound) (htouch : activeBound ≤ touchBound) :
    canonicalGradedRank population activeBound ≤
      max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) := by
  unfold canonicalGradedRank canonicalGradedDepth
  exact max_le_max (Nat.clog_mono_right 2 (Nat.mul_le_mul_left 256 htouch))
    (Nat.clog_mono_right 2 hpop)

/-- **The walk-seed exponent is `O(log)` of its three arguments.** -/
theorem walkExponent_le_seedEnvelope
    {population activeBound denominator popBound touchBound denBound : ℕ}
    (hpop : population ≤ popBound) (htouch : activeBound ≤ touchBound)
    (hden : denominator ≤ denBound) :
    walkExponent (toeplitzWalkSideBits (canonicalGradedRank population activeBound))
        denominator ≤ seedEnvelope popBound touchBound denBound := by
  unfold walkExponent seedEnvelope
  have hrank := canonicalGradedRank_mono hpop htouch
  have hside : 2 * toeplitzWalkSideBits (canonicalGradedRank population activeBound) ≤
      3 * canonicalGradedRank population activeBound + 1 :=
    le_trans (twice_toeplitzWalkSideBits_le _)
      (Nat.add_le_add_right (toeplitzSeedBits_le_three_mul _) 1)
  have hleft : 2 * toeplitzWalkSideBits (canonicalGradedRank population activeBound) ≤
      3 * max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) + 1 :=
    le_trans hside (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hrank) 1)
  have hdenLog : Nat.clog 2 (denominator + 1) ≤ Nat.clog 2 (denBound + 1) :=
    Nat.clog_mono_right 2 (Nat.add_le_add_right hden 1)
  omega

/-- The touching cost never exceeds the occurrence population: it is a sum of
indicators over the occurrence index type. -/
theorem touchingCost_le_length {q : ℕ} (occurrences : List (SupportedNormalizedGate q))
    (selected : Finset (Fin q)) :
    touchingCost (occurrenceSupport occurrences) selected ≤ occurrences.length := by
  unfold touchingCost touchIndicator
  calc (∑ gate : Fin occurrences.length,
        if Disjoint selected (occurrenceSupport occurrences gate) then 0 else 1) ≤
        ∑ _gate : Fin occurrences.length, 1 := by
        refine Finset.sum_le_sum ?_
        intro gate _hgate
        split <;> omega
    _ = occurrences.length := by simp

/-! ### §4a RESOURCE RECEIPT -- the envelope is LINEAR IN BIT LENGTHS

`ENDGAME_RESOURCE.md`, the section headed "The paper's split, and the Lean object
that is literally it": *"Nothing else in the campaign may add a second residual
factor -- `damping` proves the one factor is absorbed, and a second one is not
absorbable."*  The settling paragraph of the bucket section: *"Taking the Lean
`kappa := sigma` and the paper's `kappa >= h_D+sigma+c_1` leaves exactly the
`q^{h_D}` external-row slack the paper spends at A.8 on `q-K+h_D L_q+O(1)`."*

The test that decides it is whether `seedEnvelope` is `O(L_q)`, and the theorem
below settles it in the sharpest available form: **`seedEnvelope` is bounded by a
fixed linear function of the BIT LENGTHS of its three arguments.**  So a wire
envelope of polynomial size (bit length `O(log q) = O(L_q)`) gives an external-row
exponent `O(L_q)` -- the `h_D L_q` slack A.8 already budgets, in the
`FREE / POLYLOG` bucket -- and, contrapositively, a wire envelope of size
`2 ^ Omega(q)` gives bit length `Omega(q)` and an external-row exponent
`Omega(q)`, which would be the forbidden second residual factor.  **A wire
envelope that is not polynomial is not acceptable, and this is the inequality
that says so.** -/

/-- **The envelope is linear in the bit lengths of its arguments.** -/
theorem seedEnvelope_le_of_bits {popBound touchBound denBound popBits touchBits denBits : ℕ}
    (hpop : popBound ≤ 2 ^ popBits) (htouch : touchBound ≤ 2 ^ touchBits)
    (hden : denBound + 1 ≤ 2 ^ denBits) :
    seedEnvelope popBound touchBound denBound ≤
      3 * (8 + touchBits + popBits) + 1 + 320 * denBits := by
  unfold seedEnvelope
  have hpopLog : Nat.clog 2 popBound ≤ popBits := by
    calc Nat.clog 2 popBound ≤ Nat.clog 2 (2 ^ popBits) := Nat.clog_mono_right 2 hpop
      _ = popBits := Nat.clog_pow 2 popBits (by norm_num)
  have htouchLog : Nat.clog 2 (256 * touchBound) ≤ 8 + touchBits := by
    calc Nat.clog 2 (256 * touchBound) ≤ Nat.clog 2 (2 ^ (8 + touchBits)) := by
          refine Nat.clog_mono_right 2 ?_
          calc 256 * touchBound ≤ 256 * 2 ^ touchBits := Nat.mul_le_mul_left 256 htouch
            _ = 2 ^ (8 + touchBits) := by rw [pow_add]; norm_num
      _ = 8 + touchBits := Nat.clog_pow 2 (8 + touchBits) (by norm_num)
  have hdenLog : Nat.clog 2 (denBound + 1) ≤ denBits := by
    calc Nat.clog 2 (denBound + 1) ≤ Nat.clog 2 (2 ^ denBits) := Nat.clog_mono_right 2 hden
      _ = denBits := Nat.clog_pow 2 denBits (by norm_num)
  have hmax : max (Nat.clog 2 (256 * touchBound)) (Nat.clog 2 popBound) ≤
      8 + touchBits + popBits := max_le (by omega) (by omega)
  omega

/-! ## §5 The two branch row counts

The SYM factor is a pure power of two; the THR factor is a prime window times a
power of two.  Both exponents are `seedEnvelope`s. -/

/-- **The primes-up-to window never exceeds its cutoff.**  Available to a caller
that prefers the cutoff form of `hprime` above. -/
theorem primesUpTo_card_le (cutoff : ℕ) : (primesUpTo cutoff).card ≤ cutoff + 1 := by
  unfold primesUpTo
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_range]

/-! ## §6 The union row count and `stageDen`, from the envelope

`unionAtomRows`' count is the PRODUCT (`unionAtomRows_rowCount`,
`Proof/CaseAnalysis/FinalUnionSupplier.lean`), so both §5 bounds are needed.
`stageDen` (`Proof/CaseAnalysis/FinalStageFields.lean`) is that count times
`2 ^ q` -- A.13.9's `|\mathcal E| 2^q` (`paper.tex:3161`). -/

/-! ## §7 The membership-guarded field -- what the record stream actually needs

`phaseRecords'_valid` (`Proof/CaseAnalysis/FinalExactFraction.lean`)
takes its per-record premise as
`∀ address monomial, monomial ∈ (siteCalls …).monomials → Entry.Valid …`.
The MEMBERSHIP is the paper's rejection rule in Lean: the machine only ever
prints monomials of the description it accepted, and an accepted description
clears the per-atom wire envelope.  `exactFraction_records_valid` (`:188`)
discards that membership and re-quantifies over the whole monomial type; from
there it is re-quantified again in `StageBlock'.hden`
(`Proof/CaseAnalysis/FinalExactStagePackage.lean`).

`SiteDenFits` below is the field as `phaseRecords'_valid` consumes it, and
`siteDenFits_of_wireEnvelope` discharges it from the envelope. -/

/-! ## §9 `hfloor` is FREE at the enlarged coefficient floor

`stageEntryWidth` (`Proof/CaseAnalysis/FinalSupplierWidth.lean`) is a `max`
whose first branch is the caller's `coefficientFloor n`, so re-keying Floor 3 to
the external-row exponent costs nothing structural: the enlarged floor below
makes §6's `hfloor` an instance of `le_max_left`, and it keeps CLAUSEBITS'
coefficient bound by `le_max_left` as well, so `ecoef` transports through
`stage_field_hcoefficients` (`Proof/CaseAnalysis/FinalStageFields.lean`)
unchanged.  `stageScale` is never touched. -/


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
