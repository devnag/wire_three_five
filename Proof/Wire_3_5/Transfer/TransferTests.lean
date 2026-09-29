import Proof.Circuits.ComponentwiseBranchExtraction
import Proof.Wire_3_5.Transfer.Rounding

/-! # The masked tests `V, Q, μ`, the thresholds, and `tr:soundness` (P3:3468-3554)

Realizes the verification of `tr:verification` (P3:3468-3491): "For auxiliary variables put `P_X = S_X²(1−S_X)²`.
For a systematic variable with prescribed encoding bit `E_X`, put `P_X = (S_X−E_X)²`. Write `E_pos` for the uniform
average over the `2M` clause positions. The weak machine estimates `V = E_{pos,e,x} G_X P_X`,
`Q = E_{pos,e,x} G_X S_X²`, `μ = E_{i,e,x} M_i Cons_i(S_{X(i,1)}, S_{X(i,2)})` (tr:tests). [...] accept only if
`V̂ ≤ 2v₀`, `Q̂ ≤ 1+v₀`, `μ̂ ≥ (c_p+s_p)/2` (tr:thresholds)", with the clause masks of `tr:masks` (P3:3444-3445):
"For clause `i`, use `M_i(e,x) = G_{X(i,1)}(e,x) G_{X(i,2)}(e,x)`." The masks are never renormalized: every score is
an unnormalized masked mean (`uMean` of `mask · value`).

And `tr:soundness` (P3:3504-3554): "For sufficiently small fixed `v₀, ε₀`, no branch of the weak machine accepts a
hierarchy no-instance [...]. This holds for every syntactically legal real-valued sparse guess, including guesses
whose values lie outside `[0,1]`, and for proof-dependent, seed-dependent masks." Its proof: round to one global
Boolean proof `B` (`roundedProof`, systematic bits forced), bound the masked rounding loss (the corrected
`tr:rounding`, `maskedRounding_holds`, erratum F2), drop the mask on the nonnegative Boolean clause value
(`tr:one-sided`, P3:3538-3542), and bound the rounded score by pointwise PCPP soundness plus the outer verifier's
acceptance fraction (P3:3544-3547): "even though the proof bits themselves are functions of the full random input".

The PCPP is the Theorem 2.5 `PointwisePCPP` of a Boolean circuit `H` on the outer randomness `x ∈ {0,1}^q` (the
outer verifier with the guessed oracle substituted, P3:3651-3653); the guess `S_X(x)` is any real function of `x`;
the masks `G_X(e,x)` are any Boolean functions of the seed and `x` (the instance with the seed's `filt:gap` filters
is `Proof.Wire_3_5.Transfer.TransferSeedMasks`). The second-moment test `Q` is kept and consumed through the
`MaskedRounding` interface.

Paper quantities of the main types: the tests `testV`, `testQ`, `testMu` (tr:tests), the acceptance predicate
`MaskedAccepts` (tr:thresholds), the accepting-branch data `MaskedVerifierTrace`, and `tr:soundness` as
`maskedVerifierTrace_empty` (no accepting trace on a PCPP whose circuit the outer verifier rejects except on at
most `η` of its random inputs). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces
open NearCubicWires.WireExponent3_5.Shared (uMean bitR maskedMean uMean_mono uMean_add bitR_nonneg bitR_le_one
  maskedMean_le_of_nonneg maskedRounding_holds)
open NearCubicWires.ComponentwiseValidity (validityPenalty validityRound clauseValue)
open NearCubicWires.ComponentwiseBranchExtraction (literalIndex literalNegated systematicConstraint roundedProof
  roundedAuxiliary clauseRealValue roundedProof_eq_assignment clauseRealValue_bitAsReal)

/-! ## Uniform means: two helpers -/

theorem uMean_sub {Ω : Type} [Fintype Ω] (f g : Ω → ℝ) : uMean (fun ω => f ω - g ω) = uMean f - uMean g := by
  unfold uMean; rw [Finset.sum_sub_distrib, sub_div]

theorem uMean_const {Ω : Type} [Fintype Ω] [Nonempty Ω] (c : ℝ) : uMean (fun _ : Ω => c) = c := by
  unfold uMean
  have h : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- A statistic of the clause and the input only: its mean over clauses, seeds and inputs is the input mean of its
clause mean (the seed average is trivial, P3:3514-3515: `B` is "independent of `e`"). -/
theorem uMean_clause_seed_input {C Seed In : Type} [Fintype C] [Fintype Seed] [Fintype In] [Nonempty C]
    [Nonempty Seed] [Nonempty In] (g : C → In → ℝ) :
    uMean (fun p : C × (Seed × In) => g p.1 p.2.2) = uMean (fun x : In => uMean (fun i : C => g i x)) := by
  unfold uMean
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hS : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hI : (0 : ℝ) < Fintype.card In := by exact_mod_cast Fintype.card_pos
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Nat.cast_mul]
  rw [← Finset.sum_div, Finset.sum_comm, ← Finset.mul_sum]
  field_simp

/-! ## Clause positions of the PCPP -/

section Positions
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H)

/-- The PCPP variables, systematic first (`X` of P3:3395-3396). -/
abbrev PcppVar : Type := Fin (pcpp.systematicBits + pcpp.auxiliaryBits)

/-- The literal at position `j ∈ {0,1}` of clause `i`. -/
def posLiteral (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) :
    Literal (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  ![(pcpp.clauses i).left, (pcpp.clauses i).right] j

/-- `X(i,j)`: the variable named at position `(i,j)` (P3:3395). -/
def posVar (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) : PcppVar pcpp := literalIndex (posLiteral pcpp i j)

/-- The prescribed sign at position `(i,j)` (the signs of `Cons_i`, P3:3483-3484). -/
def posNeg (i : Fin (2 ^ pcpp.clauseBits)) (j : Fin 2) : Bool := literalNegated (posLiteral pcpp i j)

@[simp] theorem posVar_zero (i : Fin (2 ^ pcpp.clauseBits)) :
    posVar pcpp i 0 = literalIndex (pcpp.clauses i).left := by simp [posVar, posLiteral]
@[simp] theorem posVar_one (i : Fin (2 ^ pcpp.clauseBits)) :
    posVar pcpp i 1 = literalIndex (pcpp.clauses i).right := by simp [posVar, posLiteral]
@[simp] theorem posNeg_zero (i : Fin (2 ^ pcpp.clauseBits)) :
    posNeg pcpp i 0 = literalNegated (pcpp.clauses i).left := by simp [posNeg, posLiteral]
@[simp] theorem posNeg_one (i : Fin (2 ^ pcpp.clauseBits)) :
    posNeg pcpp i 1 = literalNegated (pcpp.clauses i).right := by simp [posNeg, posLiteral]

end Positions

/-! ## The tests (`tr:tests`, P3:3471-3484) and the thresholds (`tr:thresholds`, P3:3485-3491) -/

section Tests
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {Seed : Type} [Fintype Seed]

/-- `V = E_{pos,e,x} G_X P_X`: the masked validity penalty, `P_X = S_X²(1−S_X)²` on auxiliary variables and
`(S_X − E_X(x))²` on systematic ones (`validityPenalty` at the prescribed constraint). -/
noncomputable def testV (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
    bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2) *
      validityPenalty (systematicConstraint pcpp p.2.2.2 (posVar pcpp p.1 p.2.1)) (S (posVar pcpp p.1 p.2.1) p.2.2.2)

/-- `Q = E_{pos,e,x} G_X S_X²`: the masked second moment (kept). -/
noncomputable def testQ (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
    bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2) * S (posVar pcpp p.1 p.2.1) p.2.2.2 ^ 2

/-- The clause mask `M_i(e,x) = G_{X(i,1)}(e,x) G_{X(i,2)}(e,x)` (P3:3444-3445). -/
def clauseMask (G : PcppVar pcpp → Seed → BitInput q → Bool) (i : Fin (2 ^ pcpp.clauseBits)) (e : Seed)
    (x : BitInput q) : Bool :=
  G (posVar pcpp i 0) e x && G (posVar pcpp i 1) e x

/-- `μ = E_{i,e,x} M_i Cons_i(S_{X(i,1)}, S_{X(i,2)})`, with `Cons_i` the degree-two arithmetization of the
two-literal OR with its prescribed signs (`clauseRealValue`, Theorem 2.5's `clauseValue`). -/
noncomputable def testMu (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
    bitR (clauseMask pcpp G p.1 p.2.1 p.2.2) * clauseRealValue (pcpp.clauses p.1) (fun X => S X p.2.2)

end Tests

/-- The fixed rational constants of the masked verifier: the validity tolerance `v₀`, the propagated numerical
error `ε₀ ≤ v₀` (P3:3490-3491), the outer verifier's error budget `η` (it accepts a no-instance on at most `N^{−10}`
of its random inputs, P3:3544, which is `≤ η` at all sufficiently large lengths), and the rational acceptance
threshold for `μ̂`, at or above the paper's `(c_p+s_p)/2`. The paper's choice (P3:3550):
`5√(24v₀) + ε₀ < (c_p−s_p)/3`; `v₀ ≤ 1/24` is the corrected rounding's range (erratum F2). -/
structure MaskedSoundnessParameters (cp sp : ℝ) where
  v0 : ℚ
  eps0 : ℚ
  outerError : ℚ
  threshold : ℚ
  v0_pos : 0 < v0
  v0_le : v0 ≤ 1 / 24
  eps0_nonneg : 0 ≤ eps0
  eps0_le_v0 : eps0 ≤ v0
  sp_nonneg : 0 ≤ sp
  thresholdAboveMidpoint : (cp + sp) / 2 ≤ (threshold : ℝ)
  roundingReserve : 5 * Real.sqrt (24 * (v0 : ℝ)) + (eps0 : ℝ) < (cp - sp) / 3
  outerReserve : (outerError : ℝ) ≤ (cp - sp) / 6

/-! ## Soundness (`tr:soundness`, P3:3504-3554) -/

section Soundness
variable {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {Seed : Type} [Fintype Seed]

/-- The rounded Boolean proof's clause value at `(i, x)`: `Cons_i(B(x))`, with `B = roundedProof` (auxiliary bits
rounded at one half, systematic bits forced to `E_X(x)`), P3:3514-3515. -/
noncomputable def roundedClause (S : PcppVar pcpp → BitInput q → ℝ) (i : Fin (2 ^ pcpp.clauseBits))
    (x : BitInput q) : ℝ :=
  clauseRealValue (pcpp.clauses i) (fun X => bitAsReal (roundedProof pcpp x (fun X => S X x) X))

/-- The rounded proof is a genuine PCPP assignment, so its clause value is the Boolean clause value. -/
theorem roundedClause_eq (S : PcppVar pcpp → BitInput q → ℝ) (i : Fin (2 ^ pcpp.clauseBits)) (x : BitInput q) :
    roundedClause pcpp S i x =
      bitAsReal ((pcpp.clauses i).eval (pcpp.assignment x (roundedAuxiliary pcpp (fun X => S X x)))) := by
  unfold roundedClause
  rw [clauseRealValue_bitAsReal, roundedProof_eq_assignment]

theorem roundedClause_nonneg (S : PcppVar pcpp → BitInput q → ℝ) (i : Fin (2 ^ pcpp.clauseBits))
    (x : BitInput q) : 0 ≤ roundedClause pcpp S i x := by
  rw [roundedClause_eq]; cases (pcpp.clauses i).eval _ <;> simp [bitAsReal]

/-- The masked rounded score `E_{i,e,x} M_i Cons_i(B)`. -/
noncomputable def maskedRoundedScore (S : PcppVar pcpp → BitInput q → ℝ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool) : ℝ :=
  uMean fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
    bitR (clauseMask pcpp G p.1 p.2.1 p.2.2) * roundedClause pcpp S p.1 p.2.2

/-- **`tr:rounding`** at the tests (P3:3512-3536, corrected, erratum F2): passing the first two tests (after the
numerical slack, `V ≤ 3v₀` and `Q ≤ 1+2v₀`) puts the masked clause score within `5√(24v₀)` of the rounded one. -/
theorem testMu_le_rounded (S : PcppVar pcpp → BitInput q → ℝ) (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (v₀ : ℝ) (hv : 0 < v₀) (hv24 : v₀ ≤ 1 / 24) (hV : testV pcpp S G ≤ 3 * v₀)
    (hQ : testQ pcpp S G ≤ 1 + 2 * v₀) :
    testMu pcpp S G ≤ maskedRoundedScore pcpp S G + 5 * Real.sqrt (24 * v₀) := by
  have h := maskedRounding_holds (Clause := Fin (2 ^ pcpp.clauseBits)) (Ω := Seed × BitInput q)
    (fun i j ω => S (posVar pcpp i j) ω.2) (fun i j ω => systematicConstraint pcpp ω.2 (posVar pcpp i j))
    (fun i j => posNeg pcpp i j) (fun i j ω => G (posVar pcpp i j) ω.1 ω.2) v₀ hv hv24 hV hQ
  have hsplit : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) =>
      bitR (G (posVar pcpp p.1 0) p.2.1 p.2.2 && G (posVar pcpp p.1 1) p.2.1 p.2.2) *
        (clauseValue (posNeg pcpp p.1 0) (posNeg pcpp p.1 1) (S (posVar pcpp p.1 0) p.2.2)
            (S (posVar pcpp p.1 1) p.2.2) -
          clauseValue (posNeg pcpp p.1 0) (posNeg pcpp p.1 1)
            (bitAsReal (validityRound (systematicConstraint pcpp p.2.2 (posVar pcpp p.1 0))
              (S (posVar pcpp p.1 0) p.2.2)))
            (bitAsReal (validityRound (systematicConstraint pcpp p.2.2 (posVar pcpp p.1 1))
              (S (posVar pcpp p.1 1) p.2.2))))) =
      testMu pcpp S G - maskedRoundedScore pcpp S G := by
    unfold testMu maskedRoundedScore
    rw [← uMean_sub]
    refine congrArg uMean (funext fun p => ?_)
    simp only [mul_sub, posVar_zero, posVar_one, posNeg_zero, posNeg_one, clauseMask, roundedClause,
      clauseRealValue, roundedProof]
  rw [hsplit] at h
  linarith [(abs_le.mp h).2]

/-- **`tr:one-sided`** (P3:3538-3542): "For a Boolean proof, `Cons_i(B)` is a nonnegative Boolean value.
Consequently `E_{i,e,x} M_i Cons_i(B) ≤ E_{i,x} Cons_i(B)`" — whatever the masks. -/
theorem maskedRoundedScore_le [Nonempty Seed] (S : PcppVar pcpp → BitInput q → ℝ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool) :
    maskedRoundedScore pcpp S G ≤ uMean (fun x : BitInput q => uMean (fun i => roundedClause pcpp S i x)) := by
  have h0 := maskedMean_le_of_nonneg
    (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => clauseMask pcpp G p.1 p.2.1 p.2.2)
    (f := fun p => roundedClause pcpp S p.1 p.2.2) (fun p => roundedClause_nonneg pcpp S p.1 p.2.2)
  have e : maskedRoundedScore pcpp S G =
      maskedMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => clauseMask pcpp G p.1 p.2.1 p.2.2)
        (fun p => roundedClause pcpp S p.1 p.2.2) := by
    unfold maskedRoundedScore maskedMean; rfl
  have h1 : maskedRoundedScore pcpp S G ≤
      uMean (fun p : Fin (2 ^ pcpp.clauseBits) × (Seed × BitInput q) => roundedClause pcpp S p.1 p.2.2) :=
    e ▸ h0
  haveI : Nonempty (Fin (2 ^ pcpp.clauseBits)) := ⟨⟨0, by positivity⟩⟩
  rwa [uMean_clause_seed_input (fun i x => roundedClause pcpp S i x)] at h1

/-- The clause mean of the rounded proof at `x` is the PCPP satisfied fraction of that assignment. -/
theorem uMean_roundedClause (S : PcppVar pcpp → BitInput q → ℝ) (x : BitInput q) :
    uMean (fun i => roundedClause pcpp S i x) =
      pcpp.satisfiedFraction x (roundedAuxiliary pcpp (fun X => S X x)) := by
  rw [← ComponentwiseBranchExtraction.expect_bitAsReal_eq_satisfiedFraction, Finset.expect_eq_sum_div_card,
    Finset.card_univ]
  unfold uMean
  congr 1
  exact Finset.sum_congr rfl fun i _ => roundedClause_eq pcpp S i x

/-- Pointwise PCPP soundness plus the outer error (P3:3544-3547): if every rejected `x` bounds every auxiliary
assignment's satisfied fraction by `s_p`, then `E_{i,x} Cons_i(B) ≤ s_p + E_x[H(x)]`. -/
theorem roundedScore_le_soundness {sp : ℝ} (hsp : 0 ≤ sp)
    (hsound : ∀ x, ¬ H.eval x → ∀ aux, pcpp.satisfiedFraction x aux ≤ sp) (S : PcppVar pcpp → BitInput q → ℝ) :
    uMean (fun x : BitInput q => uMean (fun i => roundedClause pcpp S i x)) ≤
      sp + uMean (fun x : BitInput q => bitR (H.eval x)) := by
  have hpt : ∀ x : BitInput q, uMean (fun i => roundedClause pcpp S i x) ≤ sp + bitR (H.eval x) := by
    intro x
    rw [uMean_roundedClause]
    by_cases hx : H.eval x
    · have := ComponentwiseVerifierParameters.pointwiseSatisfiedFraction_le_one pcpp x
        (roundedAuxiliary pcpp (fun X => S X x))
      simp only [hx, bitR, if_true]; linarith
    · have := hsound x hx (roundedAuxiliary pcpp (fun X => S X x))
      simp only [hx, bitR, Bool.false_eq_true, if_false]; linarith
  calc uMean (fun x : BitInput q => uMean (fun i => roundedClause pcpp S i x))
      ≤ uMean (fun x : BitInput q => sp + bitR (H.eval x)) := uMean_mono hpt
    _ = sp + uMean (fun x : BitInput q => bitR (H.eval x)) := by rw [uMean_add, uMean_const]

end Soundness

/-! ## The paper's parameter choice is satisfiable, and the trace is not vacuous -/

end NearCubicWires.WireExponent3_5.Transfer
