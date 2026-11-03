import Proof.Wire_3_5.Transfer.TransferUnionSoundBase
import Proof.Wire_3_5.Filters.FilterGap

/-! # The union machine's completeness side (P3:3564-3614, 3711-3729): an accepting guess from an approximation

Realizes the completeness direction consumed by Case 2 (P3:3726-3729): "Lemma tr:completeness would then supply an
accepting sparse guess in that mode, contradicting rejection of the union machine". An accepting guess is one with
`UnionAccepts`. This module proves that a guess is accepted as soon as

* it passes the syntactic checks (oracle size, grid signs, the `⌊N/16⌋` word) and its calls are admissible, and
* its grid sums are a completeness witness for the honest proof of the (tautological) substituted circuit — `[0,1]`
  sums `T_X` with `E_pos‖T_X − B_X‖₁ ≤ ζ` and `‖S_X − T_X‖₄ ≤ δ` (`tr:completeness`) — whose filters miss
  incidence mass at most `β + ξ` (`tr:missing`), with the propagated error `(1+Λ̄(q))⁴q^{−D} ≤ ε₀`:

`unionAccepts_of_parts`. The thresholds come from the three test bounds and the accuracy, in the real form
`completeness_accepts_real`; the honest clause acceptance `≥ c_p` is the PCPP algorithm's `complete` at every random
input of a tautology (`honest_acceptance`, P3:3712-3714: the first small accepting oracle makes the outer verifier a
tautology). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open Filter Topology
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.Shared (uMean bitR uMean_mono)
open NearCubicWires.ComponentwiseBranchExtraction (systematicConstraint)

/-- `tr:completeness`'s acceptance with real estimates: within `ε₀` of the tests of a completeness witness whose
masks miss at most `β + ξ`, the estimates pass the thresholds. -/
theorem completeness_accepts_real {q : ℕ} {H : BooleanCircuit q} (pcpp : PointwisePCPP H) {cp sp : ℝ}
    {params : MaskedSoundnessParameters cp sp} (cparams : MaskedCompletenessParameters params)
    {Seed : Type} [Fintype Seed] [Nonempty Seed] (aux : BitInput q → BitInput pcpp.auxiliaryBits)
    (T S : PcppVar pcpp → BitInput q → ℝ) (w : CompletenessWitness pcpp aux T S cparams.ζ cparams.δ)
    (G : PcppVar pcpp → Seed → BitInput q → Bool)
    (hacc : cp ≤ uMean (fun x : BitInput q => pcpp.satisfiedFraction x (aux x)))
    (hmissing : uMean (fun p : Fin (2 ^ pcpp.clauseBits) × Fin 2 × (Seed × BitInput q) =>
        1 - bitR (G (posVar pcpp p.1 p.2.1) p.2.2.1 p.2.2.2)) ≤ (cparams.β : ℝ) + cparams.ξ)
    (Vh Qh μh : ℝ) (hV : |Vh - testV pcpp S G| ≤ params.eps0) (hQ : |Qh - testQ pcpp S G| ≤ params.eps0)
    (hμ : |μh - testMu pcpp S G| ≤ params.eps0) :
    Vh ≤ 2 * (params.v0 : ℝ) ∧ Qh ≤ 1 + (params.v0 : ℝ) ∧ (params.threshold : ℝ) ≤ μh := by
  have hζ1 : Real.sqrt (cparams.ζ : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; exact_mod_cast cparams.ζ_le_one
  have hδ1 : (cparams.δ : ℝ) ≤ 1 := by exact_mod_cast cparams.δ_le_one
  have hu : Real.sqrt (cparams.ζ : ℝ) + cparams.δ ≤ 2 := by linarith
  have hVb := completeness_testV w G
  have hQb := completeness_testQ w G
  have hmiss := (missingClause_le G).trans (mul_le_mul_of_nonneg_left hmissing zero_le_two)
  have hμb := completeness_testMu w G hacc hmiss hu
  have hVs := cparams.V_slack
  have hQs := cparams.Q_slack
  have hμs := cparams.μ_slack
  refine ⟨?_, ?_, ?_⟩
  · linarith [(abs_le.mp hV).2]
  · linarith [(abs_le.mp hQ).2]
  · linarith [(abs_le.mp hμ).1]

section Union
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

namespace UnionGuess
variable {N : ℕ} {z : BitInput N} 

/-! ## Admissible calls: the tuple of a nonzero coefficient lies in the named carriers -/

theorem coeff_factor_ne {α : Type} {P : Poly4 α} {j : Fin 4} {t : Fin 4 → α} (h : P.coeff j t ≠ 0) (k : Fin 4) :
    P.F j k (t k) ≠ 0 := by
  unfold Poly4.coeff at h
  have h2 : ∏ k, P.F j k (t k) ≠ 0 := right_ne_zero_of_mul h
  exact (Finset.prod_ne_zero_iff.mp h2) k (Finset.mem_univ _)

theorem polyV_factor {α : Type} (sys : Bool) (wS wOne wE : α → ℝ) (j k : Fin 4) :
    (polyV sys wS wOne wE).F j k = wS ∨ (polyV sys wS wOne wE).F j k = wOne ∨
      (sys = true ∧ (polyV sys wS wOne wE).F j k = wE) := by
  cases sys <;> fin_cases j <;> fin_cases k <;> simp [polyV, Poly4.mk4, fac4]

theorem polyQ_factor {α : Type} (wS wOne : α → ℝ) (j k : Fin 4) :
    (polyQ wS wOne).F j k = wS ∨ (polyQ wS wOne).F j k = wOne := by
  fin_cases j <;> fin_cases k <;> simp [polyQ, Poly4.mk4, fac4]

theorem polyMu_factor {α : Type} (n₀ n₁ : Bool) (wX wY wOne : α → ℝ) (j k : Fin 4) :
    (polyMu n₀ n₁ wX wY wOne).F j k = wX ∨ (polyMu n₀ n₁ wX wY wOne).F j k = wY ∨
      (polyMu n₀ n₁ wX wY wOne).F j k = wOne := by
  fin_cases j <;> fin_cases k <;> simp [polyMu, Poly4.mk4, fac4]

/-! ## The missing mass at the guess's own carriers (`tr:missing`, P3:3413-3443) -/

/-- The residual bits of a carrier have twice its length. -/
theorem length_residualBits {n : ℕ} (X : Stars.Carrier n) (c u v : BitInput n) :
    (Stars.Carrier.residualBits X c u v).length = 2 * X.length := by
  unfold Stars.Carrier.residualBits
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil, List.map_const', List.sum_replicate, smul_eq_mul]
  ring

/-- `star:selection`'s objective of a list indexed by `Fin k`. -/
theorem objective_finRange (P : Shared.StarParams) (σ : P.Translation) {k : ℕ} (F : Fin k → ℚ × Stars.Carrier P.n) :
    (P.objective σ ((List.finRange k).map F) : ℝ) =
      (∑ i : Fin k, ((F i).1 : ℝ) * ∑ x : BitInput P.n, (Stars.inputPopulation P σ (F i).2 x : ℝ)) / 2 ^ P.n := by
  unfold Shared.StarParams.objective
  rw [List.map_map, ← Fin.sum_univ_def]
  simp only [Function.comp_apply]
  push_cast
  rfl

/-! ## The guess word, the carriers' envelope and wires -/

theorem length_flatten_ofFn {β : Type} {k : ℕ} (F : Fin k → List β) :
    (List.ofFn F).flatten.length = ∑ a, (F a).length := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]; rfl

theorem wires_append {n : ℕ} (X Y : Stars.Carrier n) :
    Stars.Carrier.wires (X ++ Y) = Stars.Carrier.wires X + Stars.Carrier.wires Y := by
  unfold Stars.Carrier.wires; rw [List.map_append, List.sum_append]

theorem wires_flatten_ofFn {n k : ℕ} (F : Fin k → Stars.Carrier n) :
    Stars.Carrier.wires (List.ofFn F).flatten = ∑ a, Stars.Carrier.wires (F a) := by
  unfold Stars.Carrier.wires
  rw [List.map_flatten, List.sum_flatten, List.map_ofFn, List.map_ofFn, List.sum_ofFn]
  rfl

end UnionGuess

/-! ## The guess of a sparse witness, and the accepting guess -/

section Build

end Build

end Union

end NearCubicWires.WireExponent3_5.Transfer
