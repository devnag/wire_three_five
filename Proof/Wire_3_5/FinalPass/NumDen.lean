import Proof.Wire_3_5.Primitive.SeedFix.SeedFixSampler

/-! # The final pass's value as a ratio of two naturals (P3:3170-3181)

The final pass prints `ratWord (greedyValue I alg req)` (`PlanFP.fpOut`), and `greedyValue` is `fusedValueBits` at
the greedy sampler: for THR `thrValueBits` = `(Σ_z Σ_e Σ_ℓ Σ_{g,p} (1/|𝒫|)·M·R̂)/(|Z|·|E|·Q)`, for SYM `symValueBits`
= `(Σ_z Σ_{(e,e')} Σ_ℓ M·R̂)/(|Z|·|E × E'|·Q)`, and `0` off the star hypotheses. Both are one ratio of naturals:
`numOf / denOf` with `numOf` the count of the sampled points where the mask and the reported row hold (over seeds,
columns, samples, and for THR the rows `(g, p)`) and `denOf` the product of the counts (`|𝒫|` folded in for THR).
This is the seam of the final pass's `seeds` and `out` phases: `seeds` leaves `numOf` and `denOf` in binary, `out`
prints `ratWord (numOf / denOf)` (**`value_eq`**). Main declarations: `thrNum`, `thrDen`, `thrValueBits_numden`,
`symNum`, `symDen`, `symValueBits_numden`, `numOf`, `denOf`, **`value_eq`**. Paper quantity: the primitive's printed
value `greedyValue I alg req`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass

theorem bitQ_mul (b c : Bool) : bitQ b * bitQ c = ((b.toNat * c.toNat : ℕ) : ℚ) := by
  cases b <;> cases c <;> simp [bitQ]

theorem sum4_div {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (K D : ℚ)
    (f : α → β → γ → δ → ℕ) :
    (∑ x, ∑ y, ∑ z, ∑ w, (1 / K) * (f x y z w : ℚ)) / D = ((∑ x, ∑ y, ∑ z, ∑ w, f x y z w : ℕ) : ℚ) / (K * D) := by
  simp only [← Finset.mul_sum]
  push_cast
  rw [one_div_mul_eq_div, div_div]

theorem sum3_div {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (D : ℚ) (f : α → β → γ → ℕ) :
    (∑ x, ∑ y, ∑ z, (f x y z : ℚ)) / D = ((∑ x, ∑ y, ∑ z, f x y z : ℕ) : ℚ) / D := by
  push_cast; rfl

section Value
variable (P : StarParams) (σ : P.Translation) {a : ℕ} {N Q : ℕ} (eqv : P.Errors ≃ Fin N)
  (S : Fin Q → Fin N × Fin N)

/-- **The THR numerator**: the sampled points (center, filter seed, sample, row `(g, p)`) where the mask and the
reported modular row hold. -/
def thrNum (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n)) (FP : GapParams)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) : ℕ :=
  ∑ c : {c // P.IsCenter σ c}, ∑ e : GapSeed FP, ∑ l : Fin Q,
    ∑ gp : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den),
      (maskBits P σ carriers FP e (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
        (thrRhat P Cs algorithm den report gp.1 gp.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)).toNat

/-- **The THR denominator**: `|𝒫|·|Z|·|E|·Q`. -/
def thrDen (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (FP : GapParams)
    (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) : ℕ :=
  Fintype.card (PrimeIndex (thrCutoff P Cs algorithm den)) * Fintype.card {c // P.IsCenter σ c} *
    Fintype.card (GapSeed FP) * Q

theorem thrValueBits_numden (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ) :
    thrValueBits P σ eqv S Cs carriers FP algorithm den report =
      (thrNum P σ eqv S Cs carriers FP algorithm den report : ℚ) / thrDen P σ (Q := Q) Cs FP algorithm den := by
  unfold thrValueBits thrNum thrDen
  simp only [bitQ_mul]
  rw [sum4_div]
  congr 1
  push_cast
  ring

/-- **The SYM numerator**: the sampled points (center, filter and list seeds, sample) where the mask and the reported
conjunction hold. -/
def symNum (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n)) (FP : GapParams)
    (Pl : FlatListParams) : ℕ :=
  ∑ c : {c // P.IsCenter σ c}, ∑ s : GapSeed FP × Pl.FlatSeed, ∑ l : Fin Q,
    (maskBits P σ carriers FP s.1 (P.point c.1 (eqv.symm (S l).1) (eqv.symm (S l).2))).toNat *
      (symRhatFast P Cs Pl s.2 c.1 (eqv.symm (S l).1) (eqv.symm (S l).2)).toNat

/-- **The SYM denominator**: `|Z|·|E × E'|·Q`. -/
def symDen (FP : GapParams) (Pl : FlatListParams) : ℕ :=
  Fintype.card {c // P.IsCenter σ c} * Fintype.card (GapSeed FP × Pl.FlatSeed) * Q

theorem symValueBits_numden (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) :
    symValueBits P σ eqv S Cs carriers FP Pl =
      (symNum P σ eqv S Cs carriers FP Pl : ℚ) / symDen P σ (Q := Q) FP Pl := by
  unfold symValueBits symNum symDen
  simp only [bitQ_mul]
  rw [sum3_div]
  push_cast
  rfl

end Value

theorem sum_card_zero {α : Type} [Fintype α] (h : Fintype.card α = 0) (f : α → ℕ) : ∑ x, f x = 0 := by
  haveI := Fintype.card_eq_zero_iff.mp h
  simp

theorem thrNum_zero (P : StarParams) (σ : P.Translation) {a N Q : ℕ} (eqv : P.Errors ≃ Fin N)
    (S : Fin Q → Fin N × Fin N) (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den : ℕ) (report : List Bool → ℕ)
    (h : thrDen P σ (Q := Q) Cs FP algorithm den = 0) : thrNum P σ eqv S Cs carriers FP algorithm den report = 0 := by
  unfold thrDen at h
  simp only [Nat.mul_eq_zero] at h
  unfold thrNum
  rcases h with ((hP | hZ) | hE) | hQ
  · refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun e _ => Finset.sum_eq_zero (fun l _ => ?_)))
    exact sum_card_zero (by rw [Fintype.card_prod, hP, mul_zero]) _
  · exact sum_card_zero hZ _
  · exact Finset.sum_eq_zero (fun c _ => sum_card_zero hE _)
  · refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun e _ => ?_))
    exact sum_card_zero (by rw [Fintype.card_fin, hQ]) _

theorem symNum_zero (P : StarParams) (σ : P.Translation) {a N Q : ℕ} (eqv : P.Errors ≃ Fin N)
    (S : Fin Q → Fin N × Fin N) (Cs : Fin a → NormalizedSymmetricThresholdCircuit P.n) (carriers : List (Carrier P.n))
    (FP : GapParams) (Pl : FlatListParams) (h : symDen P σ (Q := Q) FP Pl = 0) :
    symNum P σ eqv S Cs carriers FP Pl = 0 := by
  unfold symDen at h
  simp only [Nat.mul_eq_zero] at h
  unfold symNum
  rcases h with (hZ | hE) | hQ
  · exact sum_card_zero hZ _
  · exact Finset.sum_eq_zero (fun c _ => sum_card_zero hE _)
  · refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun e _ => ?_))
    exact sum_card_zero (by rw [Fintype.card_fin, hQ]) _

/-! ## At a request -/

section Req
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm)

/-- **The final pass's numerator** at a request (the greedy sampler's sample). -/
def numOf : PrimRequest → ℕ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        symNum (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
          ((SeedFix.greedySampler I alg).symS Cs carriers translation hs).eqv
          ((SeedFix.greedySampler I alg).symS Cs carriers translation hs).S Cs carriers (I.filterParams .sym n)
          (symListParams I n _ Cs carriers)
      else 0
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        thrNum (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
          ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs).eqv
          ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs).S Cs carriers (I.filterParams .thr n) alg
          (thrCallDen alg I hs Cs) (thrCallReportBits alg I hs Cs carriers translation)
      else 0

/-- The product of the counts at a request (`0` only when the numerator's index set is empty). -/
def denRaw : PrimRequest → ℕ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        symDen (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
          (Q := ((SeedFix.greedySampler I alg).symS Cs carriers translation hs).Q) (I.filterParams .sym n)
          (symListParams I n _ Cs carriers)
      else 1
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : I.StarAt n then
        thrDen (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
          (Q := ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs).Q) Cs (I.filterParams .thr n) alg
          (thrCallDen alg I hs Cs)
      else 1

/-- **The final pass's denominator** at a request: the product of the counts, at least `1`. -/
def denOf (req : PrimRequest) : ℕ := max (denRaw I alg req) 1

theorem denOf_pos (req : PrimRequest) : 0 < denOf I alg req := by unfold denOf; omega

theorem num_zero_of_raw : ∀ req : PrimRequest, denRaw I alg req = 0 → numOf I alg req = 0
  | ⟨n, .sym, a, ha, Cs, carriers, translation⟩, h => by
    simp only [denRaw] at h
    simp only [numOf]
    by_cases hs : I.StarAt n
    · simp only [dif_pos hs] at h ⊢; exact symNum_zero _ _ _ _ _ _ _ _ h
    · simp only [dif_neg hs] at h; exact absurd h (by norm_num)
  | ⟨n, .thr, a, ha, Cs, carriers, translation⟩, h => by
    simp only [denRaw] at h
    simp only [numOf]
    by_cases hs : I.StarAt n
    · simp only [dif_pos hs] at h ⊢; exact thrNum_zero _ _ _ _ _ _ _ _ _ _ h
    · simp only [dif_neg hs] at h; exact absurd h (by norm_num)

/-- The printed value is `numOf / denRaw`. -/
theorem value_raw : ∀ req : PrimRequest,
    ((numOf I alg req : ℕ) : ℚ) / (denRaw I alg req : ℕ) = SeedFix.greedyValue I alg req
  | ⟨n, .sym, a, ha, Cs, carriers, translation⟩ => by
    simp only [numOf, denRaw, SeedFix.greedyValue, fusedValueBits]
    by_cases hs : I.StarAt n
    · simp only [dif_pos hs]
      unfold symCallValueBits
      rw [symValueBits_numden]
    · simp [dif_neg hs]
  | ⟨n, .thr, a, ha, Cs, carriers, translation⟩ => by
    simp only [numOf, denRaw, SeedFix.greedyValue, fusedValueBits]
    by_cases hs : I.StarAt n
    · simp only [dif_pos hs]
      unfold thrCallValueBits
      rw [thrValueBits_numden]
    · simp [dif_neg hs]

/-- **The printed value is `numOf / denOf`.** -/
theorem value_eq (req : PrimRequest) :
    ((numOf I alg req : ℕ) : ℚ) / (denOf I alg req : ℕ) = SeedFix.greedyValue I alg req := by
  rw [← value_raw I alg req]
  unfold denOf
  by_cases h : denRaw I alg req = 0
  · rw [h, num_zero_of_raw I alg req h]; simp
  · rw [max_eq_left (by omega)]

end Req

end NearCubicWires.WireExponent3_5.FinalPass.NumDen
