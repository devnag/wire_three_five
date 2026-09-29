import Proof.Wire_3_5.UnionMachine.SchedLoop

/-! # C6, part 5a: the slack check as integer comparisons (P3:3484-3491)

The union machine decides `tr:thresholds` (with the slack of) from its integer accumulators: each term's
coefficient `c` scaled by `s⁴` is an INTEGER (`coeff_scaled_int`: `c = κ_j∏_k F_{j,k}` with `κ_j ∈ ℤ` and every
factor `F·s ∈ ℤ`, since the grid mass `Λ̄` is a natural number, P3:3399-3403), and the rounded answers are
`m/2^p` with `m = ⌊v·2^p⌋ ∈ ℤ`. Then `V̂' = Z_V/(s⁴·2^p·2M)` with the integer `Z_V = Σ (c·s⁴)·m`
(`VhatQ_eq`), and the three tests are integer comparisons against integer thresholds
(**`slackCheck_int`**):
`Z_V ≤ ⌊s⁴2^p·2M·(2v₀+δ)⌋`, `Z_Q ≤ ⌊s⁴2^p·2M·(1+v₀+δ)⌋`, `⌈s⁴2^p·M·(τ−δ)⌉ ≤ Z_μ`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Bridge
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer

/-- A rational is an integer. -/
def IsIntQ (x : ℚ) : Prop := ∃ z : ℤ, x = z

theorem IsIntQ.mul {x y : ℚ} (hx : IsIntQ x) (hy : IsIntQ y) : IsIntQ (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, by push_cast; ring⟩

/-- The integer value of an integral rational. -/
theorem IsIntQ.num_eq {x : ℚ} (hx : IsIntQ x) : (x.num : ℚ) = x := by
  obtain ⟨z, rfl⟩ := hx; simp

section Scaled
variable {α : Type} (s : ℕ)

/-- A linear form whose values times `s` are integers. -/
def IntForm (w : α → ℚ) : Prop := ∀ a, IsIntQ (w a * s)

/-- **Scaled coefficients are integers**: `κ_j ∈ ℤ` and every factor an `IntForm` make `c·s⁴` an integer. -/
theorem coeff_scaled_int (P : Poly4Q α) (hκ : ∀ j, IsIntQ (P.κ j)) (hF : ∀ j k, IntForm s (P.F j k)) (j : Fin 4)
    (t : Fin 4 → α) : IsIntQ (P.coeff j t * (s : ℚ) ^ 4) := by
  unfold Poly4Q.coeff
  rw [Fin.prod_univ_four]
  have e : P.κ j * (P.F j 0 (t 0) * P.F j 1 (t 1) * P.F j 2 (t 2) * P.F j 3 (t 3)) * (s : ℚ) ^ 4 =
      P.κ j * ((P.F j 0 (t 0) * s) * (P.F j 1 (t 1) * s) * (P.F j 2 (t 2) * s) * (P.F j 3 (t 3) * s)) := by ring
  rw [e]
  exact (hκ j).mul ((((hF j 0 (t 0)).mul (hF j 1 (t 1))).mul (hF j 2 (t 2))).mul (hF j 3 (t 3)))

end Scaled

/-! ## The check data's forms are integral -/

namespace CheckData
variable (D : UnionCheckData)

theorem wS_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (X : PcppVar D.pcpp) : IntForm D.s (D.wS X) := by
  intro a
  rcases a with u | (⟨Y, b⟩ | Y)
  · exact ⟨0, by simp [UnionCheckData.wS]⟩
  · by_cases h : Y = X
    · refine ⟨Λ * D.sign Y b, ?_⟩
      simp only [UnionCheckData.wS, h, if_true, hm]
      have : (D.s : ℚ) ≠ 0 := by exact_mod_cast (show D.s ≠ 0 by omega)
      field_simp
      push_cast; ring
    · exact ⟨0, by simp [UnionCheckData.wS, h]⟩
  · exact ⟨0, by simp [UnionCheckData.wS]⟩

theorem wOne_int : IntForm D.s D.wOne := by
  intro a
  rcases a with u | (p | Y)
  · exact ⟨D.s, by simp [UnionCheckData.wOne]⟩
  · exact ⟨0, by simp [UnionCheckData.wOne]⟩
  · exact ⟨0, by simp [UnionCheckData.wOne]⟩

theorem wE_int (X : PcppVar D.pcpp) : IntForm D.s (D.wE X) := by
  intro a
  rcases a with u | (p | Y)
  · exact ⟨0, by simp [UnionCheckData.wE]⟩
  · exact ⟨0, by simp [UnionCheckData.wE]⟩
  · by_cases h : Y = X
    · exact ⟨D.s, by simp [UnionCheckData.wE, h]⟩
    · exact ⟨0, by simp [UnionCheckData.wE, h]⟩

theorem polyV_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (j : Fin 4)
    (t : Fin 4 → D.AtomIx) : IsIntQ ((D.polyVAt pos).coeff j t * (D.s : ℚ) ^ 4) := by
  refine coeff_scaled_int D.s _ ?_ ?_ j t
  · intro j; unfold UnionCheckData.polyVAt polyVQ
    split_ifs <;> fin_cases j <;>
      first
        | (refine ⟨1, ?_⟩; norm_num; done)
        | (refine ⟨-2, ?_⟩; norm_num; done)
        | (refine ⟨0, ?_⟩; norm_num; done)
  · intro j k; unfold UnionCheckData.polyVAt polyVQ
    have hS := CheckData.wS_int D Λ hm hs (posVar D.pcpp pos.1 pos.2)
    have hO := CheckData.wOne_int D
    have hE := CheckData.wE_int D (posVar D.pcpp pos.1 pos.2)
    split_ifs <;> fin_cases j <;> fin_cases k <;> simpa

theorem polyQ_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (j : Fin 4)
    (t : Fin 4 → D.AtomIx) : IsIntQ ((D.polyQAt pos).coeff j t * (D.s : ℚ) ^ 4) := by
  refine coeff_scaled_int D.s _ ?_ ?_ j t
  · intro j; unfold UnionCheckData.polyQAt polyQQ
    fin_cases j <;> first | (refine ⟨1, ?_⟩; norm_num; done) | (refine ⟨0, ?_⟩; norm_num; done)
  · intro j k; unfold UnionCheckData.polyQAt polyQQ
    have hS := CheckData.wS_int D Λ hm hs (posVar D.pcpp pos.1 pos.2)
    have hO := CheckData.wOne_int D
    fin_cases j <;> fin_cases k <;> simpa

theorem polyMu_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (i : Fin (2 ^ D.pcpp.clauseBits)) (j : Fin 4)
    (t : Fin 4 → D.AtomIx) : IsIntQ ((D.polyMuAt i).coeff j t * (D.s : ℚ) ^ 4) := by
  refine coeff_scaled_int D.s _ ?_ ?_ j t
  · intro j; unfold UnionCheckData.polyMuAt polyMuQ litAQ litBQ
    fin_cases j <;> split_ifs <;> simp <;>
      first
        | (refine ⟨1, ?_⟩; norm_num; done)
        | (refine ⟨0, ?_⟩; norm_num; done)
        | (refine ⟨-1, ?_⟩; norm_num; done)
        | (refine ⟨2, ?_⟩; norm_num; done)
        | (refine ⟨-2, ?_⟩; norm_num; done)
  · intro j k; unfold UnionCheckData.polyMuAt polyMuQ
    have hX := CheckData.wS_int D Λ hm hs (posVar D.pcpp i 0)
    have hY := CheckData.wS_int D Λ hm hs (posVar D.pcpp i 1)
    have hO := CheckData.wOne_int D
    fin_cases j <;> fin_cases k <;> simpa

/-- Every `V` term's scaled coefficient is an integer. -/
theorem termsV_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) : ∀ t ∈ D.termsV, IsIntQ (t.1 * (D.s : ℚ) ^ 4) := by
  intro t ht
  obtain ⟨pos, j, u, -, rfl⟩ := (D.mem_termsV t).1 ht
  exact polyV_int D Λ hm hs pos j u

theorem termsQ_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) : ∀ t ∈ D.termsQ, IsIntQ (t.1 * (D.s : ℚ) ^ 4) := by
  intro t ht
  obtain ⟨pos, j, u, -, rfl⟩ := (D.mem_termsQ t).1 ht
  exact polyQ_int D Λ hm hs pos j u

theorem termsMu_int (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) : ∀ t ∈ D.termsMu, IsIntQ (t.1 * (D.s : ℚ) ^ 4) := by
  intro t ht
  obtain ⟨i, j, u, -, rfl⟩ := (D.mem_termsMu t).1 ht
  exact polyMu_int D Λ hm hs i j u

end CheckData

/-! ## Integer sums and integer thresholds -/

/-- **The scaled integer coefficient** `c·s⁴`. -/
def scaledZ (s : ℕ) (c : ℚ) : ℤ := (c * (s : ℚ) ^ 4).num

/-- **The integer accumulator** `Σ (c·s⁴)·m(r)` of a term list at integer answers `m`. -/
def zSum (s : ℕ) (terms : List (ℚ × PrimRequest)) (m : PrimRequest → ℤ) : ℤ :=
  (terms.map fun t => scaledZ s t.1 * m t.2).sum

theorem combine_scaled (s p : ℕ) (hs : 1 ≤ s) (terms : List (ℚ × PrimRequest)) (m : PrimRequest → ℤ)
    (hint : ∀ t ∈ terms, IsIntQ (t.1 * (s : ℚ) ^ 4)) :
    combine terms (fun r => (m r : ℚ) / 2 ^ p) = (zSum s terms m : ℚ) / ((s : ℚ) ^ 4 * 2 ^ p) := by
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
  induction terms with
  | nil => simp [combine, zSum]
  | cons t ts ih =>
    have h1 := (hint t (List.mem_cons_self ..)).num_eq
    have ih' := ih (fun u hu => hint u (List.mem_cons_of_mem _ hu))
    simp only [combine, zSum, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih']
    push_cast
    rw [show ((scaledZ s t.1 : ℤ) : ℚ) = t.1 * (s : ℚ) ^ 4 from h1]
    field_simp

/-- The positive scale of the `V`, `Q` tests: `s⁴·2^p·2M`. -/
def scaleVQ (D : UnionCheckData) (p : ℕ) : ℚ := (D.s : ℚ) ^ 4 * 2 ^ p * (2 ^ D.pcpp.clauseBits * 2)

/-- The positive scale of the `μ` test: `s⁴·2^p·M`. -/
def scaleMu (D : UnionCheckData) (p : ℕ) : ℚ := (D.s : ℚ) ^ 4 * 2 ^ p * 2 ^ D.pcpp.clauseBits

theorem le_div_iff_int (z : ℤ) (K X : ℚ) (hK : 0 < K) : (z : ℚ) / K ≤ X ↔ z ≤ ⌊K * X⌋ := by
  rw [div_le_iff₀ hK, Int.le_floor, mul_comm]

theorem div_ge_iff_int (z : ℤ) (K X : ℚ) (hK : 0 < K) : X ≤ (z : ℚ) / K ↔ ⌈K * X⌉ ≤ z := by
  rw [le_div_iff₀ hK, Int.ceil_le, mul_comm]

/-- **The slack check is integer arithmetic**: at rounded answers `m/2^p`, the three tests are the integer
accumulators against the integer thresholds `⌊s⁴2^p·2M·(2v₀+δ)⌋`, `⌊s⁴2^p·2M·(1+v₀+δ)⌋`, `⌈s⁴2^p·M·(τ−δ)⌉`. -/
theorem slackCheck_int (D : UnionCheckData) (Λ : ℕ) (hm : D.mass = Λ) (hs : 1 ≤ D.s) (p : ℕ) (m : PrimRequest → ℤ)
    (v0 τ δ : ℚ) (callOk : PrimRequest → Bool) :
    slackCheck D (fun r => (m r : ℚ) / 2 ^ p) v0 τ δ callOk =
      (D.signsOk && D.schedule.all callOk &&
        decide (zSum D.s D.termsV m ≤ ⌊scaleVQ D p * (2 * v0 + δ)⌋) &&
        decide (zSum D.s D.termsQ m ≤ ⌊scaleVQ D p * (1 + v0 + δ)⌋) &&
        decide (⌈scaleMu D p * (τ - δ)⌉ ≤ zSum D.s D.termsMu m)) := by
  have hs0 : (0 : ℚ) < (D.s : ℚ) := by exact_mod_cast (show 0 < D.s by omega)
  have hKV : 0 < scaleVQ D p := by unfold scaleVQ; positivity
  have hKM : 0 < scaleMu D p := by unfold scaleMu; positivity
  have eV : D.VhatQ (fun r => (m r : ℚ) / 2 ^ p) = (zSum D.s D.termsV m : ℚ) / scaleVQ D p := by
    unfold UnionCheckData.VhatQ scaleVQ
    rw [combine_scaled D.s p hs _ m (CheckData.termsV_int D Λ hm hs)]
    field_simp
  have eQ : D.QhatQ (fun r => (m r : ℚ) / 2 ^ p) = (zSum D.s D.termsQ m : ℚ) / scaleVQ D p := by
    unfold UnionCheckData.QhatQ scaleVQ
    rw [combine_scaled D.s p hs _ m (CheckData.termsQ_int D Λ hm hs)]
    field_simp
  have eM : D.μhatQ (fun r => (m r : ℚ) / 2 ^ p) = (zSum D.s D.termsMu m : ℚ) / scaleMu D p := by
    unfold UnionCheckData.μhatQ scaleMu
    rw [combine_scaled D.s p hs _ m (CheckData.termsMu_int D Λ hm hs)]
    field_simp
  unfold slackCheck
  rw [eV, eQ, eM]
  congr 1
  · congr 1
    · congr 1
      exact decide_eq_decide.mpr (le_div_iff_int _ _ _ hKV)
    · exact decide_eq_decide.mpr (by rw [show 1 + v0 + δ = 1 + v0 + δ from rfl]; exact le_div_iff_int _ _ _ hKV)
  · exact decide_eq_decide.mpr (div_ge_iff_int _ _ _ hKM)

/-! ## The call table of a term list -/

section Table
open NearCubicWires.WireExponent3_5.UnionMachine.Entry NearCubicWires.WireExponent3_5.UnionMachine.Sched
open NearCubicWires.WireExponent3_5.Cost
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

/-- The table entry of a term of test `k`: the sign and magnitude of `c·s⁴`, the request's word. -/
def entryOf (k : Fin 3) (s : ℕ) (t : ℚ × PrimRequest) : CallEntry :=
  ⟨k, decide (scaledZ s t.1 < 0), (scaledZ s t.1).natAbs, t.2.word⟩

/-- **The call table of an admissible term list** of test `k`. -/
def tableOfTerms (k : Fin 3) (s : ℕ) (T : List (ℚ × PrimRequest)) (h : ∀ t ∈ T, I.Call t.2) : List (TEntry I) :=
  T.pmap (fun t ht => (⟨entryOf k s t, ⟨t.2, ht⟩, rfl⟩ : TEntry I)) h

theorem signed_natAbs (z m : ℤ) : (if decide (z < 0) = true then (-1 : ℤ) else 1) * (z.natAbs : ℤ) * m = z * m := by
  by_cases hz : z < 0
  · simp only [hz, decide_true, if_true, Int.natCast_natAbs, abs_of_neg hz]; ring
  · simp only [hz, decide_false, Bool.false_eq_true, if_false, Int.natCast_natAbs, abs_of_nonneg (not_lt.mp hz)]
    ring

/-- An entry's signed term, from its entry and request only. -/
noncomputable def signedRaw (p : ℕ) (k' : Fin 3) (e : CallEntry) (r : PrimRequest) : ℤ :=
  if e.kind = k' then (if e.neg then -1 else 1) * (e.mag : ℤ) * ⌊P.value r * 2 ^ p⌋ else 0

theorem signedTerm_raw (p : ℕ) (k' : Fin 3) (x : TEntry I) : signedTerm P p k' x = signedRaw P p k' x.e x.req.1 := rfl

/-- **The table's signed terms sum to the integer accumulator** on its own test, and to `0` on the others. -/
theorem table_sum (k k' : Fin 3) (s p : ℕ) (T : List (ℚ × PrimRequest)) (h : ∀ t ∈ T, I.Call t.2) :
    ((tableOfTerms k s T h).map (signedTerm P p k')).sum =
      if k = k' then zSum s T (fun r => ⌊P.value r * 2 ^ p⌋) else 0 := by
  unfold tableOfTerms zSum
  rw [List.map_pmap]
  simp only [signedTerm_raw]
  rw [List.pmap_eq_map (f := fun t => signedRaw P p k' (entryOf k s t) t.2)]
  split_ifs with hk
  · subst hk
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [signedRaw, entryOf, if_true]
    exact signed_natAbs _ _
  · apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨t, _, rfl⟩ := hx
    simp [signedRaw, entryOf, hk]

end Table


end NearCubicWires.WireExponent3_5.UnionMachine.Bridge
