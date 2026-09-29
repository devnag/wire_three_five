import Proof.Wire_3_5.FinalPass.SymPool

/-! # The child's printed objective: its shape from the batch's (mode-generic)

"`V=\sum_\nu c_\nu\prod_{j\le m}p_{\nu,j}` [...] where `m,d≥1`, each `p_{ν,j}` is a Boolean `𝔽₂` polynomial given as a
multilinear monomial list of degree at most `d` in the threshold pool, and each `c_ν` has at most `b` bits"
(alg:compiler, P3:1882-1887): the child expression `sampTerms P nT R batch plen pre` (P3:3011-3016: the coefficient
term `(−N²)^{|β|}·count` times the eight entries' rows) inherits from the batch
* every factor's property (degree, atoms): **`facOk_sampTerms`**;
* the exact factor count `8·Σ_{r<R} f r` from the rows' counts `f r`: **`uniform_sampTerms`**;
* the coefficients' size `N^{16}·2^{8ℓ}` from `±1` row coefficients: **`coefLe_sampTerms`**;
* the term count `n_T·N^8·2^{8ℓ}·2^8` from single-term rows: **`length_sampTerms_le`**.
Paper quantities of the main types: the child's `m`, `d`, `b` and `A` of alg:compiler. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SampShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Sampler Finset

/-! ## Factors -/

/-- Every factor of every term has the property `Φ`. -/
def FacOk (Φ : F2Poly ℕ → Prop) (V : SExpr) : Prop := ∀ t ∈ V, ∀ p ∈ t.2, Φ p

theorem FacOk.smul {Φ : F2Poly ℕ → Prop} {V W : SExpr} (hV : FacOk Φ V) (hW : FacOk Φ W) : FacOk Φ (smul V W) := by
  intro t ht p hp
  unfold SeedFix.smul at ht
  obtain ⟨x, hx, hxt⟩ := List.mem_flatMap.mp ht
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxt
  rcases List.mem_append.mp hp with h | h
  · exact hV x hx p h
  · exact hW y hy p h

theorem FacOk.sfold {Φ : F2Poly ℕ → Prop} : ∀ (L : List SExpr) (A : SExpr), FacOk Φ A → (∀ V ∈ L, FacOk Φ V) →
    FacOk Φ (SeedFix.sfold A L)
  | [], A, hA, _ => by simpa [SeedFix.sfold] using hA
  | V :: L, A, hA, hL => by
    show FacOk Φ (SeedFix.sfold (SeedFix.smul A V) L)
    exact FacOk.sfold L _ (hA.smul (hL V List.mem_cons_self)) (fun W hW => hL W (List.mem_cons_of_mem _ hW))

theorem FacOk.flatMap {Φ : F2Poly ℕ → Prop} {β : Type} (l : List β) (f : β → SExpr) (h : ∀ b ∈ l, FacOk Φ (f b)) :
    FacOk Φ (l.flatMap f) := by
  intro t ht
  obtain ⟨b, hb, htb⟩ := List.mem_flatMap.mp ht
  exact h b hb t htb

theorem row_facOk {Φ : F2Poly ℕ → Prop} (batch : List SExpr) (hb : ∀ V ∈ batch, FacOk Φ V) (i : ℕ) :
    FacOk Φ (batch.getD i []) := by
  rcases Nat.lt_or_ge i batch.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]; exact hb _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; intro t ht; simp at ht

/-- **Every factor of the child expression is a factor of a batch row.** -/
theorem facOk_sampTerms (Φ : F2Poly ℕ → Prop) (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (plen pre : ℕ)
    (hb : ∀ V ∈ batch, FacOk Φ V) : FacOk Φ (sampTerms P nT R batch plen pre) := by
  unfold sampTerms sampTermsT
  refine FacOk.flatMap _ _ fun t _ => FacOk.flatMap _ _ fun w _ => FacOk.flatMap _ _ fun α' _ => ?_
  split_ifs
  · refine FacOk.flatMap _ _ fun β' _ => ?_
    split_ifs
    · intro t ht; simp at ht
    · unfold termsAt
      refine FacOk.sfold _ _ (by intro t ht p hp; simp [coefTerm] at ht; rw [ht] at hp; simp at hp) ?_
      intro V hV
      unfold walkRows at hV
      obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hV
      unfold entryRows at hk
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hk
      exact row_facOk batch hb _
  · intro t ht; simp at ht

/-! ## The factor count -/

theorem uniform_sfold_idx : ∀ (L : List SExpr) (cs : List ℕ) (A : SExpr) (a : ℕ), List.Forall₂ Uniform L cs →
    Uniform A a → Uniform (SeedFix.sfold A L) (a + cs.sum)
  | [], [], A, a, _, hA => by simpa [SeedFix.sfold] using hA
  | V :: L, c :: cs, A, a, h, hA => by
    obtain ⟨hVc, hL⟩ := List.forall₂_cons.mp h
    show Uniform (SeedFix.sfold (SeedFix.smul A V) L) _
    have := uniform_sfold_idx L cs (SeedFix.smul A V) (a + c) hL (hA.smul hVc)
    rw [List.sum_cons, ← Nat.add_assoc]
    exact this

theorem forall2_flatMap {β : Type} (l : List β) (F : β → List SExpr) (G : β → List ℕ)
    (h : ∀ b ∈ l, List.Forall₂ Uniform (F b) (G b)) : List.Forall₂ Uniform (l.flatMap F) (l.flatMap G) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons b l ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.rel_append (h b List.mem_cons_self) (ih fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))

theorem sum_flatMap_const {α : Type} (m : List α) (l : List ℕ) : (m.flatMap fun _ => l).sum = m.length * l.sum := by
  induction m with
  | nil => simp
  | cons x m ih => rw [List.flatMap_cons, List.sum_append, ih, List.length_cons]; ring

/-- **The child expression has exactly `8·Σ_{r<R} f r` factors per term** when row `r` of every entry has `f r`. -/
theorem uniform_sampTerms (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (plen pre : ℕ) (f : ℕ → ℕ)
    (hf : ∀ i r, r < R → Uniform (batch.getD (i * R + r) []) (f r)) :
    Uniform (sampTerms P nT R batch plen pre) (8 * ((List.range R).map f).sum) := by
  unfold sampTerms sampTermsT
  refine Uniform.flatMap _ _ _ fun t _ => Uniform.flatMap _ _ _ fun w _ => Uniform.flatMap _ _ _ fun α' _ => ?_
  split_ifs
  · refine Uniform.flatMap _ _ _ fun β' _ => ?_
    split_ifs
    · intro t ht; simp at ht
    · unfold termsAt
      have hA : Uniform (coefTerm P (fun k => finTwoEquiv (β' k)) (cntL P plen pre (fun k => α' k) w
          (fun k => finTwoEquiv (β' k)))) 0 := by
        intro t ht; simp [coefTerm] at ht; subst ht; rfl
      have h2 : List.Forall₂ Uniform (walkRows P batch R w t)
          ((List.finRange 8).flatMap fun _ => (List.range R).map f) := by
        unfold walkRows
        refine forall2_flatMap _ _ _ fun k _ => ?_
        unfold entryRows
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.forall₂_same.mpr fun r hr => hf _ r (List.mem_range.mp hr)
      have h3 := uniform_sfold_idx _ _ _ 0 h2 hA
      have e : ((List.finRange 8).flatMap fun _ => (List.range R).map f).sum = 8 * ((List.range R).map f).sum := by
        rw [sum_flatMap_const]; simp
      rw [e, Nat.zero_add] at h3
      exact h3
  · intro t ht; simp at ht

end NearCubicWires.WireExponent3_5.FinalPass.SampShape

