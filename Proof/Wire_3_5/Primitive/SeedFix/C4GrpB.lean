import Proof.Wire_3_5.Primitive.SeedFix.C4GrpA

/-! # C4.K side conditions, part 2: the sizes of the group's words (the T-b), generic in the batch

P3:3011-3016, 3034-3038 (the printed conditional objective: each group is the coefficient `±2^e` times the fetched
rows, the output the groups of the counter values so far): with the batch's rows of coefficient `±1` (every product
keeps the coefficient's size), each fold state after `m` rows has at most `b^m` terms of at most `T₀ + m·b` bits each,
`b = bsz batch` the largest row word. So every fold state, product and emitted group is below
`Fs = b^{8R}·(T₀ + 8R·b + 1) + 1`, and the output before counter value `j` below `j·b^{8R}·(T₀ + 8R·b + 1) + 1`.

* `coefWord_len`, `termWord_len`, `exprWord_len`, `term_le_expr`, `len_le_expr`, `smul_len`, `smul_term`, `expr_le`,
  `Inv`, `inv_smul`, `inv_mono`, `inv_foldl`, `bsz`, `bsz_mem`, `bsz_pos`.

Paper quantity of the main type: the sizes of the printed objective's groups. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Grp
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.ListMachine.Rec (coefWord termWord exprWord polyWord)
open Split Cells Valid Cons FetchAll FetchCells Emit JBank JStages JBody SplitT JEnum

/-! ## Word sizes -/

theorem coefWord_len (c : ℤ) : (coefWord c).length = 2 * (c.natAbs.bits.length + 1) + 1 := by
  simp [coefWord]

theorem termWord_len (t : ℤ × List (List (List ℕ))) :
    (termWord t).length = (coefWord t.1).length + (t.2.flatMap (fun f => true :: polyWord f)).length + 1 := by
  unfold termWord
  simp only [List.length_append, List.length_singleton]
  omega

theorem exprWord_len (V : SExpr) : (exprWord V).length = (V.map fun t => (termWord t).length + 1).sum + 1 := by
  induction V with
  | nil => simp [exprWord]
  | cons t V ih =>
    simp only [exprWord, List.flatMap_cons, List.length_append, List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem term_le_expr {V : SExpr} {t : ℤ × List (List (List ℕ))} (ht : t ∈ V) :
    (termWord t).length + 1 ≤ (exprWord V).length := by
  induction V with
  | nil => simp at ht
  | cons u V ih =>
    rw [exprWord_len] at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ht with h | h
    · subst h; omega
    · have := ih h; omega

theorem len_le_expr (V : SExpr) : V.length ≤ (exprWord V).length := by
  induction V with
  | nil => simp
  | cons t V ih =>
    rw [exprWord_len] at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem smul_len (A V : SExpr) : (smul A V).length = A.length * V.length := by
  induction A with
  | nil => simp [smul]
  | cons a A ih =>
    simp only [smul, List.flatMap_cons, List.length_append, List.length_map, List.length_cons] at ih ⊢
    rw [ih]; ring

/-- **A product term's word**: the row's coefficient is `±1`, so the product's coefficient word keeps its size and
the factor records add up. -/
theorem smul_term (A V : SExpr) (T : ℕ) (hA : ∀ a ∈ A, (termWord a).length ≤ T)
    (hV : ∀ b ∈ V, b.1 = 1 ∨ b.1 = -1) : ∀ t ∈ smul A V, (termWord t).length ≤ T + (exprWord V).length := by
  intro t ht
  unfold smul at ht
  obtain ⟨a, ha, ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
  have h1 := hA a ha
  have h2 := term_le_expr hb
  rw [termWord_len] at h1 h2 ⊢
  have hc : (coefWord (a.1 * b.1)).length = (coefWord a.1).length := by
    rcases hV b hb with h | h <;> rw [h] <;> simp [coefWord_len]
  rw [hc]
  simp only [List.flatMap_append, List.length_append]
  omega

theorem expr_le (W : SExpr) (T : ℕ) (hW : ∀ t ∈ W, (termWord t).length ≤ T) :
    (exprWord W).length ≤ W.length * (T + 1) + 1 := by
  induction W with
  | nil => simp [exprWord]
  | cons t W ih =>
    rw [exprWord_len] at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hW t List.mem_cons_self
    have h2 := ih (fun u hu => hW u (List.mem_cons_of_mem _ hu))
    nlinarith

/-! ## The fold's invariant -/

/-- A fold state's size: at most `c` terms, each of at most `T` bits. -/
def Inv (A : SExpr) (c T : ℕ) : Prop := A.length ≤ c ∧ ∀ a ∈ A, (termWord a).length ≤ T

theorem inv_mono {A : SExpr} {c T c' T' : ℕ} (h : Inv A c T) (hc : c ≤ c') (hT : T ≤ T') : Inv A c' T' :=
  ⟨le_trans h.1 hc, fun a ha => le_trans (h.2 a ha) hT⟩

theorem inv_smul {A : SExpr} {c T : ℕ} (h : Inv A c T) (V : SExpr) (b : ℕ) (hb : (exprWord V).length ≤ b)
    (hV : ∀ x ∈ V, x.1 = 1 ∨ x.1 = -1) : Inv (smul A V) (c * b) (T + b) :=
  ⟨by rw [smul_len]; exact Nat.mul_le_mul h.1 (le_trans (len_le_expr V) hb),
   fun t ht => le_trans (smul_term A V T h.2 hV t ht) (Nat.add_le_add_left hb T)⟩

theorem inv_expr {A : SExpr} {c T : ℕ} (h : Inv A c T) : (exprWord A).length ≤ c * (T + 1) + 1 :=
  le_trans (expr_le A T h.2) (Nat.add_le_add_right (Nat.mul_le_mul_right _ h.1) 1)

/-- The rows' condition: a word below `b`, coefficients `±1`. -/
def RowOk (b : ℕ) (V : SExpr) : Prop := (exprWord V).length ≤ b ∧ ∀ x ∈ V, x.1 = 1 ∨ x.1 = -1

theorem inv_foldl (b : ℕ) : ∀ (rs : List SExpr) (s : FoldSt) (c T : ℕ), Inv s.A c T → (∀ V ∈ rs, RowOk b V) →
    Inv (rs.foldl FoldSt.step s).A (c * b ^ rs.length) (T + rs.length * b)
  | [], s, c, T, h, _ => by simpa using h
  | V :: rs, s, c, T, h, hr => by
    rw [List.foldl_cons]
    have h1 := inv_smul h V b (hr V List.mem_cons_self).1 (hr V List.mem_cons_self).2
    have h2 := inv_foldl b rs (FoldSt.step s V) (c * b) (T + b) h1 (fun W hW => hr W (List.mem_cons_of_mem _ hW))
    refine inv_mono h2 (le_of_eq ?_) (le_of_eq ?_)
    · simp only [List.length_cons, pow_succ]; ring
    · simp only [List.length_cons]; ring

theorem inv_sfold (b : ℕ) : ∀ (rs : List SExpr) (A : SExpr) (c T : ℕ), Inv A c T → (∀ V ∈ rs, RowOk b V) →
    Inv (sfold A rs) (c * b ^ rs.length) (T + rs.length * b)
  | [], A, c, T, h, _ => by simpa [sfold] using h
  | V :: rs, A, c, T, h, hr => by
    have h1 := inv_smul h V b (hr V List.mem_cons_self).1 (hr V List.mem_cons_self).2
    have h2 := inv_sfold b rs (smul A V) (c * b) (T + b) h1 (fun W hW => hr W (List.mem_cons_of_mem _ hW))
    refine inv_mono h2 (le_of_eq ?_) (le_of_eq ?_)
    · simp only [List.length_cons, pow_succ]; ring
    · simp only [List.length_cons]; ring

/-! ## The batch's size -/

/-- **`bsz batch`**: the largest row word (at least `1`). -/
def bsz (batch : List SExpr) : ℕ := (batch.map fun V => (exprWord V).length).foldr max 1

theorem bsz_pos (batch : List SExpr) : 1 ≤ bsz batch := by
  unfold bsz
  induction batch with
  | nil => simp
  | cons V batch ih => simp only [List.map_cons, List.foldr_cons]; exact le_trans ih (le_max_right _ _)

theorem bsz_mem {batch : List SExpr} {V : SExpr} (hV : V ∈ batch) : (exprWord V).length ≤ bsz batch := by
  unfold bsz
  induction batch with
  | nil => simp at hV
  | cons W batch ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hV with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- Every row of the batch's entries is below `bsz batch` with coefficients `±1`. -/
theorem chunk_rowOk (N nT R : ℕ) (batch : List SExpr) (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (e : ℕ) :
    ∀ V ∈ (JLink.chunk N nT R batch).getD e [], RowOk (bsz batch) V := by
  intro V hV
  rcases chunk_row N nT R batch e V hV with h | h
  · subst h
    exact ⟨by simpa [exprWord] using bsz_pos batch, by simp⟩
  · exact ⟨bsz_mem h, hpm V h⟩

end NearCubicWires.WireExponent3_5.PrimT.C4Grp
