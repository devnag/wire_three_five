import Proof.Wire_3_5.Primitive.Writers.PopLink
import Proof.Wire_3_5.Primitive.Writers.WriterIface

/-! # (P-b): the batch's shape, part 1: generic (rows from requests) and the three request kinds

The compiler's admissible requests (`C3Req.Pre`, alg:compiler P3:1886-1906) need the printed objective's shape: every
term of a row has a fixed number of factors, every factor's monomials have bounded length and atoms inside the pool's
corner range, the coefficients are `±1`, and the rows have boundedly many terms. The rows are C2's reference
expressions of the batch's requests (`refOf`, concatenated by `groupExpr`); this part proves the shape once per request
kind (FILTER `filtRefC`, POP `popRefC`, RADIX `radRefC`) and lifts it to `batchExprs (batchOf …)`, generic in the
batch's groups.

Paper quantity of the main types: the printed rows' factor counts, degrees, atoms, coefficients and term counts (the
row expressions of row:filter, row:pop, row:radix, P3:1496-1526, 2608-2614). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.ListMachine.Row

/-! ## Factors -/

/-- A factor's shape: every monomial has at most `D` atoms, each below `A`. -/
def PolyOk (D A : ℕ) (p : Poly) : Prop := ∀ mono ∈ p, mono.length ≤ D ∧ ∀ x ∈ mono, x < A

theorem PolyOk.mono {D D' A A' : ℕ} {p : Poly} (h : PolyOk D A p) (hD : D ≤ D') (hA : A ≤ A') : PolyOk D' A' p :=
  fun m hm => ⟨(h m hm).1.trans hD, fun x hx => lt_of_lt_of_le ((h m hm).2 x hx) hA⟩

/-- A population's labels: at least `4L` of them, all below `A`. -/
def LabsOk (L : ℕ) (labs : List ℕ) (A : ℕ) : Prop := 4 * L ≤ labs.length ∧ ∀ x ∈ labs, x < A

/-- **An interpolated factor's shape**: its monomials are supports of degree `≤ d` over the `4L` corner positions,
renamed through the labels. -/
theorem factorPoly_ok (f : List Bool → Bool) (L d : ℕ) (labs : List ℕ) (A : ℕ) (h : LabsOk L labs A) :
    PolyOk d A (factorPoly f (4 * L) d labs) := by
  intro m hm
  unfold factorPoly at hm
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hm
  unfold ListMachine.Interp.interpPrint at hS
  have hS' := ListMachine.Interp.mem_monos (List.mem_filter.mp hS).1
  refine ⟨by simpa using hS'.2.2, fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hi' : i < labs.length := lt_of_lt_of_le (hS'.2.1 i hi) h.1
  unfold ListMachine.Print.labOf
  rw [List.getD_eq_getElem _ _ hi']
  exact h.2 _ (List.getElem_mem hi')

/-- The corner labels of a population at star row `row`: `4(row+1)·G` bounds them. -/
theorem labsOf_lt (G row : ℕ) (gis : List ℕ) (hg : ∀ gi ∈ gis, gi < G) :
    ∀ x ∈ CompilerMachine.Pool.labsOf G row gis, x < 4 * (row + 1) * G := by
  intro x hx
  unfold CompilerMachine.Pool.labsOf at hx
  obtain ⟨gi, hgi, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  have h1 := hg gi hgi
  have h2 : k < 4 := List.mem_range.mp hk
  unfold CompilerMachine.Pool.poolIndex
  have : (4 * row + k) * G + gi < (4 * row + k + 1) * G := by nlinarith
  have h3 : (4 * row + k + 1) * G ≤ 4 * (row + 1) * G := Nat.mul_le_mul_right _ (by omega)
  omega

theorem labsOf_ok (G row : ℕ) (gis : List ℕ) (L : ℕ) (hL : L ≤ gis.length) (hg : ∀ gi ∈ gis, gi < G) :
    LabsOk L (CompilerMachine.Pool.labsOf G row gis) (4 * (row + 1) * G) :=
  ⟨by rw [labsOf_length]; omega, labsOf_lt G row gis hg⟩

/-! ## From requests to rows -/

theorem mem_groupExpr {g : List RowReq} {t : ℤ × List Poly} : t ∈ groupExpr g ↔ ∃ r ∈ g, t ∈ refOf r := by
  unfold groupExpr
  simp only [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨V, ⟨r, hr, rfl⟩, ht⟩; exact ⟨r, hr, ht⟩
  · rintro ⟨r, hr, ht⟩; exact ⟨_, ⟨r, hr, rfl⟩, ht⟩

theorem groupExpr_length (g : List RowReq) : (groupExpr g).length = (g.map fun r => (refOf r).length).sum := by
  unfold groupExpr
  rw [List.length_flatten, List.map_map]
  rfl

theorem groupExpr_nil : groupExpr [] = [] := rfl

/-- A property of every term of every request of a batch holds of every term of every row. -/
theorem terms_of_reqs (Q : ℤ × List Poly → Prop) (bl : List (List RowReq))
    (h : ∀ g ∈ bl, ∀ r ∈ g, ∀ t ∈ refOf r, Q t) : ∀ V ∈ batchExprs bl, ∀ t ∈ V, Q t := by
  intro V hV t ht
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hV
  obtain ⟨r, hr, ht'⟩ := mem_groupExpr.mp ht
  exact h g hg r hr t ht'

/-- A row's term count from its requests'. -/
theorem rows_length_le (T : ℕ) (bl : List (List RowReq)) (h : ∀ g ∈ bl, (g.map fun r => (refOf r).length).sum ≤ T) :
    ∀ V ∈ batchExprs bl, V.length ≤ T := by
  intro V hV
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hV
  rw [groupExpr_length]
  exact h g hg

theorem sum_map_le_card {α : Type} (l : List α) (f : α → ℕ) (T : ℕ) (h : ∀ x ∈ l, f x ≤ T) :
    (l.map f).sum ≤ l.length * T := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    nlinarith

theorem batchOf_length (nT N R : ℕ) (grp : ℕ → ℕ → List (List RowReq)) (hR : ∀ t row, (grp t row).length = R) :
    (batchOf nT N grp).length = nT * N ^ 2 * R := by
  unfold batchOf
  rw [List.length_flatMap]
  simp only [hR, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]

/-- **Factor counts by row position**: row `r` of every entry has exactly `f r` factors in each term, when each
request of that row does. -/
theorem rows_uniform (nT N R : ℕ) (grp : ℕ → ℕ → List (List RowReq)) (f : ℕ → ℕ)
    (hR : ∀ t row, (grp t row).length = R)
    (h : ∀ t row r, t < nT → row < N ^ 2 → r < R → ∀ q ∈ (grp t row).getD r [], SeedFix.Uniform (refOf q) (f r)) :
    ∀ i r, r < R → SeedFix.Uniform ((batchExprs (batchOf nT N grp)).getD (i * R + r) []) (f r) := by
  intro i r hr
  have hmap : (batchExprs (batchOf nT N grp)).getD (i * R + r) [] =
      groupExpr ((batchOf nT N grp).getD (i * R + r) []) := by
    unfold batchExprs
    rw [← groupExpr_nil, List.getD_map]
  rw [hmap]
  by_cases hi : i < nT * N ^ 2
  · have hN : 0 < N ^ 2 := by
      rcases Nat.eq_zero_or_pos (N ^ 2) with h0 | h0
      · rw [h0, Nat.mul_zero] at hi; omega
      · exact h0
    have ht : i / N ^ 2 < nT := by
      rw [Nat.div_lt_iff_lt_mul hN]; exact hi
    have hrow : i % N ^ 2 < N ^ 2 := Nat.mod_lt _ hN
    have e : i = i / N ^ 2 * N ^ 2 + i % N ^ 2 := (Nat.div_add_mod' i (N ^ 2)).symm
    have hg := batchOf_getD nT N R grp hR (i / N ^ 2) (i % N ^ 2) r ht hrow hr
    rw [← e] at hg
    rw [hg]
    intro t htm
    obtain ⟨q, hq, htq⟩ := mem_groupExpr.mp htm
    exact h _ _ r ht hrow hr q hq t htq
  · have hl := batchOf_length nT N R grp hR
    have hge : (batchOf nT N grp).length ≤ i * R + r := by
      rw [hl]
      have : nT * N ^ 2 ≤ i := by omega
      nlinarith
    rw [List.getD_eq_default _ _ hge, groupExpr_nil]
    intro t ht
    simp at ht

/-! ## The three request kinds -/

/-- **A FILTER row**: one term, coefficient `1`, one factor, of degree `filtDeg` over its labels. -/
theorem filt_shape (r : FiltReq) (A : ℕ) (h : LabsOk r.L r.labs A) :
    refOf (.filt r) = [(1, [filtPolyC r.thr r.tbl r.L r.sgn r.labs])] ∧
      PolyOk (filtDeg r.tbl) A (filtPolyC r.thr r.tbl r.L r.sgn r.labs) :=
  ⟨rfl, factorPoly_ok _ _ _ _ _ h⟩

theorem filtDeg_req (r : FiltReq) : filtDeg r.tbl = 384 * r.P.walkLen + 1 :=
  FiltRec.filtDeg_filterTable r.P r.e r.L

/-- The truth-table rows of a POP state: at most `2^n`, each with `min(n, |ps|)` factors, selected from `ps`. -/
theorem rowsExpr_length (n θ : ℕ) (c : ℤ) (ps : List (Poly × Poly)) : (rowsExpr n θ c ps).length ≤ 2 ^ n := by
  unfold rowsExpr
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem mem_rowsExpr {n θ : ℕ} {c : ℤ} {ps : List (Poly × Poly)} {t : ℤ × List Poly} (ht : t ∈ rowsExpr n θ c ps) :
    t.1 = c ∧ t.2.length = min n ps.length ∧ ∀ p ∈ t.2, ∃ q ∈ ps, p = q.1 ∨ p = q.2 := by
  unfold rowsExpr at ht
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  refine ⟨rfl, ?_, ?_⟩
  · simp [selFacs, RepairOrdinary.SignedSortKey.binary_length]
  · intro p hp
    unfold selFacs at hp
    obtain ⟨bq, hbq, rfl⟩ := List.mem_map.mp hp
    refine ⟨bq.2, List.of_mem_zip hbq |>.2, ?_⟩
    by_cases hb : bq.1 <;> simp [hb]

end NearCubicWires.WireExponent3_5.PrimAsm.BShape
