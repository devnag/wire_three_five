import Proof.Wire_3_5.Primitive.Writers.BShape2

/-! # (P-b): the batch's shape, part 3: the SYM batch (`symExprs`, `hpre`)

The SYM entry's rows (`symGroups`): `|carriers|` FILTER rows (one term, one factor) then, per
circuit, the `+` and `−` POP factors (`popFactor`: the POP rows of the targets whose clamp is the state). Over the
SYM batch `symExprs`:
* **`sym_rows_factors`**: row `r` of every entry has `1` (FILTER) or `walkLen` (POP) factors in each term;
* **`sym_factors_ok`**: every monomial has length `≤ max(384·walkLen_F + 1, 3·lbP)` and atoms below
  `4·(2^{kh}·2^{kh})·|pool|` (the corner pool of `C4Geo.poolReq`);
* **`sym_coef_pm1`**: every coefficient is `±1`;
* **`sym_row_terms_le`**: every row has at most `(M+1)²·2^{walkLen}` terms;
* `lbP_le`: `3·lbP ≤ 4608·(⌊√B⌋+1) + 783·(⌈log₂B⌉+9)` (list:base's degree, P3:1425-1426).

Paper quantity of the main types: the SYM batch's factor counts, degrees, atoms, coefficients and term counts
(row:sym, P3:1496-1526). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.Enum NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr listBound)
open NearCubicWires.WireExponent3_5.ListMachine.Row

/-! ## Generic: the groups of a batch -/

theorem mem_batchOf {nT N : ℕ} {grp : ℕ → ℕ → List (List RowReq)} {g : List RowReq} (hg : g ∈ batchOf nT N grp) :
    ∃ t row, t < nT ∧ row < N ^ 2 ∧ g ∈ grp t row := by
  unfold batchOf at hg
  obtain ⟨q, hq, hg⟩ := List.mem_flatMap.mp hg
  have hq' := List.mem_range.mp hq
  have hN : 0 < N ^ 2 := by
    rcases Nat.eq_zero_or_pos (N ^ 2) with h0 | h0
    · rw [h0, Nat.mul_zero] at hq'; omega
    · exact h0
  exact ⟨q / N ^ 2, q % N ^ 2, (Nat.div_lt_iff_lt_mul hN).mpr hq', Nat.mod_lt _ hN, hg⟩

theorem getD_mem_or_nil {β : Type} (l : List (List β)) (k : ℕ) : l.getD k [] ∈ l ∨ l.getD k [] = [] := by
  by_cases hk : k < l.length
  · left; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  · right; exact List.getD_eq_default _ _ (by omega)

/-! ## The SYM groups -/

section Sym
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive

/-- **A FILTER row request's terms**: coefficient `1`, one factor, of degree `384·walkLen + 1` over its labels. -/
theorem filtRow_ok {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (FP : GapParams) (e : GapSeed FP)
    (G row nw j A : ℕ) (h : LabsOk (sl.getD j []).length (CompilerMachine.Pool.labsOf G row (sliceGis sl j)) A) :
    ∀ t ∈ refOf (filtRow sl FP e G row nw j), t.1 = 1 ∧ t.2.length = 1 ∧
      ∀ p ∈ t.2, PolyOk (384 * FP.walkLen + 1) A p := by
  intro t ht
  unfold filtRow at ht
  rw [filt_ref, List.mem_singleton] at ht
  subst ht
  refine ⟨rfl, rfl, fun p hp => ?_⟩
  rw [List.mem_singleton] at hp
  subst hp
  have h1 := (filt_shape ⟨FP, e, ⟨(sl.getD j []).length, true, CompilerMachine.Pool.labsOf G row (sliceGis sl j), nw⟩⟩
    A h).2
  rw [filtDeg_req] at h1
  exact h1

/-- **A POP row request's terms** (`pop_terms` at `popRow`). -/
theorem popRow_ok {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (Pl : FlatListParams) (e' : Pl.FlatSeed)
    (G row nw j : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)) (A : ℕ)
    (h : LabsOk (sl.getD j []).length (CompilerMachine.Pool.labsOf G row (sliceGis sl j)) A) :
    ∀ t ∈ refOf (popRow sl Pl e' G row nw j sgn s), (t.1 = 1 ∨ t.1 = -1) ∧ t.2.length = Pl.walkLen ∧
      ∀ p ∈ t.2, PolyOk (3 * PopLink.lbP Pl) A p :=
  pop_terms ⟨Pl, e', (sl.getD j []).length, sgn, CompilerMachine.Pool.labsOf G row (sliceGis sl j), s, nw⟩ A h

theorem popRow_length {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (Pl : FlatListParams) (e' : Pl.FlatSeed)
    (G row nw j : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)) :
    (refOf (popRow sl Pl e' G row nw j sgn s)).length ≤ 1 + Pl.M * 2 ^ Pl.walkLen :=
  pop_length ⟨Pl, e', (sl.getD j []).length, sgn, CompilerMachine.Pool.labsOf G row (sliceGis sl j), s, nw⟩

theorem mem_popFactor {n : ℕ} {sl : List (List (NormalizedThresholdGate n))} {Pl : FlatListParams} {e' : Pl.FlatSeed}
    {G row nw j : ℕ} {sgn : Bool} {m τ : ℕ} {q : RowReq} (hq : q ∈ popFactor sl Pl e' G row nw j sgn m τ) :
    ∃ s, q = popRow sl Pl e' G row nw j sgn s := by
  unfold popFactor at hq
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hq
  exact ⟨s, rfl⟩

theorem popFactor_length {n : ℕ} (sl : List (List (NormalizedThresholdGate n))) (Pl : FlatListParams)
    (e' : Pl.FlatSeed) (G row nw j : ℕ) (sgn : Bool) (m τ : ℕ) :
    (popFactor sl Pl e' G row nw j sgn m τ).length ≤ Pl.M + 1 := by
  unfold popFactor clampPre
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem mem_symGroups {n a : ℕ} {Cs : Fin a → NormalizedSymmetricThresholdCircuit n} {carriers : List (Carrier n)}
    {FP : GapParams} {e : GapSeed FP} {Pl : FlatListParams} {e' : Pl.FlatSeed} {m : Fin a → ℕ}
    {τ : Rows.SymState m} {G row nw : ℕ} {g : List RowReq}
    (hg : g ∈ symGroups Cs carriers FP e Pl e' m τ G row nw) :
    (∃ j < carriers.length, g = [filtRow (symSlices Cs carriers) FP e G row nw j]) ∨
      (∃ i : Fin a, ∃ sgn mm tt, g = popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + i) sgn mm tt) := by
  unfold symGroups at hg
  rcases List.mem_append.mp hg with h1 | h2
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h1
    exact Or.inl ⟨j, List.mem_range.mp hj, rfl⟩
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact Or.inr ⟨i, true, _, _, rfl⟩
    · exact Or.inr ⟨i, false, _, _, rfl⟩

theorem symGroups_getD_filt {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (FP : GapParams) (e : GapSeed FP) (Pl : FlatListParams) (e' : Pl.FlatSeed) (m : Fin a → ℕ) (τ : Rows.SymState m)
    (G row nw r : ℕ) (hr : r < carriers.length) :
    (symGroups Cs carriers FP e Pl e' m τ G row nw).getD r [] = [filtRow (symSlices Cs carriers) FP e G row nw r] := by
  unfold symGroups
  rw [List.getD_append _ _ _ _ (by simpa using hr), List.getD_eq_getElem _ _ (by simpa using hr)]
  simp

theorem symGroups_getD_pop {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n))
    (FP : GapParams) (e : GapSeed FP) (Pl : FlatListParams) (e' : Pl.FlatSeed) (m : Fin a → ℕ) (τ : Rows.SymState m)
    (G row nw r : ℕ) (hr : carriers.length ≤ r) :
    ∀ q ∈ (symGroups Cs carriers FP e Pl e' m τ G row nw).getD r [],
      ∃ i : Fin a, ∃ sgn s, q = popRow (symSlices Cs carriers) Pl e' G row nw (carriers.length + i) sgn s := by
  intro q hq
  unfold symGroups at hq
  rw [List.getD_append_right _ _ _ _ (by simpa using hr)] at hq
  rcases getD_mem_or_nil ((List.finRange a).flatMap fun (i : Fin a) =>
      [popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) true (m i) (τ i).1,
        popFactor (symSlices Cs carriers) Pl e' G row nw (carriers.length + (i : ℕ)) false (m i) (τ i).2])
      (r - (List.map (fun j => [filtRow (symSlices Cs carriers) FP e G row nw j]) (List.range carriers.length)).length)
    with hm | hnil
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h' | h' <;>
    · rw [h'] at hq
      obtain ⟨s, rfl⟩ := mem_popFactor hq
      exact ⟨i, _, s, rfl⟩
  · rw [hnil] at hq
    simp at hq

end Sym

end NearCubicWires.WireExponent3_5.PrimAsm.BShape
