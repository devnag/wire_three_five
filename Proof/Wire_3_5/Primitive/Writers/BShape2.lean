import Proof.Wire_3_5.Primitive.Writers.BShape1

/-! # (P-b): the batch's shape, part 2: the POP and RADIX rows

A POP row (`popRefC`, row:pop P3:1519-1526) is the zero coordinate's constant term and, per visited state, the
truth-table rows with at least `θ` ones: coefficients `±1`, `walkLen` factors per term, each factor a visit print of
degree `3·lbP`; at most `1 + M·2^{walkLen}` terms. A RADIX row (`radRefC`, row:radix P3:2608-2614) is one term per
digit tuple of the right residue: coefficient `1`, two factors per digit, each a digit print of degree
`3·listBound D`; at most `((M+1)²)^{digits}` terms.

Paper quantity of the main types: the POP and RADIX rows' coefficients, factor counts, degrees and term counts. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimAsm.Records NearCubicWires.WireExponent3_5.PrimAsm.Batch
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr radixExpr allTuples pairsUpTo tupleFactors listBound)
open NearCubicWires.SupplierWalk (majorityThreshold)
open NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.Lists

/-! ## POP -/

theorem statesC_coef (P : FlatListParams) (s : Fin (P.M + 1)) :
    ∀ st ∈ statesC P s, st.1 = 1 ∨ st.1 = -1 := by
  intro st hst
  unfold statesC at hst
  split_ifs at hst
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hst; right; rfl
  · rw [List.mem_singleton] at hst; subst hst; left; rfl

theorem statesC_length (P : FlatListParams) (s : Fin (P.M + 1)) : (statesC P s).length ≤ P.M := by
  unfold statesC
  split_ifs with h
  · simp
  · simp only [List.length_singleton]; have := s.isLt; omega

theorem pairsC_length (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ)
    (s' : Fin (P.M + 1)) : (pairsC P e L sgn labs s').length = P.walkLen := by
  simp [pairsC]

theorem pairsC_ok (P : FlatListParams) (e : P.FlatSeed) (L : ℕ) (sgn : Bool) (labs : List ℕ) (A : ℕ)
    (h : LabsOk L labs A) (s' : Fin (P.M + 1)) :
    ∀ q ∈ pairsC P e L sgn labs s', PolyOk (3 * PopLink.lbP P) A q.1 ∧ PolyOk (3 * PopLink.lbP P) A q.2 := by
  intro q hq
  unfold pairsC at hq
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
  have hl := PopLink.listBound_visit P e k
  refine ⟨?_, ?_⟩ <;>
  · show PolyOk _ A (factorPoly _ (4 * L) (3 * listBound (visitData P e k)) labs)
    rw [hl]
    exact factorPoly_ok _ _ _ _ _ h

/-- **A POP row's terms**: coefficient `±1`, `walkLen` factors, each the constant `[[]]` or a visit print. -/
theorem mem_popRef (r : ListMachine.Row.PopReq) :
    ∀ t ∈ refOf (.pop r), (t.1 = 1 ∨ t.1 = -1) ∧ t.2.length = r.P.walkLen ∧
      ∀ p ∈ t.2, p = [[]] ∨ ∃ s' : Fin (r.P.M + 1), ∃ q ∈ pairsC r.P r.e r.L r.sgn r.labs s', p = q.1 ∨ p = q.2 := by
  intro t ht
  change t ∈ popExprP (popOne r.P r.s.val) r.P.walkLen (majorityThreshold r.P.walkLen)
    ((statesC r.P r.s).map fun st => (st.1, pairsC r.P r.e r.L r.sgn r.labs st.2)) at ht
  unfold popExprP at ht
  rcases List.mem_append.mp ht with h1 | h2
  · unfold popOne at h1
    split_ifs at h1
    · rw [List.mem_singleton] at h1
      subst h1
      refine ⟨Or.inl rfl, by simp, fun p hp => Or.inl ?_⟩
      exact (List.mem_replicate.mp hp).2
    · simp at h1
  · obtain ⟨st, hst, ht'⟩ := List.mem_flatMap.mp h2
    obtain ⟨st0, hst0, rfl⟩ := List.mem_map.mp hst
    obtain ⟨e1, e2, e3⟩ := mem_rowsExpr ht'
    refine ⟨by rw [e1]; exact statesC_coef r.P r.s st0 hst0, by rw [e2, pairsC_length]; simp, fun p hp => ?_⟩
    obtain ⟨q, hq, hpq⟩ := e3 p hp
    exact Or.inr ⟨st0.2, q, hq, hpq⟩

/-- **A POP row's factors**: each of degree `≤ 3·lbP` over its labels. -/
theorem pop_terms (r : ListMachine.Row.PopReq) (A : ℕ) (h : LabsOk r.L r.labs A) :
    ∀ t ∈ refOf (.pop r), (t.1 = 1 ∨ t.1 = -1) ∧ t.2.length = r.P.walkLen ∧
      ∀ p ∈ t.2, PolyOk (3 * PopLink.lbP r.P) A p := by
  intro t ht
  obtain ⟨e1, e2, e3⟩ := mem_popRef r t ht
  refine ⟨e1, e2, fun p hp => ?_⟩
  rcases e3 p hp with rfl | ⟨s', q, hq, hpq⟩
  · intro m hm
    rw [List.mem_singleton] at hm
    subst hm
    exact ⟨by simp, fun x hx => by simp at hx⟩
  · have hok := pairsC_ok r.P r.e r.L r.sgn r.labs A h s' q hq
    rcases hpq with rfl | rfl
    · exact hok.1
    · exact hok.2

/-- **A POP row's term count.** -/
theorem pop_length (r : ListMachine.Row.PopReq) : (refOf (.pop r)).length ≤ 1 + r.P.M * 2 ^ r.P.walkLen := by
  change (popExprP (popOne r.P r.s.val) r.P.walkLen (majorityThreshold r.P.walkLen)
    ((statesC r.P r.s).map fun st => (st.1, pairsC r.P r.e r.L r.sgn r.labs st.2))).length ≤ _
  unfold popExprP
  rw [List.length_append, List.length_flatMap]
  have h1 : (popOne r.P r.s.val).length ≤ 1 := by unfold popOne; split_ifs <;> simp
  have h2 := sum_map_le_card ((statesC r.P r.s).map fun st => (st.1, pairsC r.P r.e r.L r.sgn r.labs st.2))
    (fun st => (rowsExpr r.P.walkLen (majorityThreshold r.P.walkLen) st.1 st.2).length) (2 ^ r.P.walkLen)
    (fun st _ => rowsExpr_length _ _ _ _)
  rw [List.length_map] at h2
  have h3 := statesC_length r.P r.s
  have h4 : (statesC r.P r.s).length * 2 ^ r.P.walkLen ≤ r.P.M * 2 ^ r.P.walkLen := Nat.mul_le_mul_right _ h3
  omega

/-! ## RADIX -/

theorem allTuples_length (K : ℕ) : ∀ (n : ℕ), ∀ tup ∈ allTuples K n, tup.length = n
  | 0, tup, h => by simp [allTuples] at h; subst h; rfl
  | n + 1, tup, h => by
    unfold allTuples at h
    obtain ⟨ab, _, h'⟩ := List.mem_flatMap.mp h
    obtain ⟨tl, htl, rfl⟩ := List.mem_map.mp h'
    simp [allTuples_length K n tl htl]

theorem allTuples_card (K : ℕ) : ∀ n : ℕ, (allTuples K n).length = ((K + 1) ^ 2) ^ n
  | 0 => by simp [allTuples]
  | n + 1 => by
    unfold allTuples
    rw [List.length_flatMap]
    simp only [List.length_map, allTuples_card K n, List.map_const', List.sum_replicate, smul_eq_mul]
    have : (pairsUpTo K).length = (K + 1) ^ 2 := by
      unfold pairsUpTo
      rw [List.length_flatMap]
      simp [sq]
    rw [this, pow_succ]
    ring

theorem tupleFactors_length (Pp Pm : ℕ → ℕ → Poly) : ∀ (o : ℕ) (tup : List (ℕ × ℕ)),
    (tupleFactors Pp Pm o tup).length = 2 * tup.length
  | _, [] => rfl
  | o, ab :: tl => by simp [tupleFactors, tupleFactors_length Pp Pm (o + 1) tl]; ring

theorem mem_tupleFactors (Pp Pm : ℕ → ℕ → Poly) : ∀ (o : ℕ) (tup : List (ℕ × ℕ)), ∀ p ∈ tupleFactors Pp Pm o tup,
    ∃ d t, p = Pp d t ∨ p = Pm d t
  | _, [], p, h => by simp [tupleFactors] at h
  | o, ab :: tl, p, h => by
    simp only [tupleFactors, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨o, ab.1, Or.inl rfl⟩
    · exact ⟨o, ab.2, Or.inr rfl⟩
    · exact mem_tupleFactors Pp Pm (o + 1) tl p h

theorem digAt_ok (digs : List Dig) (A : ℕ) (h : ∀ dg ∈ digs, LabsOk dg.1 dg.2 A) (d : ℕ) :
    LabsOk (digAt digs d).1 (digAt digs d).2 A := by
  unfold digAt
  by_cases hd : d < digs.length
  · rw [List.getD_eq_getElem _ _ hd]; exact h _ (List.getElem_mem hd)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨by simp, fun x hx => by simp at hx⟩

/-- **A RADIX row's terms**: coefficient `1`, two factors per digit, each a digit print. -/
theorem mem_radRef (r : ListMachine.Row.RadReq) :
    ∀ t ∈ refOf (.rad r), t.1 = 1 ∧ t.2.length = 2 * r.digs.length ∧
      ∀ p ∈ t.2, ∃ d u, p = radPp r.D r.digs d u ∨ p = radPm r.D r.digs d u := by
  intro t ht
  change t ∈ radixExpr r.digs.length r.D.M r.p r.b0 (radPp r.D r.digs) (radPm r.D r.digs) (r.s : ZMod r.p) at ht
  unfold radixExpr at ht
  obtain ⟨tup, htup, rfl⟩ := List.mem_map.mp ht
  have hl := allTuples_length r.D.M r.digs.length tup (List.mem_filter.mp htup).1
  exact ⟨rfl, by rw [tupleFactors_length, hl], fun p hp => mem_tupleFactors _ _ 0 tup p hp⟩

/-- **A RADIX row's factors**: each of degree `≤ 3·listBound D` over its digit's labels. -/
theorem rad_terms (r : ListMachine.Row.RadReq) (A : ℕ) (h : ∀ dg ∈ r.digs, LabsOk dg.1 dg.2 A) :
    ∀ t ∈ refOf (.rad r), t.1 = 1 ∧ t.2.length = 2 * r.digs.length ∧
      ∀ p ∈ t.2, PolyOk (3 * listBound r.D) A p := by
  intro t ht
  obtain ⟨e1, e2, e3⟩ := mem_radRef r t ht
  refine ⟨e1, e2, fun p hp => ?_⟩
  obtain ⟨d, u, hpt⟩ := e3 p hp
  have hd := digAt_ok r.digs A h d
  rcases hpt with rfl | rfl
  · exact factorPoly_ok _ _ _ _ _ hd
  · exact factorPoly_ok _ _ _ _ _ hd

/-- A FILTER row is one term with coefficient `1` and one factor. -/
theorem filt_ref (r : ListMachine.Row.FiltReq) :
    refOf (.filt r) = [(1, [filtPolyC r.thr r.tbl r.L r.sgn r.labs])] := rfl

/-- **A RADIX row's term count.** -/
theorem rad_length (r : ListMachine.Row.RadReq) : (refOf (.rad r)).length ≤ ((r.D.M + 1) ^ 2) ^ r.digs.length := by
  change (radixExpr r.digs.length r.D.M r.p r.b0 (radPp r.D r.digs) (radPm r.D r.digs) (r.s : ZMod r.p)).length ≤ _
  unfold radixExpr
  rw [List.length_map, ← allTuples_card]
  exact List.length_filter_le _ _

end NearCubicWires.WireExponent3_5.PrimAsm.BShape
