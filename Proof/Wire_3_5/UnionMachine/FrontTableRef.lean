import Proof.Wire_3_5.UnionMachine.DecisionBridge

/-! # C6 front, U5: the call table in the machine's order (P3:3685-3691, 3483-3489)

The union machine "performs (tr:tests)" (P3:3689-3691): for each position (validity `V`, second moment `Q`) and each
clause (`μ`), each monomial `j` of the masked polynomial, and each four-tuple of atoms with a nonzero coefficient, one
call. The schedule (`UnionCheckData.termsV/termsQ/termsMu`) enumerates ALL `A⁴` tuples in their numbering and
keeps the nonzero ones. The machine enumerates only the nonzero ones: a coefficient `κ_j ∏_k F_{j,k}(t_k)` is nonzero
exactly when `κ_j ≠ 0` and every factor is, and each factor's support is a short list (**`cand`**: the constant, the
encoding parity of `X`, or the grid atoms of `X`/`Y` with a nonzero sign). So the machine's tuples are the four-fold
product of those lists (**`lexProd`**), the last factor outermost.

The two enumerations differ only in order: **`termsV_perm`**, **`termsQ_perm`**, **`termsMu_perm`** (permutations,
both sides duplicate-free with the same members). The decision reads only the tests' sums, so a permuted table decides
the same (`tableAll_perm_decision`).

Paper quantity of the main statements: the call schedule of `(tr:tests)`, as the machine issues it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.UnionMachine.Bridge

/-! ## Four nested enumerations -/

section Lex
variable {α : Type}

/-- The tuples of a four-fold product, the last factor outermost. -/
def lexProd (S : Fin 4 → List α) : List (Fin 4 → α) :=
  (S 3).flatMap fun t3 => (S 2).flatMap fun t2 => (S 1).flatMap fun t1 => (S 0).map fun t0 => ![t0, t1, t2, t3]

theorem mem_lexProd (S : Fin 4 → List α) (t : Fin 4 → α) : t ∈ lexProd S ↔ ∀ k, t k ∈ S k := by
  constructor
  · intro h
    simp only [lexProd, List.mem_flatMap, List.mem_map] at h
    obtain ⟨t3, h3, t2, h2, t1, h1, t0, h0, rfl⟩ := h
    intro k
    fin_cases k <;> simpa
  · intro h
    simp only [lexProd, List.mem_flatMap, List.mem_map]
    refine ⟨t 3, h 3, t 2, h 2, t 1, h 1, t 0, h 0, ?_⟩
    funext k
    fin_cases k <;> rfl

theorem nodup_flatMap_of {β : Type} (l : List α) (f : α → List β) (hl : l.Nodup) (hf : ∀ x ∈ l, (f x).Nodup)
    (hd : ∀ x y, x ≠ y → ∀ u, u ∈ f x → u ∉ f y) : (l.flatMap f).Nodup :=
  List.nodup_flatMap.2 ⟨hf, hl.imp fun {x y} hxy => fun u hx hy => hd x y hxy u hx hy⟩

theorem nodup_lexProd (S : Fin 4 → List α) (h : ∀ k, (S k).Nodup) : (lexProd S).Nodup := by
  unfold lexProd
  refine nodup_flatMap_of _ _ (h 3) (fun t3 _ => ?_) ?_
  · refine nodup_flatMap_of _ _ (h 2) (fun t2 _ => ?_) ?_
    · refine nodup_flatMap_of _ _ (h 1) (fun t1 _ => ?_) ?_
      · refine (h 0).map fun a b hab => ?_
        simpa using congrFun hab 0
      · intro x y hxy u hx hy
        simp only [List.mem_map] at hx hy
        obtain ⟨a, -, rfl⟩ := hx
        obtain ⟨b, -, hb⟩ := hy
        exact hxy (by simpa using (congrFun hb 1).symm)
    · intro x y hxy u hx hy
      simp only [List.mem_flatMap, List.mem_map] at hx hy
      obtain ⟨a, -, a', -, rfl⟩ := hx
      obtain ⟨b, -, b', -, hb⟩ := hy
      exact hxy (by simpa using (congrFun hb 2).symm)
  · intro x y hxy u hx hy
    simp only [List.mem_flatMap, List.mem_map] at hx hy
    obtain ⟨a, -, a', -, a'', -, rfl⟩ := hx
    obtain ⟨b, -, b', -, b'', -, hb⟩ := hy
    exact hxy (by simpa using (congrFun hb 3).symm)

end Lex

/-! ## The factors' supports -/

/-- The kind of a factor: the constant `1`, the encoding parity `E_X`, the grid sum `S_X`, the grid sum `S_Y`. -/
inductive FK
  | one
  | par
  | sx
  | sy
  deriving DecidableEq

section Cands
variable (D : UnionCheckData)

/-- The grid atoms of `X` with a nonzero sign, in order. -/
def gridC (X : PcppVar D.pcpp) : List D.AtomIx :=
  (List.finRange D.s).filterMap fun a => if D.sign X a = 0 then none else some (Sum.inr (Sum.inl (X, a)))

/-- **A factor's support**: the atoms where its weight is nonzero. -/
def cand (X Y : PcppVar D.pcpp) : FK → List D.AtomIx
  | .one => [Sum.inl ()]
  | .par => [Sum.inr (Sum.inr X)]
  | .sx => gridC D X
  | .sy => gridC D Y

/-- A factor's weight. -/
def wOf (X Y : PcppVar D.pcpp) : FK → D.AtomIx → ℚ
  | .one => D.wOne
  | .par => D.wE X
  | .sx => D.wS X
  | .sy => D.wS Y

theorem mem_gridC (X : PcppVar D.pcpp) (a : D.AtomIx) :
    a ∈ gridC D X ↔ ∃ b, D.sign X b ≠ 0 ∧ a = Sum.inr (Sum.inl (X, b)) := by
  simp only [gridC, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨b, hb⟩
    split_ifs at hb with h
    simp only [Option.some.injEq] at hb
    exact ⟨b, h, hb.symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, by simp [hb]⟩

theorem nodup_gridC (X : PcppVar D.pcpp) : (gridC D X).Nodup := by
  refine List.Nodup.filterMap ?_ (List.nodup_finRange _)
  intro a a' b ha ha'
  by_cases h1 : D.sign X a = 0
  · simp [h1] at ha
  · by_cases h2 : D.sign X a' = 0
    · simp [h2] at ha'
    · simp only [h1, h2, if_false, Option.mem_def, Option.some.injEq] at ha ha'
      subst ha
      simpa using ha'.symm

theorem nodup_cand (X Y : PcppVar D.pcpp) (k : FK) : (cand D X Y k).Nodup := by
  cases k <;> simp [cand, nodup_gridC]

theorem wS_ne_zero_iff (hm : D.mass ≠ 0) (hs : D.s ≠ 0) (X : PcppVar D.pcpp) (a : D.AtomIx) :
    D.wS X a ≠ 0 ↔ a ∈ gridC D X := by
  rw [mem_gridC]
  have hs' : (D.s : ℚ) ≠ 0 := by exact_mod_cast hs
  rcases a with u | (⟨Z, b⟩ | Z)
  · simp [UnionCheckData.wS]
  · simp only [UnionCheckData.wS]
    by_cases hZ : Z = X
    · subst hZ
      constructor
      · intro h
        refine ⟨b, ?_, rfl⟩
        intro h0
        apply h
        simp [h0]
      · rintro ⟨c, hc, e⟩
        simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at e
        subst e
        simp [hm, hs', hc]
    · constructor
      · intro h
        exact absurd (by simp [hZ]) h
      · rintro ⟨c, -, e⟩
        simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at e
        exact absurd e.1 hZ
  · simp [UnionCheckData.wS]

theorem wOf_ne_zero_iff (hm : D.mass ≠ 0) (hs : D.s ≠ 0) (X Y : PcppVar D.pcpp) (k : FK) (a : D.AtomIx) :
    wOf D X Y k a ≠ 0 ↔ a ∈ cand D X Y k := by
  cases k
  · rcases a with u | (p | Z) <;> simp [wOf, cand, UnionCheckData.wOne]
  · rcases a with u | (p | Z)
    · simp [wOf, cand, UnionCheckData.wE]
    · simp [wOf, cand, UnionCheckData.wE]
    · by_cases h : Z = X <;> simp [wOf, cand, UnionCheckData.wE, h]
  · exact wS_ne_zero_iff D hm hs X a
  · exact wS_ne_zero_iff D hm hs Y a

end Cands

/-! ## One monomial's calls, in the machine's order -/

section Block
variable (D : UnionCheckData)

/-- The terms with a nonzero coefficient, filtered from a list. -/
theorem filterMap_nzTerm {β : Type} (l : List β) (c : β → ℚ) (r : β → PrimRequest) :
    l.filterMap (fun b => nzTerm (c b) (r b)) = (l.filter fun b => c b ≠ 0).map fun b => (c b, r b) := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.filterMap_cons, List.filter_cons, ih]
    by_cases hb : c b = 0 <;> simp [nzTerm, hb]

theorem nodup_tuples : D.tuples.Nodup :=
  (List.nodup_finRange _).map D.tupleEquiv.symm.injective

theorem mem_tuples (t : Fin 4 → D.AtomIx) : t ∈ D.tuples := mem_map_equiv _ _

/-- **One monomial's calls in the machine's order**: nothing when `κ_j = 0`, else the four-fold product of the
factors' supports. -/
def blk (P : Poly4Q D.AtomIx) (j : Fin 4) (X Y : PcppVar D.pcpp) (pat : Fin 4 → FK)
    (call : (Fin 4 → D.AtomIx) → PrimRequest) : List (ℚ × PrimRequest) :=
  if P.κ j = 0 then [] else (lexProd fun k => cand D X Y (pat k)).map fun t => (P.coeff j t, call t)

/-- **The schedule's filter is the machine's product, up to order.** -/
theorem filterMap_perm_blk (hm : D.mass ≠ 0) (hs : D.s ≠ 0) (P : Poly4Q D.AtomIx) (j : Fin 4)
    (X Y : PcppVar D.pcpp) (pat : Fin 4 → FK) (hF : ∀ k, P.F j k = wOf D X Y (pat k))
    (call : (Fin 4 → D.AtomIx) → PrimRequest) :
    (D.tuples.filterMap fun t => nzTerm (P.coeff j t) (call t)).Perm (blk D P j X Y pat call) := by
  rw [filterMap_nzTerm]
  unfold blk
  by_cases hκ : P.κ j = 0
  · rw [if_pos hκ]
    have : D.tuples.filter (fun t => P.coeff j t ≠ 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro t _
      simp [Poly4Q.coeff, hκ]
    rw [this]; rfl
  · rw [if_neg hκ]
    refine List.Perm.map _ ?_
    refine (List.perm_ext_iff_of_nodup ((nodup_tuples D).filter _) (nodup_lexProd _ fun k => nodup_cand D X Y _)).2 ?_
    intro t
    rw [List.mem_filter, mem_lexProd]
    simp only [mem_tuples, true_and, decide_eq_true_eq, Poly4Q.coeff, ne_eq, mul_eq_zero, hκ, false_or,
      Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, not_exists]
    refine forall_congr' fun k => ?_
    rw [hF k, ← ne_eq, wOf_ne_zero_iff D hm hs]

end Block

/-! ## The three tests' patterns -/

section Patterns
variable (D : UnionCheckData)

/-- The validity polynomial's factor kinds (`polyVQ`): systematic `[S S 1 1], [E S 1 1], [E 1 1 1], [1 1 1 1]`;
otherwise `[S S 1 1], [S S S 1], [S S S S], [1 1 1 1]`. -/
def patV (sys : Bool) (j : Fin 4) : Fin 4 → FK :=
  if sys then ![![.sx, .sx, .one, .one], ![.par, .sx, .one, .one], ![.par, .one, .one, .one], ![.one, .one, .one, .one]] j
  else ![![.sx, .sx, .one, .one], ![.sx, .sx, .sx, .one], ![.sx, .sx, .sx, .sx], ![.one, .one, .one, .one]] j

/-- The second-moment polynomial's factor kinds (`polyQQ`). -/
def patQ (j : Fin 4) : Fin 4 → FK :=
  ![![.sx, .sx, .one, .one], ![.one, .one, .one, .one], ![.one, .one, .one, .one], ![.one, .one, .one, .one]] j

/-- The clause polynomial's factor kinds (`polyMuQ`): `[1 1 1 1], [S_X 1 1 1], [S_Y 1 1 1], [S_X S_Y 1 1]`. -/
def patMu (j : Fin 4) : Fin 4 → FK :=
  ![![.one, .one, .one, .one], ![.sx, .one, .one, .one], ![.sy, .one, .one, .one], ![.sx, .sy, .one, .one]] j

theorem polyV_F (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (j k : Fin 4) :
    (D.polyVAt pos).F j k =
      wOf D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (patV (D.sysBit (posVar D.pcpp pos.1 pos.2)) j k) := by
  unfold UnionCheckData.polyVAt polyVQ patV
  cases D.sysBit (posVar D.pcpp pos.1 pos.2) <;> fin_cases j <;> fin_cases k <;> rfl

theorem polyQ_F (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (j k : Fin 4) :
    (D.polyQAt pos).F j k = wOf D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (patQ j k) := by
  unfold UnionCheckData.polyQAt polyQQ patQ
  fin_cases j <;> fin_cases k <;> rfl

theorem polyMu_F (i : Fin (2 ^ D.pcpp.clauseBits)) (j k : Fin 4) :
    (D.polyMuAt i).F j k = wOf D (posVar D.pcpp i 0) (posVar D.pcpp i 1) (patMu j k) := by
  unfold UnionCheckData.polyMuAt polyMuQ patMu
  fin_cases j <;> fin_cases k <;> rfl

/-- The machine's positions: clause-major, then the literal. -/
def posList : List (Fin (2 ^ D.pcpp.clauseBits) × Fin 2) :=
  (List.finRange (2 ^ D.pcpp.clauseBits)).flatMap fun i => [(i, 0), (i, 1)]

theorem positions_perm : D.positions.Perm (posList D) := by
  refine (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map finProdFinEquiv.symm.injective) ?_).2 ?_
  · refine nodup_flatMap_of _ _ (List.nodup_finRange _) (fun i _ => by simp) ?_
    intro x y hxy u hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp_all
  · intro pos
    constructor
    · intro _
      simp only [posList, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
        or_false]
      refine ⟨pos.1, ?_⟩
      rcases pos with ⟨i, b⟩
      fin_cases b <;> simp
    · intro _
      exact mem_map_equiv _ _

/-- **The machine's `V` terms**: per position, per monomial, the product of the supports. -/
def myV : List (ℚ × PrimRequest) :=
  (posList D).flatMap fun pos => (List.finRange 4).flatMap fun j =>
    blk D (D.polyVAt pos) j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2)
      (patV (D.sysBit (posVar D.pcpp pos.1 pos.2)) j) (D.vCall pos)

/-- The machine's `Q` terms. -/
def myQ : List (ℚ × PrimRequest) :=
  (posList D).flatMap fun pos => (List.finRange 4).flatMap fun j =>
    blk D (D.polyQAt pos) j (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (patQ j) (D.vCall pos)

/-- The machine's `μ` terms. -/
def myMu : List (ℚ × PrimRequest) :=
  (List.finRange (2 ^ D.pcpp.clauseBits)).flatMap fun i => (List.finRange 4).flatMap fun j =>
    blk D (D.polyMuAt i) j (posVar D.pcpp i 0) (posVar D.pcpp i 1) (patMu j) (D.muCall i)

theorem termsV_perm (hm : D.mass ≠ 0) (hs : D.s ≠ 0) : D.termsV.Perm (myV D) := by
  unfold UnionCheckData.termsV myV
  refine (List.Perm.flatMap_right _ (positions_perm D)).trans (List.Perm.flatMap_left _ fun pos _ => ?_)
  exact List.Perm.flatMap_left _ fun j _ => filterMap_perm_blk D hm hs _ j _ _ _ (fun k => polyV_F D pos j k) _

theorem termsQ_perm (hm : D.mass ≠ 0) (hs : D.s ≠ 0) : D.termsQ.Perm (myQ D) := by
  unfold UnionCheckData.termsQ myQ
  refine (List.Perm.flatMap_right _ (positions_perm D)).trans (List.Perm.flatMap_left _ fun pos _ => ?_)
  exact List.Perm.flatMap_left _ fun j _ => filterMap_perm_blk D hm hs _ j _ _ _ (fun k => polyQ_F D pos j k) _

theorem termsMu_perm (hm : D.mass ≠ 0) (hs : D.s ≠ 0) : D.termsMu.Perm (myMu D) := by
  unfold UnionCheckData.termsMu myMu
  refine List.Perm.flatMap_left _ fun i _ => ?_
  exact List.Perm.flatMap_left _ fun j _ => filterMap_perm_blk D hm hs _ j _ _ _ (fun k => polyMu_F D i j k) _

end Patterns

/-! ## A permuted table decides the same -/

section Decision
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (decisionOf)
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I)

theorem zSum_perm (s : ℕ) {T T' : List (ℚ × PrimRequest)} (h : T.Perm T') (m : PrimRequest → ℤ) :
    zSum s T m = zSum s T' m := by
  unfold zSum
  exact (h.map _).sum_eq

/-- **A permuted table decides the same**: the decision reads only each test's sum (`decision_accOf`). -/
theorem tableAll_perm_decision (s p : ℕ) (TV TQ TM : ℤ) (LV LQ LM LV' LQ' LM' : List (ℚ × PrimRequest))
    (hV : ∀ t ∈ LV, I.Call t.2) (hQ : ∀ t ∈ LQ, I.Call t.2) (hM : ∀ t ∈ LM, I.Call t.2)
    (hV' : ∀ t ∈ LV', I.Call t.2) (hQ' : ∀ t ∈ LQ', I.Call t.2) (hM' : ∀ t ∈ LM', I.Call t.2)
    (pV : LV.Perm LV') (pQ : LQ.Perm LQ') (pM : LM.Perm LM') :
    decisionOf (Sched.accOf P p (threshAcc TV TQ TM) (tableAll s LV LQ LM hV hQ hM)
        (tableAll s LV LQ LM hV hQ hM).length) =
      decisionOf (Sched.accOf P p (threshAcc TV TQ TM) (tableAll s LV' LQ' LM' hV' hQ' hM')
        (tableAll s LV' LQ' LM' hV' hQ' hM').length) := by
  rw [decision_accOf, decision_accOf]
  simp only [tableAll_sum]
  rw [zSum_perm s pV, zSum_perm s pQ, zSum_perm s pM]

end Decision

/-! ## One call's entry: the sign and magnitude of `c·s⁴` -/

section Entry
variable (D : UnionCheckData)

/-- The sign of a grid atom (`0` for the constant and the parities). -/
def sgnAt : D.AtomIx → ℤ
  | Sum.inr (Sum.inl (Z, b)) => D.sign Z b
  | _ => 0

/-- A factor's scaled value `F·s` at an atom of its support: `s` for the constant and the parity, `Λ̄σ` for a grid
atom. -/
def fv (Λ : ℕ) : FK → D.AtomIx → ℤ
  | .one, _ => D.s
  | .par, _ => D.s
  | .sx, a => Λ * sgnAt D a
  | .sy, a => Λ * sgnAt D a

theorem factor_scaled (hs : D.s ≠ 0) (Λ : ℕ) (hm : D.mass = Λ) (X Y : PcppVar D.pcpp) (k : FK) (a : D.AtomIx)
    (ha : a ∈ cand D X Y k) : wOf D X Y k a * (D.s : ℚ) = (fv D Λ k a : ℚ) := by
  have hs' : (D.s : ℚ) ≠ 0 := by exact_mod_cast hs
  cases k
  · simp only [cand, List.mem_singleton] at ha
    subst ha
    simp [wOf, fv, UnionCheckData.wOne]
  · simp only [cand, List.mem_singleton] at ha
    subst ha
    simp [wOf, fv, UnionCheckData.wE]
  · obtain ⟨b, -, rfl⟩ := (mem_gridC D X a).1 ha
    simp only [wOf, fv, UnionCheckData.wS, if_true, sgnAt, hm]
    push_cast
    field_simp
  · obtain ⟨b, -, rfl⟩ := (mem_gridC D Y a).1 ha
    simp only [wOf, fv, UnionCheckData.wS, if_true, sgnAt, hm]
    push_cast
    field_simp

/-- **The scaled coefficient is an integer product**: `c·s⁴ = κ_j ∏_k (F·s)` on the machine's tuples. -/
theorem coeff_scaled (hs : D.s ≠ 0) (Λ : ℕ) (hm : D.mass = Λ) (P : Poly4Q D.AtomIx) (j : Fin 4)
    (X Y : PcppVar D.pcpp) (pat : Fin 4 → FK) (hF : ∀ k, P.F j k = wOf D X Y (pat k)) (κz : ℤ)
    (hκ : P.κ j = κz) (t : Fin 4 → D.AtomIx) (ht : ∀ k, t k ∈ cand D X Y (pat k)) :
    scaledZ D.s (P.coeff j t) = κz * ∏ k, fv D Λ (pat k) (t k) := by
  have e : P.coeff j t * (D.s : ℚ) ^ 4 = ((κz * ∏ k, fv D Λ (pat k) (t k) : ℤ) : ℚ) := by
    unfold Poly4Q.coeff
    rw [hκ, mul_assoc]
    push_cast
    congr 1
    rw [show (D.s : ℚ) ^ 4 = ∏ _k : Fin 4, (D.s : ℚ) by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hF k]
    exact factor_scaled D hs Λ hm X Y (pat k) (t k) (ht k)
  unfold scaledZ
  rw [e, Rat.num_intCast]

/-- `±1` from a sign bit. -/
def sgnZ (b : Bool) : ℤ := if b then -1 else 1

theorem prod4_sgn (b0 b1 b2 b3 : Bool) (m0 m1 m2 m3 : ℤ) :
    (sgnZ b0 * m0) * (sgnZ b1 * m1) * (sgnZ b2 * m2) * (sgnZ b3 * m3) =
      sgnZ (b0 ^^ b1 ^^ b2 ^^ b3) * (m0 * m1 * m2 * m3) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp [sgnZ] <;> ring

/-- Whether a factor is a grid sum. -/
def isS : FK → Bool
  | .sx => true
  | .sy => true
  | _ => false

/-- A factor's magnitude: `s` for the constant and the parity, `Λ̄` for a grid atom. -/
def mOf (Λ : ℕ) : FK → ℕ
  | .one => D.s
  | .par => D.s
  | .sx => Λ
  | .sy => Λ

/-- A factor's sign bit at an atom: a grid atom with sign `−1`. -/
def nbOf (k : FK) (a : D.AtomIx) : Bool := isS k && decide (sgnAt D a < 0)

theorem fv_sgn (hsg : D.signsOk = true) (Λ : ℕ) (X Y : PcppVar D.pcpp) (k : FK) (a : D.AtomIx)
    (ha : a ∈ cand D X Y k) : fv D Λ k a = sgnZ (nbOf D k a) * (mOf D Λ k : ℤ) := by
  have hsg' : ∀ Z b, D.sign Z b ∈ ({-1, 0, 1} : Finset ℤ) := by
    simpa [UnionCheckData.signsOk] using hsg
  cases k
  · simp [fv, nbOf, isS, sgnZ, mOf]
  · simp [fv, nbOf, isS, sgnZ, mOf]
  · obtain ⟨b, hb, rfl⟩ := (mem_gridC D X a).1 ha
    have h := hsg' X b
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · simp [fv, nbOf, isS, sgnZ, mOf, sgnAt, h]
    · exact absurd h hb
    · simp [fv, nbOf, isS, sgnZ, mOf, sgnAt, h]
  · obtain ⟨b, hb, rfl⟩ := (mem_gridC D Y a).1 ha
    have h := hsg' Y b
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · simp [fv, nbOf, isS, sgnZ, mOf, sgnAt, h]
    · exact absurd h hb
    · simp [fv, nbOf, isS, sgnZ, mOf, sgnAt, h]

/-- The magnitude of a block's calls: `κ·∏ m_k`. -/
def magOf (Λ κm : ℕ) (pat : Fin 4 → FK) : ℕ :=
  κm * (mOf D Λ (pat 0) * mOf D Λ (pat 1) * mOf D Λ (pat 2) * mOf D Λ (pat 3))

/-- The sign bit of a call: the monomial's sign, flipped by each grid atom of sign `−1`. -/
def negOf (κn : Bool) (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx) : Bool :=
  κn ^^ (nbOf D (pat 0) (t 0) ^^ nbOf D (pat 1) (t 1) ^^ nbOf D (pat 2) (t 2) ^^ nbOf D (pat 3) (t 3))

/-- **One call's table entry**, as the machine writes it: the test's kind, the sign bit `negOf`, the magnitude
`magOf`, the request's word. -/
theorem entryOf_blk (hs : D.s ≠ 0) (Λ : ℕ) (hm : D.mass = Λ) (hsg : D.signsOk = true) (P : Poly4Q D.AtomIx)
    (j : Fin 4) (X Y : PcppVar D.pcpp) (pat : Fin 4 → FK) (hF : ∀ k, P.F j k = wOf D X Y (pat k)) (κn : Bool)
    (κm : ℕ) (hκ : P.κ j = ((sgnZ κn * κm : ℤ) : ℚ)) (hκm : 1 ≤ κm) (hΛ : 1 ≤ Λ) (kd : Fin 3)
    (call : (Fin 4 → D.AtomIx) → PrimRequest) (t : Fin 4 → D.AtomIx) (ht : ∀ k, t k ∈ cand D X Y (pat k)) :
    entryOf kd D.s (P.coeff j t, call t) = ⟨kd, negOf D κn pat t, magOf D Λ κm pat, (call t).word⟩ := by
  have hz := coeff_scaled D hs Λ hm P j X Y pat hF _ hκ t ht
  rw [Fin.prod_univ_four, fv_sgn D hsg Λ X Y _ _ (ht 0), fv_sgn D hsg Λ X Y _ _ (ht 1),
    fv_sgn D hsg Λ X Y _ _ (ht 2), fv_sgn D hsg Λ X Y _ _ (ht 3), prod4_sgn] at hz
  have hpos : 0 < ((κm * (mOf D Λ (pat 0) * mOf D Λ (pat 1) * mOf D Λ (pat 2) * mOf D Λ (pat 3)) : ℕ) : ℤ) := by
    have hm0 : ∀ k, 1 ≤ mOf D Λ k := fun k => by
      cases k <;> simp only [mOf] <;> omega
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hm0 (pat 0)) (hm0 (pat 1))) (hm0 (pat 2))) (hm0 (pat 3))
    have := Nat.mul_le_mul hκm this
    omega
  have hz' : scaledZ D.s (P.coeff j t) = sgnZ (negOf D κn pat t) *
      ((κm * (mOf D Λ (pat 0) * mOf D Λ (pat 1) * mOf D Λ (pat 2) * mOf D Λ (pat 3)) : ℕ) : ℤ) := by
    rw [hz]
    unfold negOf
    push_cast
    cases κn <;> cases nbOf D (pat 0) (t 0) ^^ nbOf D (pat 1) (t 1) ^^ nbOf D (pat 2) (t 2) ^^ nbOf D (pat 3) (t 3) <;>
      simp [sgnZ] <;> ring
  unfold entryOf magOf
  simp only [hz']
  generalize κm * (mOf D Λ (pat 0) * mOf D Λ (pat 1) * mOf D Λ (pat 2) * mOf D Λ (pat 3)) = M at hpos ⊢
  cases negOf D κn pat t <;> simp [sgnZ] <;> omega

end Entry


end NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
