import Proof.Wire_3_5.Selection.MathPlan

/-! # C1.1 R3: pooling the error rows into pairs of half points (P3:1339-1347)

Paper: "Enumerate its `2^k` error rows. For each gate and row, the four threshold predicates have integer scores of
the form `a_j(z_L)+b_j(z_R)`, `1 ≤ j ≤ 4`. [...] Enumerate each half's score vectors. For each of the sixteen corner
patterns, count pairs satisfying its four weak inequalities" (P3:1339-1347). The corner structure
(`cornerLeft = ![a',a',a,a]`, `cornerRight = ![b',b,b',b]`) lets the left error `u` travel with the left half and the
right error `v` with the right half: summing the row counts over all rows `(u, v)` is counting pairs of POOLED points
`(a, a')` over `(u, z_L)` and `(b, b')` over `(v, z_R)`. Exactly one corner pattern holds at each pair, so the sum
over the patterns with a nonzero mixed difference is the indicator of a nonzero mixed difference. A half outside the
coset is written as the null point `(0, 0)`, which pairs with nothing.

Proves **`r3Pool : R3Pool`** (`gateRows P σ g = pairCount θ (Ls.map ptLz) (Rs.map ptRz)` for enumerations of all
halves) and **`r3Bound : R3Bound`** (the key range under `KeyBound`). Paper quantity: a gate's row counts. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math.Pool
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars Finset
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

variable (P : StarParams)

/-- The corner predicates of a pair of pooled points are the gate's corner predicates at `(u, v, z_L, z_R)`. -/
theorem cutCorners_eq (g : NormalizedThresholdGate P.n) (u v : P.Errors) (xL : P.SideL → Bool)
    (xR : P.SideR → Bool) :
    cutCorners g.threshold (ptL P g (u, xL)) (ptR P g (v, xR)) =
      fun j => decide (g.threshold ≤ P.cornerLeft g u xL j + P.cornerRight g v xR j) := by
  funext j; fin_cases j <;> rfl

theorem patternHolds_iff_cut (π : Fin 4 → Bool) (g : NormalizedThresholdGate P.n) (u v : P.Errors)
    (xL : P.SideL → Bool) (xR : P.SideR → Bool) :
    P.PatternHolds π g u v xL xR ↔ cutCorners g.threshold (ptL P g (u, xL)) (ptR P g (v, xR)) = π := by
  rw [cutCorners_eq]
  simp only [StarParams.PatternHolds, StarParams.cut_eq_true_iff]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

/-- A null left point pairs with nothing. -/
theorem cornerDelta_nullL (θ : ℤ) (q : ℤ × ℤ) : cornerDelta (cutCorners θ (0, 0) q) = 0 := by
  simp [cornerDelta, cutCorners]

/-- A null right point pairs with nothing. -/
theorem cornerDelta_nullR (θ : ℤ) (p : ℤ × ℤ) : cornerDelta (cutCorners θ p (0, 0)) = 0 := by
  simp [cornerDelta, cutCorners]

/-- The pair indicator of the written points. -/
def ind (σ : P.Translation) (g : NormalizedThresholdGate P.n) (p : P.Errors × (P.SideL → Bool))
    (q : P.Errors × (P.SideR → Bool)) : ℕ :=
  if cornerDelta (cutCorners g.threshold (ptLz P σ g p) (ptRz P σ g q)) ≠ 0 then 1 else 0

theorem ind_eq (σ : P.Translation) (g : NormalizedThresholdGate P.n) (u v : P.Errors) (xL : P.SideL → Bool)
    (xR : P.SideR → Bool) :
    ind P σ g (u, xL) (v, xR) =
      if P.LeftOK σ xL ∧ P.RightOK σ xR ∧ cornerDelta (cutCorners g.threshold (ptL P g (u, xL)) (ptR P g (v, xR))) ≠ 0
      then 1 else 0 := by
  unfold ind ptLz ptRz
  by_cases hl : P.LeftOK σ xL <;> by_cases hr : P.RightOK σ xR <;>
    simp [hl, hr, cornerDelta_nullL, cornerDelta_nullR]

/-- **One row's count is the pair count of the row's halves**: exactly one corner pattern holds at each pair. -/
theorem rowCount_eq_ind (σ : P.Translation) (g : NormalizedThresholdGate P.n) (u v : P.Errors) :
    P.rowCount σ g u v = ∑ xL : P.SideL → Bool, ∑ xR : P.SideR → Bool, ind P σ g (u, xL) (v, xR) := by
  classical
  set OK := (univ.filter (P.LeftOK σ)) ×ˢ (univ.filter (P.RightOK σ)) with hOK
  set f : (P.SideL → Bool) × (P.SideR → Bool) → (Fin 4 → Bool) :=
    fun p => cutCorners g.threshold (ptL P g (u, p.1)) (ptR P g (v, p.2)) with hf
  set S := OK.filter fun p => cornerDelta (f p) ≠ 0 with hS
  have hB : S.card = ∑ π ∈ univ.filter (fun π : Fin 4 → Bool => cornerDelta π ≠ 0),
      (S.filter fun p => f p = π).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    simp only [hS, coe_filter, Set.mem_setOf_eq] at hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact hp.2
  have hA : P.rowCount σ g u v = S.card := by
    rw [hB]
    unfold StarParams.rowCount
    apply Finset.sum_congr rfl
    intro π hπ
    simp only [mem_filter, mem_univ, true_and] at hπ
    congr 1
    ext p
    rw [mem_filter, mem_filter, hS, mem_filter, patternHolds_iff_cut]
    constructor
    · intro h; exact ⟨⟨h.1, by rw [show f p = π from h.2]; exact hπ⟩, h.2⟩
    · intro h; exact ⟨h.1.1, h.2⟩
  rw [hA, hS, Finset.card_filter, hOK, Finset.sum_product, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro xL _
  by_cases hl : P.LeftOK σ xL
  · rw [if_pos hl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xR _
    rw [ind_eq]
    by_cases hr : P.RightOK σ xR <;> simp [hl, hr, hf]
  · rw [if_neg hl]
    symm
    apply Finset.sum_eq_zero
    intro xR _
    rw [ind_eq]
    simp [hl]

/-- A count is the sum of the indicator. -/
theorem countP_eq_sum {α : Type} (l : List α) (p : α → Bool) :
    l.countP p = (l.map fun x => if p x then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.countP_cons, ih, List.map_cons, List.sum_cons]; omega

/-- A list enumerating the whole type sums like the type. -/
theorem sum_enum {α : Type} [Fintype α] [DecidableEq α] (l : List α) (hl : Enumerates l (fun _ => True))
    (f : α → ℕ) : (l.map f).sum = ∑ x, f x := by
  rw [← List.sum_toFinset f hl.1]
  congr 1
  ext x
  simp [(hl.2 x).mpr trivial]

/-- **R3**: a gate's row counts are the pair count of the written points. -/
theorem r3Pool : R3Pool := by
  classical
  intro P σ g Ls Rs hLs hRs
  have hR : ∀ p : P.Errors × (P.SideL → Bool),
      (Rs.map (ptRz P σ g)).countP (fun q => decide (cornerDelta (cutCorners g.threshold (ptLz P σ g p) q) ≠ 0)) =
        ∑ q, ind P σ g p q := by
    intro p
    rw [List.countP_map, countP_eq_sum]
    rw [sum_enum Rs hRs]
    apply Finset.sum_congr rfl
    intro q _
    simp only [Function.comp_apply, ind]
    split_ifs <;> simp_all
  unfold pairCount
  rw [List.map_map]
  simp only [Function.comp_def, hR]
  rw [sum_enum Ls hLs (fun p => ∑ q, ind P σ g p q)]
  unfold gateRows
  simp only [rowCount_eq_ind]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xL _
  rw [Fintype.sum_prod_type]

/-! ## The key range -/

theorem sides_natAbs (g : NormalizedThresholdGate P.n) :
    (∑ i : P.SideL, (g.weight i.1).natAbs) + (∑ i : P.SideR, (g.weight i.1).natAbs) = ∑ i, (g.weight i).natAbs :=
  Fintype.sum_subtype_add_sum_subtype (fun i => P.centerSide i = true) (fun i => (g.weight i).natAbs)

theorem halfScoreL_natAbs_le (g : NormalizedThresholdGate P.n) (xL : P.SideL → Bool) :
    (P.halfScoreL g xL).natAbs ≤ ∑ i, (g.weight i).natAbs := by
  unfold StarParams.halfScoreL
  have h1 := Int.natAbs_sum_le univ (fun i : P.SideL => g.weight i.1 * if xL i then 1 else 0)
  have h2 : ∑ i : P.SideL, (g.weight i.1 * if xL i then 1 else 0).natAbs ≤ ∑ i : P.SideL, (g.weight i.1).natAbs := by
    apply Finset.sum_le_sum; intro i _; split_ifs <;> simp
  have h3 := sides_natAbs P g
  omega

theorem halfScoreR_natAbs_le (g : NormalizedThresholdGate P.n) (xR : P.SideR → Bool) :
    (P.halfScoreR g xR).natAbs ≤ ∑ i, (g.weight i).natAbs := by
  unfold StarParams.halfScoreR
  have h1 := Int.natAbs_sum_le univ (fun i : P.SideR => g.weight i.1 * if xR i then 1 else 0)
  have h2 : ∑ i : P.SideR, (g.weight i.1 * if xR i then 1 else 0).natAbs ≤ ∑ i : P.SideR, (g.weight i.1).natAbs := by
    apply Finset.sum_le_sum; intro i _; split_ifs <;> simp
  have h3 := sides_natAbs P g
  omega

/-- **R3b**: under `KeyBound`, the threshold, `θ − a` and `b` lie strictly between `−2^V` and `2^V`. -/
theorem r3Bound : R3Bound := by
  intro P g V hV
  unfold KeyBound at hV
  refine ⟨by omega, fun xL => ?_, fun xR => ?_⟩
  · have h1 := halfScoreL_natAbs_le P g xL
    have h2 := Int.natAbs_sub_le g.threshold (P.halfScoreL g xL)
    omega
  · have h1 := halfScoreR_natAbs_le P g xR
    omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Math.Pool
