import Proof.Wire_3_5.FinalPass.PoolFit

/-! # The pool's coefficient width (mode-generic), part 2: `PNFit`, `DenseFit`, `CoefFit`

From a bound `M` on every exact child's weights and target (`coef_lt_budget`: `M = 2^{budget}`), the pulled-back
dense child (P3:1645-1648, 1655-1658) has weights of size `≤ M`, a target of size `≤ (n+1)M` and a total of
`≤ (2n+1)M`; so the pool's P/N fields and dense children fit `h` bits once `(2n+1)M < 2^h`.
* `ChildBound`, `dense_weight_le`, `splitTarget_le`, **`pnFit_of`**, **`denseFit_of`**, **`coefFit_of`**,
  **`poolFits_of`** (all three from `sourceBudget ≤ Bud` and `Bud + n + 2 ≤ h`).
Paper quantities of the main types: the pool's fields against the compiler's word width `h`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.PoolFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline

/-- Every exact child of every pool gate has weights and target of size `≤ M`. -/
def ChildBound (a : DecompositionAlgorithm) {n : ℕ} (gates : List (SupportedNormalizedGate n)) (M : ℕ) : Prop :=
  ∀ g ∈ gates, ∀ e ∈ children a g, (∀ i, (e.weight i).natAbs ≤ M) ∧ e.target.natAbs ≤ M

theorem mem_route (cs : List Coord) (z : ℤ) (hz : z ∈ routeL cs ∨ z ∈ routeR cs) :
    ∃ c ∈ cs, |z| = |c.2.2| := by
  simp only [routeL, routeR] at hz
  rcases hz with hz | hz
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact ⟨c, (List.mem_filter.mp hc).1, abs_flipW _ _⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
    exact ⟨c, (List.mem_filter.mp hc).1, abs_flipW _ _⟩

theorem getD_pad_abs (L R : List ℤ) (w j : ℕ) (M : ℤ) (h0 : 0 ≤ M) (hL : ∀ z ∈ L, |z| ≤ M) (hR : ∀ z ∈ R, |z| ≤ M) :
    |(padTo w L ++ padTo w R).getD j 0| ≤ M := by
  rcases Nat.lt_or_ge j (padTo w L ++ padTo w R).length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj]
    have hm := List.getElem_mem hj
    generalize (padTo w L ++ padTo w R)[j] = z at hm ⊢
    unfold padTo at hm
    simp only [List.mem_append, List.mem_replicate] at hm
    rcases hm with (h | h) | (h | h)
    · exact hL _ h
    · rw [h.2]; simpa using h0
    · exact hR _ h
    · rw [h.2]; simpa using h0
  · rw [List.getD_eq_default _ _ hj]; simpa using h0

theorem coords_abs {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) (M : ℕ)
    (hM : ∀ i, (e.weight i).natAbs ≤ M) : ∀ c ∈ coords side f e, |c.2.2| ≤ (M : ℤ) := by
  intro c hc
  unfold coords at hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  have := hM i; rw [Int.abs_eq_natAbs]; exact_mod_cast this

theorem dense_weight_le {n : ℕ} (side f : List Bool) (w : ℕ) (e : ExactThresholdGate n) (M : ℕ)
    (hM : ∀ i, (e.weight i).natAbs ≤ M) (j : ℕ) : |(denseWeights side f w e).getD j 0| ≤ (M : ℤ) := by
  have hc := coords_abs side f e M hM
  unfold denseWeights
  refine getD_pad_abs _ _ w j M (by positivity) (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨c, hc', he⟩ := mem_route (coords side f e) z (Or.inl hz); rw [he]; exact hc c hc'
  · obtain ⟨c, hc', he⟩ := mem_route (coords side f e) z (Or.inr hz); rw [he]; exact hc c hc'

theorem toNat_le_abs (t : ℤ) : ((t.toNat : ℕ) : ℤ) ≤ |t| := by
  rw [Int.toNat_eq_max]; exact max_le (le_abs_self t) (abs_nonneg t)

theorem negToNat_le_abs (t : ℤ) : (((-t).toNat : ℕ) : ℤ) ≤ |t| := by
  rw [Int.toNat_eq_max]; exact max_le (neg_le_abs t) (abs_nonneg t)

theorem sum_cast_le (cs : List Coord) (g : Coord → ℕ) (hg : ∀ c ∈ cs, ((g c : ℕ) : ℤ) ≤ |c.2.2|) :
    (((cs.map g).sum : ℕ) : ℤ) ≤ (cs.map fun c => |c.2.2|).sum := by
  rw [Nat.cast_list_sum, List.map_map]
  exact List.sum_le_sum (fun c hc => hg c hc)

theorem splitTarget_le (cs : List Coord) (t : ℤ) :
    ((splitTarget cs t).1 : ℤ) ≤ |t| + (cs.map fun c => |c.2.2|).sum ∧
      ((splitTarget cs t).2 : ℤ) ≤ |t| + (cs.map fun c => |c.2.2|).sum := by
  unfold splitTarget
  have k1 := sum_cast_le cs (fun c => if c.2.1 then (-c.2.2).toNat else 0) (fun c _ => by
    split_ifs
    · exact negToNat_le_abs _
    · simp)
  have k2 := sum_cast_le cs (fun c => if c.2.1 then c.2.2.toNat else 0) (fun c _ => by
    split_ifs
    · exact toNat_le_abs _
    · simp)
  have ht1 := toNat_le_abs t
  have ht2 := negToNat_le_abs t
  constructor <;> rw [Nat.cast_add] <;> linarith

end NearCubicWires.WireExponent3_5.FinalPass.PoolFit

