import Proof.Wire_3_5.FinalPass.C3Geo

/-! # The pool's coefficient width (mode-generic): `CoefFit`, `PNFit`, `DenseFit` at `h ≥ budget + n + 2`

"Their coefficients and targets have `O(ℓ+log(f+2))` bits [...] Construction is polynomial in the explicit output size"
(alg:disjoint, P3:1596-1615): the exact children of a pool gate are the output of the decomposition algorithm, whose
word `exactListWord` has at most `sourceBudget a (request g) = coefficient·(arity + encodingBits + 1)^degree` bits
(base's `cache_le_budget`), so every child coefficient is below `2^{budget}`; the pulled-back dense fields of a child
(P3:1645-1648, 1655-1658) are sums of at most `n+1` of them.
* `length_le_flatMap`, `natAbs_lt_bits`, **`coef_lt_budget`**;
* `sum_getD_le`, `routeLR_sum`, **`pnFit_of`**, **`denseFit_of`**, **`coefFit_of`** (every pool gate's budget `≤ Bud`,
  `Bud + n + 2 ≤ h`).
Paper quantities of the main types: the pool children's coefficient bits against the compiler's word width `h`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.PoolFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline

theorem length_le_flatMap {α β : Type} (f : α → List β) : ∀ (l : List α) (x : α), x ∈ l →
    (f x).length ≤ (l.flatMap f).length
  | [], _, h => absurd h (List.not_mem_nil)
  | y :: l, x, h => by
    rw [List.flatMap_cons, List.length_append]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := length_le_flatMap f l x h; omega

theorem natAbs_lt_bits (z : ℤ) : z.natAbs < 2 ^ intBitLength z := by
  unfold intBitLength
  exact Nat.lt_pow_succ_log_self (by norm_num) _

/-- **Every exact child coefficient is below `2^{budget}`** (the decomposition algorithm's output bound). -/
theorem coef_lt_budget (a : DecompositionAlgorithm) {q : ℕ} (g : SupportedNormalizedGate q)
    (e : ExactThresholdGate q) (he : e ∈ children a g) (z : ℤ) (hz : z ∈ List.ofFn e.weight ++ [e.target]) :
    z.natAbs < 2 ^ RepairOrdinary.DecompositionSource.sourceBudget a (request g) := by
  have hB := cache_le_budget a g
  have h1 : (intWord z).length ≤ (exactWord e).length := by
    unfold exactWord
    rcases List.mem_append.mp hz with hw | ht
    · have := length_le_flatMap intWord _ z hw
      rw [List.length_append]; omega
    · rw [List.mem_singleton.mp ht, List.length_append]; omega
  have h2 : (exactWord e).length ≤ (exactListWord (children a g)).length := by
    unfold exactListWord
    have := length_le_flatMap exactWord _ e he
    rw [List.length_append]; omega
  have h3 : intBitLength z ≤ (intWord z).length := by
    rw [RepairOrdinary.DecompositionSource.intWord_length]; omega
  exact lt_of_lt_of_le (natAbs_lt_bits z) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-! ## The dense fields -/

theorem sum_getD_le (l : List ℤ) : ∀ N : ℕ, (∑ j ∈ Finset.range N, |l.getD j 0|) ≤ (l.map fun z => |z|).sum := by
  induction l with
  | nil => intro N; simp
  | cons x l ih =>
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact List.sum_nonneg (by simp)
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.sum_cons]
      have := ih N
      linarith

theorem abs_flipW (f : Bool) (w : ℤ) : |flipW f w| = |w| := by unfold flipW; split_ifs <;> simp

theorem routeLR_sum (cs : List Coord) :
    ((routeL cs).map fun z => |z|).sum + ((routeR cs).map fun z => |z|).sum = (cs.map fun c => |c.2.2|).sum := by
  induction cs with
  | nil => simp [routeL, routeR]
  | cons c cs ih =>
    unfold routeL routeR at ih ⊢
    cases hc : c.1 <;> simp [hc, abs_flipW] at ih ⊢ <;> linarith

theorem flipSum_abs (cs : List Coord) : |flipSum cs| ≤ (cs.map fun c => |c.2.2|).sum := by
  unfold flipSum
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : |(if c.2.1 then c.2.2 else 0)| ≤ |c.2.2| := by split_ifs <;> simp
    calc |(if c.2.1 then c.2.2 else 0) + (cs.map fun c => if c.2.1 then c.2.2 else 0).sum|
        ≤ |(if c.2.1 then c.2.2 else 0)| + |(cs.map fun c => if c.2.1 then c.2.2 else 0).sum| := abs_add_le _ _
      _ ≤ _ := by linarith

theorem coords_sum {n : ℕ} (side f : List Bool) (e : ExactThresholdGate n) (M : ℕ)
    (hM : ∀ i, (e.weight i).natAbs ≤ M) : ((coords side f e).map fun c => |c.2.2|).sum ≤ n * M := by
  unfold coords
  rw [List.map_ofFn]
  have : ∀ i : Fin n, |(e.weight i)| ≤ (M : ℤ) := fun i => by
    have := hM i; rw [Int.abs_eq_natAbs]; exact_mod_cast this
  calc (List.ofFn ((fun c : Coord => |c.2.2|) ∘ fun i : Fin n => (side.getD i false, f.getD i false, e.weight i))).sum
      = ∑ i : Fin n, |e.weight i| := by rw [List.sum_ofFn]; rfl
    _ ≤ ∑ _i : Fin n, (M : ℤ) := Finset.sum_le_sum fun i _ => this i
    _ = n * M := by simp

end NearCubicWires.WireExponent3_5.FinalPass.PoolFit

