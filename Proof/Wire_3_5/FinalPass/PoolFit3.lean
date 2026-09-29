import Proof.Wire_3_5.FinalPass.PoolFit2

/-! # The pool's coefficient width (mode-generic), part 3: the three fits

From `sourceBudget a (request g) ≤ Bud` at every pool gate and `Bud + n + 2 ≤ h`: the children's coefficients
(`CoefFit`, P3:1612-1613), the pool's P/N fields (`Req.PNFit`) and the dense children (`Req.DenseFit`) fit `h` bits
(alg:disjoint, P3:1596-1615; the pullback, P3:1645-1648, 1655-1658).
* `childBound_of`, **`pnFit_of`**, **`denseFit_of`**, **`coefFit_of`**, **`poolFits_of`**.
Paper quantities of the main types: the pool's fields against the compiler's word width `h`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.PoolFit
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline

variable (a : DecompositionAlgorithm)

theorem childBound_of {n : ℕ} (gates : List (SupportedNormalizedGate n)) (Bud : ℕ)
    (hB : ∀ g ∈ gates, RepairOrdinary.DecompositionSource.sourceBudget a (request g) ≤ Bud) :
    ChildBound a gates (2 ^ Bud) := by
  intro g hg e he
  have hlt : ∀ z ∈ List.ofFn e.weight ++ [e.target], z.natAbs ≤ 2 ^ Bud := fun z hz =>
    le_trans (coef_lt_budget a g e he z hz).le (Nat.pow_le_pow_right (by norm_num) (hB g hg))
  exact ⟨fun i => hlt _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)),
    hlt _ (List.mem_append_right _ (List.mem_singleton_self _))⟩

theorem mem_poolChildren {n : ℕ} (gates : List (SupportedNormalizedGate n)) (flips : List (List Bool))
    (fe : List Bool × ExactThresholdGate n) (h : fe ∈ poolChildren a gates flips) :
    ∃ g ∈ gates, fe.2 ∈ children a g := by
  unfold poolChildren at h
  obtain ⟨f, _, hf⟩ := List.mem_flatMap.mp h
  obtain ⟨g, hg, hg'⟩ := List.mem_flatMap.mp hf
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg'
  exact ⟨g, hg, he⟩

/-- **`PNFit` from a child bound `M` with `(n+1)·M < 2^h`.** -/
theorem pnFit_of (R : PoolReq) (M : ℕ) (hB : ChildBound a R.gates M) (hh : (R.n + 1) * M < 2 ^ R.h) :
    Req.PNFit a R := by
  intro fe hfe q _
  obtain ⟨g, hg, he⟩ := mem_poolChildren a R.gates R.flips fe hfe
  obtain ⟨hw, ht⟩ := hB g hg fe.2 he
  have hM1 : M ≤ (R.n + 1) * M := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  unfold fieldPN
  split_ifs with hq
  · have hz := dense_weight_le R.side fe.1 R.width fe.2 M hw q
    obtain ⟨z, hzd⟩ : ∃ z, z = (denseWeights R.side fe.1 R.width fe.2).getD q 0 := ⟨_, rfl⟩
    rw [← hzd] at hz ⊢
    simp only [pn]
    have h1 : z.toNat ≤ M := by
      have := toNat_le_abs z; exact_mod_cast this.trans hz
    have h2 : (-z).toNat ≤ M := by
      have := negToNat_le_abs z; exact_mod_cast this.trans hz
    omega
  · have hs := splitTarget_le (coords R.side fe.1 fe.2) fe.2.target
    have hc := coords_sum R.side fe.1 fe.2 M hw
    have hta : |fe.2.target| ≤ (M : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht
    have hbound : (|fe.2.target| + ((coords R.side fe.1 fe.2).map fun c => |c.2.2|).sum) ≤ ((R.n + 1) * M : ℕ) := by
      push_cast; nlinarith
    have hh' : (((R.n + 1) * M : ℕ) : ℤ) < ((2 ^ R.h : ℕ) : ℤ) := by exact_mod_cast hh
    constructor
    · have := lt_of_le_of_lt (hs.1.trans hbound) hh'; exact_mod_cast this
    · have := lt_of_le_of_lt (hs.2.trans hbound) hh'; exact_mod_cast this

theorem sum_fin_getD (l : List ℤ) (N : ℕ) : (∑ i : Fin N, |l.getD i 0|) ≤ (l.map fun z => |z|).sum := by
  rw [Fin.sum_univ_eq_sum_range (fun i => |l.getD i 0|)]
  exact sum_getD_le l N

theorem pad_abs_sum (w : ℕ) (L : List ℤ) : ((padTo w L).map fun z => |z|).sum = (L.map fun z => |z|).sum := by
  unfold padTo; simp

/-- **`DenseFit` from a child bound `M` with `(2n+1)·M < 2^h`.** -/
theorem denseFit_of {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width h : ℕ)
    (flips : List (List Bool)) (M : ℕ) (hB : ChildBound a gates M) (hh : (2 * n + 1) * M < 2 ^ h) :
    Req.DenseFit h (densePool a gates side width flips) := by
  intro e he
  unfold densePool at he
  obtain ⟨Lg, hLg, heL⟩ := List.mem_flatten.mp he
  obtain ⟨f, _, hf⟩ := List.mem_flatMap.mp hLg
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp heL
  obtain ⟨hw, ht⟩ := hB g hg e0 he0
  have hc := coords_sum side f e0 M hw
  have hs : (∑ i : Fin (width + width), |(pullDense side f width e0).weight i|) ≤ ((coords side f e0).map fun c => |c.2.2|).sum := by
    show (∑ i : Fin (width + width), |(padTo width (routeL (coords side f e0)) ++ padTo width (routeR (coords side f e0))).getD i 0|) ≤ _
    refine (sum_fin_getD _ _).trans (le_of_eq ?_)
    rw [List.map_append, List.sum_append, pad_abs_sum, pad_abs_sum]
    exact routeLR_sum _
  have hf := flipSum_abs (coords side f e0)
  have hta : |e0.target| ≤ (M : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast ht
  have htg : |(pullDense side f width e0).target| ≤ M + ((coords side f e0).map fun c => |c.2.2|).sum := by
    show |e0.target - flipSum (coords side f e0)| ≤ _
    exact (abs_sub _ _).trans (by linarith)
  have hh' : (((2 * n + 1) * M : ℕ) : ℤ) < ((2 ^ h : ℕ) : ℤ) := by exact_mod_cast hh
  push_cast at hh'
  nlinarith

/-- **`CoefFit` from `sourceBudget ≤ Bud ≤ h`.** -/
theorem coefFit_of (R : PoolReq) (Bud : ℕ)
    (hB : ∀ g ∈ R.gates, RepairOrdinary.DecompositionSource.sourceBudget a (request g) ≤ Bud) (hh : Bud ≤ R.h) :
    CoefFit a R := by
  intro g hg e he z hz
  exact lt_of_lt_of_le (coef_lt_budget a g e he z hz)
    (Nat.pow_le_pow_right (by norm_num) ((hB g hg).trans hh))

theorem two_mul_lt (n Bud : ℕ) : (2 * n + 1) * 2 ^ Bud < 2 ^ (Bud + n + 2) := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have e : 2 ^ (Bud + n + 2) = 2 ^ Bud * (4 * 2 ^ n) := by rw [pow_add, pow_add]; ring
  rw [e]
  have h2 : 0 < 2 ^ Bud := Nat.two_pow_pos _
  nlinarith

/-- **The three fits** from `sourceBudget ≤ Bud` at every pool gate and `Bud + n + 2 ≤ h`. -/
theorem poolFits_of (R : PoolReq) (Bud : ℕ)
    (hB : ∀ g ∈ R.gates, RepairOrdinary.DecompositionSource.sourceBudget a (request g) ≤ Bud)
    (hh : Bud + R.n + 2 ≤ R.h) :
    CoefFit a R ∧ Req.PNFit a R ∧ Req.DenseFit R.h (densePool a R.gates R.side R.width R.flips) := by
  have hC := childBound_of a R.gates Bud hB
  have hlt : (2 * R.n + 1) * 2 ^ Bud < 2 ^ R.h :=
    lt_of_lt_of_le (two_mul_lt R.n Bud) (Nat.pow_le_pow_right (by norm_num) hh)
  refine ⟨coefFit_of a R Bud hB (by omega), pnFit_of a R _ hC (lt_of_le_of_lt ?_ hlt),
    denseFit_of a R.gates R.side R.width R.h R.flips _ hC hlt⟩
  exact Nat.mul_le_mul_right _ (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.PoolFit

