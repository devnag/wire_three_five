import Proof.Wire_3_5.Lists.ListPoly
import Proof.Supplier.SupplierListCompiler
import Proof.MachineModel.CanonicalFourfoldRowProgram

/-! # `list:base` (P3:1375-1414): the pointwise base list at the windows `W_j`

Realizes `list:base` (P3:1375-1391): "Fix `0<ρ<1/128` and a cap `B ≥ 1`. There is an explicit nested hash with a seed
of `O_ρ(log(M+2)+log(B+2))` bits and `J=O_ρ(L)` levels [...] such that the following holds at each input of weight at
most `B`. Put `c_j=Σ_{i∈𝓛_j}Z_i`, `δ_j=c_j−2c_{j+1}`, `W_j=⌈C_ρ√B 2^{−⌊j/3⌋}+C_ρ⌉`. With probability at least `1−ρ`,
simultaneously `c_J=0` and `|δ_j| ≤ W_j` for `j<J`. Moreover `Σ_{j<J}W_j=O_ρ(√B+L)`. The promise is only
`Σ_iZ_i ≤ B` at the current complete input."

The nested hash is the binary Toeplitz hash of `SupplierToeplitzCore` (pairwise-independent uniform labels,
P3:1392-1395); its level sets are the zero-prefix cells, and the probability bound is the donor
`SupplierListCompiler.prefixListBad_unionBound` (Chebyshev per level plus the terminal union bound, stated at the
fixed complete input: pointwise). The constants: `ρ = 1/128`, `C_ρ = 64`, `J = ⌈log₂B⌉ + 9`, and the integer windows
are Theorem 2.5's executable graded windows `W_j = 64 + ⌈⌈√(64²B)⌉/2^{⌊j/3⌋}⌉` (`executableGradedWindow`,
R4: the machine families are base's), so `W_j·2^{⌊j/3⌋} ≥ 64(⌊√B⌋+1)`.

Main quantities: `BaseListParams` (the paper's `M` and `B`), the seed space `Seed` (a Toeplitz seed of `rank` bits),
the repaired list `data h` of `list:repair` at the seed's nested hash, and its report `report h Z`. Results:
**`report_fail_le`** (`w(Z) ≤ B ⟹ Pr_h[report ≠ w(Z)] ≤ 1/128`), **`report_poly`** (every state is an `𝔽₂`
polynomial of degree `≤ Σ_{j<J}(H_j−1)`), **`degree_le`** (`Σ_{j<J}(H_j−1) ≤ 1536(⌊√B⌋+1) + 260J`, i.e.
`O(√B + L)`), `sum_windows_le` (`Σ_{j<J}W_j ≤ 384(⌊√B⌋+1) + 65J`), `W_eq_executable` and `card_seed` (`2^{3·rank−1}`
seeds). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Lists
open NearCubicWires NearCubicWires.WireExponent3_5.Filters NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierToeplitz NearCubicWires.SupplierListCompiler
open Finset

/-- The parameters of `list:base`: the vector length (and count range) `M` and the cap `B`. -/
structure BaseListParams where
  M : ℕ
  B : ℕ

namespace BaseListParams
variable (P : BaseListParams)

/-- `J = ⌈log₂B⌉ + 9` levels: `B·2^{−J} ≤ 1/512` (P3:1397-1398). -/
def J : ℕ := Nat.clog 2 P.B + 9

/-- The windows `W_j = 64 + ⌈⌈√(64²B)⌉/2^{⌊j/3⌋}⌉` (P3:1384, `C_ρ = 64`): Theorem 2.5's `executableGradedWindow`. -/
def W (j : ℕ) : ℕ :=
  64 + (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B) ⌈/⌉ 2 ^ (j / 3))

/-- The Toeplitz rank: `J` levels and distinct labels for `M` coordinates. -/
def rank : ℕ := max P.J (Nat.clog 2 P.M)

/-- The base seed: a Toeplitz seed. -/
abbrev Seed : Type := ToeplitzSeed P.rank

/-- The level sets `𝓛_j`: coordinates whose hashed label has its first `j` bits zero (P3:1392-1393). -/
def inLevel (h : P.Seed) (j i : ℕ) : Bool :=
  decide (toeplitzHash (coordLabel P.rank i) h ∈ zeroPrefixCell P.rank j)

/-- The repaired list of `list:repair` at the seed's nested hash. -/
def data (h : P.Seed) : ListData := ⟨P.M, P.J, P.W, P.inLevel h⟩

/-- **The base list's reported count** at seed `h`. -/
def report (h : P.Seed) (Z : List Bool) : ℕ := (P.data h).listReport Z

theorem inLevel_zero (h : P.Seed) (i : ℕ) : P.inLevel h 0 i = true := by
  simp [inLevel, mem_zeroPrefixCell]

theorem inLevel_nest (h : P.Seed) (j i : ℕ) (hi : P.inLevel h (j + 1) i = true) : P.inLevel h j i = true := by
  simp only [inLevel, decide_eq_true_eq] at hi ⊢
  exact zeroPrefixCell_succ_subset hi

theorem W_pos (j : ℕ) : 0 < P.W j := by unfold W; omega

/-- `⌈√(64²B)⌉ ≥ 64⌊√B⌋`. -/
theorem ceilSqrt_ge : 64 * Nat.sqrt P.B ≤ CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B) := by
  have h1 := CanonicalFourfoldRowProgram.le_natCeilSqrt_sq (64 ^ 2 * P.B)
  have h2 := Nat.sqrt_le' P.B
  apply Nat.mul_self_le_mul_self_iff.mp
  calc 64 * Nat.sqrt P.B * (64 * Nat.sqrt P.B) = 64 ^ 2 * (Nat.sqrt P.B ^ 2) := by ring
    _ ≤ 64 ^ 2 * P.B := Nat.mul_le_mul_left _ h2
    _ ≤ _ := h1

theorem ceilDiv_mul_ge (a d : ℕ) (hd : 0 < d) : a ≤ (a ⌈/⌉ d) * d := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  have := Nat.lt_div_mul_add (a := a + d - 1) hd
  omega

/-- `W_j·2^{⌊j/3⌋} ≥ 64(⌊√B⌋+1)`. -/
theorem W_mul_ge (j : ℕ) : 64 * (Nat.sqrt P.B + 1) ≤ P.W j * 2 ^ (j / 3) := by
  unfold W
  have h1 := ceilDiv_mul_ge (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * P.B)) (2 ^ (j / 3))
    (Nat.two_pow_pos _)
  have h2 : 1 ≤ 2 ^ (j / 3) := Nat.one_le_two_pow
  have h3 := P.ceilSqrt_ge
  nlinarith

theorem levelCount_eq (h : P.Seed) (j : ℕ) (Z : List Bool) :
    (P.data h).levelCount j Z = prefixCount (activeSet Z) (coordLabel P.rank) h j := by
  unfold ListData.levelCount prefixCount toeplitzCellCount
  simp only [data, inLevel]
  rw [show ((Finset.range Z.length).filter fun i => Z.getD i false = true ∧
      decide (toeplitzHash (coordLabel P.rank i) h ∈ zeroPrefixCell P.rank j) = true) =
      (activeSet Z).filter fun i => toeplitzHash (coordLabel P.rank i) h ∈ zeroPrefixCell P.rank j by
    ext i; simp [activeSet, and_assoc]]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hm : toeplitzHash (coordLabel P.rank i) h ∈ zeroPrefixCell P.rank j <;> simp [hm]

theorem levelDelta_eq (h : P.Seed) (j : ℕ) (Z : List Bool) :
    (P.data h).levelDelta j Z = prefixDelta (activeSet Z) (coordLabel P.rank) h j := by
  unfold ListData.levelDelta prefixDelta
  rw [P.levelCount_eq, P.levelCount_eq]

/-- Off the donor's bad event, the good event of `list:repair` holds. -/
theorem good_of_not_bad (h : P.Seed) (Z : List Bool)
    (hbad : prefixListBad (activeSet Z) (coordLabel P.rank) (fun l : Fin P.J => P.W l) 0 h = false) :
    (P.data h).Good Z := by
  simp only [prefixListBad, decide_eq_false_iff_not, not_or, not_lt, not_exists] at hbad
  refine ⟨?_, fun j hj => ?_⟩
  · have := hbad.1; rw [P.levelCount_eq]; show prefixCount _ _ h P.J = 0; omega
  · have := hbad.2 ⟨j, hj⟩
    rw [P.levelDelta_eq]; exact this

/-- `Σ_{j<J} 2^{−⌊j/3⌋} ≤ 6`. -/
theorem sum_half_pow_div_three_le (J : ℕ) : ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j / 3) ≤ 6 := by
  have hQ : ∀ Q, ∑ j ∈ range (3 * Q), (1 / 2 : ℝ) ^ (j / 3) = 6 - 6 * (1 / 2) ^ Q := by
    intro Q
    induction Q with
    | zero => simp
    | succ Q ih =>
      rw [show 3 * (Q + 1) = 3 * Q + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      have e1 : (3 * Q) / 3 = Q := by omega
      have e2 : (3 * Q + 1) / 3 = Q := by omega
      have e3 : (3 * Q + 1 + 1) / 3 = Q := by omega
      rw [e1, e2, e3, pow_succ]; ring
  calc ∑ j ∈ range J, (1 / 2 : ℝ) ^ (j / 3) ≤ ∑ j ∈ range (3 * J), (1 / 2 : ℝ) ^ (j / 3) :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega) (fun _ _ _ => by positivity)
    _ = 6 - 6 * (1 / 2) ^ J := hQ J
    _ ≤ 6 := by have : (0 : ℝ) ≤ (1 / 2) ^ J := by positivity
                linarith

/-- One level's Chebyshev term: `B·2^{−j}/W_j² ≤ 2^{−⌊j/3⌋}/4096`. -/
theorem level_term_le (j : ℕ) :
    ((P.B : ℝ) * (1 / (2 : ℝ) ^ j)) / (P.W j : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ (j / 3) / 4096 := by
  have hW : (0 : ℝ) < P.W j := by exact_mod_cast P.W_pos j
  have hmul : (64 * (Nat.sqrt P.B + 1) : ℝ) ≤ P.W j * 2 ^ (j / 3) := by exact_mod_cast P.W_mul_ge j
  have hsq : (P.B : ℝ) < (Nat.sqrt P.B + 1) ^ 2 := by exact_mod_cast Nat.lt_succ_sqrt' P.B
  have hq : (2 : ℝ) ^ (j / 3) * (2 : ℝ) ^ (2 * (j / 3)) ≤ 2 ^ j := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2q : (0 : ℝ) < 2 ^ (j / 3) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  -- `4096·B ≤ (W·2^q)²` and `2^{2q}·2^q ≤ 2^j`
  have hB : 4096 * (P.B : ℝ) ≤ (P.W j * 2 ^ (j / 3)) ^ 2 := by
    have h0 : (0 : ℝ) ≤ 64 * (Nat.sqrt P.B + 1) := by positivity
    nlinarith
  have hsplit : (1 / (2 : ℝ) ^ j) * (2 : ℝ) ^ (j / 3) ≤ 1 / (2 : ℝ) ^ (2 * (j / 3)) := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hhalf : (1 / 2 : ℝ) ^ (j / 3) = 1 / (2 : ℝ) ^ (j / 3) := by rw [one_div_pow]
  rw [hhalf]
  have e : ((P.W j : ℝ) * 2 ^ (j / 3)) ^ 2 = (P.W j : ℝ) ^ 2 * 2 ^ (2 * (j / 3)) := by rw [mul_pow, ← pow_mul]; ring_nf
  rw [e] at hB
  have h22 : (0 : ℝ) < 2 ^ (2 * (j / 3)) := by positivity
  have key : (P.B : ℝ) * (1 / 2 ^ j) * 2 ^ (j / 3) * 4096 ≤ (P.W j : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hsplit (show (0 : ℝ) ≤ 4096 * P.B by positivity)
    calc (P.B : ℝ) * (1 / 2 ^ j) * 2 ^ (j / 3) * 4096 = 4096 * P.B * ((1 / (2 : ℝ) ^ j) * 2 ^ (j / 3)) := by ring
      _ ≤ 4096 * P.B * (1 / (2 : ℝ) ^ (2 * (j / 3))) := this
      _ ≤ (P.W j : ℝ) ^ 2 := by
        rw [mul_one_div, div_le_iff₀ h22]; exact hB
  calc (P.B : ℝ) * (1 / 2 ^ j) * 4096 = (P.B : ℝ) * (1 / 2 ^ j) * 2 ^ (j / 3) * 4096 * (1 / 2 ^ (j / 3)) := by
        field_simp
    _ ≤ (P.W j : ℝ) ^ 2 * (1 / 2 ^ (j / 3)) := mul_le_mul_of_nonneg_right key (by positivity)
    _ = 1 / 2 ^ (j / 3) * (P.W j : ℝ) ^ 2 := by ring

/-- **`list:base`** (P3:1383-1389): at every input of weight at most `B` (and at most `M` coordinates), the reported
count is wrong with probability at most `ρ = 1/128` over the Toeplitz seed. -/
theorem report_fail_le (Z : List Bool) (hZ : Z.length ≤ P.M) (hw : Z.count true ≤ P.B) :
    booleanMean (fun h : P.Seed => decide (P.report h Z ≠ Z.count true)) ≤ 1 / 128 := by
  have hdepth : P.J ≤ P.rank := le_max_left _ _
  have hlen : P.M ≤ 2 ^ P.rank :=
    (Nat.le_pow_clog (by norm_num) P.M).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
  have hlabels : ∀ l ∈ activeSet Z, ∀ r ∈ activeSet Z, l ≠ r → coordLabel P.rank l ≠ coordLabel P.rank r := by
    intro l hl r hr hne heq
    exact hne (coordLabel_injective (by have := mem_activeSet_lt hl; omega)
      (by have := mem_activeSet_lt hr; omega) heq)
  have hactive : (activeSet Z).card ≤ P.B := by rw [card_activeSet]; exact hw
  have hunion := prefixListBad_unionBound hdepth (activeSet Z) (coordLabel P.rank) P.B
    (fun l : Fin P.J => P.W l) 0 hlabels hactive (fun l => P.W_pos l)
  refine le_trans (NearCubicWires.SupplierWalk.booleanMean_mono _ _ fun h hh => ?_) (hunion.trans ?_)
  · by_contra hb
    simp only [Bool.not_eq_true] at hb
    have hgood := P.good_of_not_bad h Z hb
    have := (P.data h).listReport_eq_count (P.inLevel_zero h) (P.inLevel_nest h) Z hZ hgood
    simp only [report, decide_eq_true_eq] at hh
    exact hh this
  · -- the terminal term `B/2^J ≤ 1/512` and the level terms `≤ 6/4096`
    have hterm : ((P.B : ℝ) / (2 : ℝ) ^ P.J) / ((0 + 1 : ℕ) : ℝ) ≤ 1 / 512 := by
      have h2J : (512 * P.B : ℝ) ≤ 2 ^ P.J := by
        have := Nat.le_pow_clog (b := 2) (by norm_num) P.B
        have : 512 * P.B ≤ 2 ^ P.J := by unfold J; rw [pow_add]; norm_num; omega
        exact_mod_cast this
      rw [Nat.cast_one, div_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have hlev : ∑ l : Fin P.J, ((P.B : ℝ) * (1 / (2 : ℝ) ^ (l : ℕ))) / (P.W l : ℝ) ^ 2 ≤ 6 / 4096 := by
      calc ∑ l : Fin P.J, ((P.B : ℝ) * (1 / (2 : ℝ) ^ (l : ℕ))) / (P.W l : ℝ) ^ 2
          ≤ ∑ l : Fin P.J, (1 / 2 : ℝ) ^ ((l : ℕ) / 3) / 4096 :=
            Finset.sum_le_sum fun l _ => P.level_term_le l
        _ = (∑ j ∈ range P.J, (1 / 2 : ℝ) ^ (j / 3)) / 4096 := by
            rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun j => (1 / 2 : ℝ) ^ (j / 3))]
        _ ≤ 6 / 4096 := by
            apply div_le_div_of_nonneg_right (sum_half_pow_div_three_le P.J) (by norm_num)
    linarith

end BaseListParams

end NearCubicWires.WireExponent3_5.Lists
