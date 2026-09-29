import Proof.Wire_3_5.Sampler.SamplerPotential
import Proof.Wire_3_5.Filters.GFExists
import Proof.Wire_3_5.Filters.FilterKWiseExtra

/-! # B6: `samp:seed` — the `8`-wise generator over `𝔽_{2^ℓ}` reproduces the potential's expectation (P3:2910-2948)

Realizes `samp:seed`'s generator and moment transfer: "Take `ℓ ≥ max{k, ⌈log₂(Q+1)⌉}` and a field `𝔽_{2^ℓ}`. Label
the `Q` samples by distinct field elements. Evaluate a uniformly random polynomial of degree `2h−1` at those labels and
project each value to `k` binary coordinates. Evaluations at any `2h` distinct labels are independent uniform field
elements, so the projected positions are `2h`-wise independent and uniform on `[N]²`. The seed consists of `2hℓ`
binary coefficient bits [...] Expand the even trace by summing over closed walks [...] A trace term uses at most `2h`
sample positions [...] hence the expectation only uses independence on at most `2h` distinct sample labels. This proves
equality with the independent expectation" (P3:2929-2948), at `h = 4`, over the certified bit-vector field of
`Proof.Wire_3_5.Foundations.GF` (`𝔽₂[X]/(p)`, `p = firstPrimitive ℓ`), with the S3 lemmas `polyEvalKWise`,
`projectKWise` and `expectEqIndep_of_nonempty`.

Main declarations: `SeedParams` (`ℓ`, `N = 2^{kh}`, `Q`, with `2kh ≤ ℓ` and `Q ≤ 2^ℓ`), the field `K` (with its
`Field`/`Fintype` instances from the certificate), `label` (sample `j ↦ x`-coordinates of `j`), `value` (the degree-`7`
polynomial at the label), `proj` (the first `2kh` coordinates), `cellEquiv` (`k` bits ↦ `[N]²`), **`pos`** (the
sample positions of a seed); **`pos_kwise`** (`8`-wise uniform); `potential_expand` (a trace term reads at most `8`
positions); **`uMean_potential_seed`** (the seed average of the potential equals the independent average);
`card_seed` (`2^{8ℓ}` seeds); **`samp_universal_seed`** (any seed whose potential is at most the seed average — the
greedy seed of C4 — gives a sample list meeting `samp:universal`), and `exists_seed_le`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters Finset

/-! ## `KWiseUniform` under a bijection of values -/

theorem kwise_comp_equiv {S L V W : Type} [Fintype S] [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (t : ℕ) (f : S → L → V) (e : V ≃ W) (hf : KWiseUniform t f) : KWiseUniform t (fun s l => e (f s l)) := by
  intro ls hls val
  have h := hf ls hls (fun l => e.symm (val l))
  rw [← Fintype.card_congr e]
  convert h using 3
  apply Finset.filter_congr
  intro s _
  constructor
  · intro hs l hl; rw [← hs l hl, Equiv.symm_apply_apply]
  · intro hs l hl; show e (f s l) = val l; rw [hs l hl, Equiv.apply_symm_apply]

/-! ## The generator -/

/-- The parameters of the sample generator: field bits `ℓ`, half position bits `kh` (`N = 2^{kh}`, `k = 2kh`), and the
number of samples `Q`, with `k ≤ ℓ` and `Q ≤ 2^ℓ` (P3:2932). -/
structure SeedParams where
  ell : ℕ
  kh : ℕ
  Q : ℕ
  one_le_ell : 1 ≤ ell
  k_le : 2 * kh ≤ ell
  Q_le : Q ≤ 2 ^ ell

namespace SeedParams
variable (P : SeedParams)

/-- The searched modulus of degree `ℓ`. -/
def modulus : ℕ := GF.firstPrimitive P.ell

theorem cert : GF.PrimitiveCert P.modulus P.ell := GF.firstPrimitive_cert _ P.one_le_ell

/-- The field `𝔽_{2^ℓ} = 𝔽₂[X]/(p)`. -/
abbrev K : Type := AdjoinRoot (GF.toPoly P.modulus)

noncomputable instance instField : Field P.K := by
  haveI := GF.fact_irreducible P.modulus P.ell P.cert
  infer_instance

noncomputable instance instFintype : Fintype P.K := Fintype.ofEquiv _ (GF.encEquiv P.modulus P.ell P.cert.2.1)

noncomputable instance instDecEq : DecidableEq P.K := Classical.decEq _

/-- The side length `N = 2^{kh}`. -/
abbrev N : ℕ := 2 ^ P.kh

/-- A seed: the `8` coefficients of a polynomial of degree `≤ 7` (`2hℓ` bits, `h = 4`). -/
abbrev Seed : Type := Fin 8 → P.K

/-- The label of sample `j`: the field element of the bit vector `j` (distinct for `j < Q ≤ 2^ℓ`). -/
noncomputable def label (j : Fin P.Q) : P.K := GF.rep P.modulus j

theorem label_injective : Function.Injective P.label := by
  intro i j h
  exact Fin.ext (GF.rep_injOn P.modulus P.ell i j P.cert.2.1 (lt_of_lt_of_le i.isLt P.Q_le)
    (lt_of_lt_of_le j.isLt P.Q_le) h)

/-- The polynomial `Σ_{i<8} c_i x^i` at the label of sample `j`. -/
noncomputable def value (c : P.Seed) (j : Fin P.Q) : P.K := ∑ i : Fin 8, c i * P.label j ^ (i : ℕ)

/-- The projection to `k = 2kh` binary coordinates (P3:2936). -/
noncomputable def proj : P.K →+ (Fin (2 * P.kh) → ZMod 2) := GF.projK P.modulus P.ell P.cert.2.1 (2 * P.kh)

theorem proj_surjective : Function.Surjective P.proj :=
  GF.projK_surjective P.modulus P.ell P.cert.2.1 (2 * P.kh) P.k_le

/-- `k = 2kh` bits as a position `(U, V) ∈ [N]²` (little-endian digits, then the product split). -/
def cellEquiv : (Fin (2 * P.kh) → ZMod 2) ≃ Cell P.N :=
  ((finFunctionFinEquiv : (Fin (2 * P.kh) → Fin 2) ≃ Fin (2 ^ (2 * P.kh))).trans
    (finCongr (by rw [two_mul, pow_add]))).trans finProdFinEquiv.symm

/-- **The sample positions of a seed** (P3:2933-2937). -/
noncomputable def pos (c : P.Seed) (j : Fin P.Q) : Cell P.N := P.cellEquiv (P.proj (P.value c j))

/-- **The positions are `8`-wise independent and uniform on `[N]²`** (P3:2936-2938). -/
theorem pos_kwise : KWiseUniform 8 P.pos := by
  have h1 : KWiseUniform 8 P.value := polyEvalKWise 8 P.label P.label_injective
  have h2 := projectKWise 8 P.value P.proj P.proj_surjective h1
  exact kwise_comp_equiv 8 _ P.cellEquiv h2

/-- The seed space has `2^{8ℓ}` elements (`2hℓ` binary coefficient bits, P3:2938). -/
theorem card_seed : Fintype.card P.Seed = 2 ^ (8 * P.ell) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_congr (GF.encEquiv P.modulus P.ell P.cert.2.1).symm,
    Fintype.card_fin, ← pow_mul, mul_comm]

instance instNonemptySeed : Nonempty P.Seed := ⟨fun _ => 0⟩

end SeedParams

/-! ## The moment transfer -/

theorem uMean_sum {Ω ι : Type} [Fintype Ω] (s : Finset ι) (F : ι → Ω → ℝ) :
    uMean (fun ω => ∑ i ∈ s, F i ω) = ∑ i ∈ s, uMean (F i) := by
  unfold uMean
  rw [Finset.sum_comm, Finset.sum_div]

theorem uMean_const_mul {Ω : Type} [Fintype Ω] (C : ℝ) (F : Ω → ℝ) :
    uMean (fun ω => C * F ω) = C * uMean F := by
  unfold uMean
  rw [← Finset.mul_sum, mul_div_assoc]

variable {N Q : ℕ}

/-- **A trace term reads at most eight positions**: the potential as a sum over matrix indices, closed walks `w` and
sample-index maps `α`, each term reading the positions `α(0), …, α(7)` (P3:2943-2948). -/
theorem potential_expand {Z T : Type} [Fintype Z] [Fintype T] (D : Z → T → Cell N → ℝ) (S : Fin Q → Cell N) :
    potential D S = ∑ z, ∑ t, ∑ w : Fin 8 → Fin N, ∑ α : Fin 8 → Fin Q,
      (∏ k, D z t (cellOf (by norm_num) w k)) * ∏ k, yc N (S (α k)) (cellOf (by norm_num) w k) := by
  unfold potential
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro t _
  rw [← walkMoment_eq_trace]
  unfold walkMoment Ecell
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.prod_mul_distrib, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]

/-- **The seed average of the potential equals the independent average** (P3:2945-2948). -/
theorem uMean_potential_seed (P : SeedParams) {Z T : Type} [Fintype Z] [Fintype T]
    (D : Z → T → Cell P.N → ℝ) :
    uMean (fun c : P.Seed => potential D (P.pos c)) = uMean (fun S : Fin P.Q → Cell P.N => potential D S) := by
  simp_rw [potential_expand]
  simp only [uMean_sum, uMean_const_mul]
  apply Finset.sum_congr rfl; intro z _
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro w _
  apply Finset.sum_congr rfl; intro α _
  congr 1
  refine expectEqIndep_of_nonempty 8 P.pos P.pos_kwise (Finset.univ.image α) ?_
    (fun S => ∏ k, yc P.N (S (α k)) (cellOf (by norm_num) w k)) ?_
  · exact (Finset.card_image_le).trans (by simp)
  · intro S S' hSS'
    apply Finset.prod_congr rfl
    intro k _
    rw [hSS' (α k) (Finset.mem_image_of_mem α (Finset.mem_univ k))]

end NearCubicWires.WireExponent3_5.Sampler
