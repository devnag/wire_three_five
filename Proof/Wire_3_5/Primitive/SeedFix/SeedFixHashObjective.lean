import Proof.Wire_3_5.Primitive.SeedFix.SeedFixSampObjective

/-! # C4.Hm: the fixed count hash's printed conditional objective (`filt:soft`, P3:2238-2336)

Realizes, at the value level, what `filt:soft`'s hash fixing prints at each prefix of the `s_h`-bit hash seed:
"Expanding a discrepancy power gives `δ_{a,j}^{2t} = Σ_{i_1,…,i_{2t}} Z_{a,i_1}⋯Z_{a,i_{2t}} A_{i_1,j}⋯A_{i_{2t},j}`,
`A_{i,j} = 1[i∈L_j] − 2·1[i∈L_{j+1}]`. Expand each `A`-product into at most `2^{2t}` signed products of hash prefix
indicators. [...] Each product of indicators is therefore a system of binary linear equations in the seed bits. After
fixing `p`, Gaussian elimination finds its conditional probability [...] The terminal counts are handled in the same
way. One prefix-independent positive integer `Δ₀ = 2^{s_h}Π_{j<J}W_j^{2t}` clears every coefficient denominator [...]
At prefix `p` print `V_p(z) = Δ₀Σ_yΣ_e F_aux(e,x(y,z))·E_h[H_h(x(y,z)) | p]`" (P3:2253-2290), with the column bound
(P3:2291-2293) and "Greedily choose a child with no larger value" (P3:2331-2335).

The hash of `filt:majorant` at a seed code is the reference generator `JoinElimination.gen` over the majorant's field
(`valueBits_eq_gen`), so `i ∈ L_j` is the linear condition "the low `j` bits of `gen(σ, i)` vanish" (`levelNum`), and
`A_{i,j} = 1[low_{j+1} = 2^j] − 1[low_{j+1} = 0]` needs one constraint width `j + 1` per product.

Paper quantities: the cleared majorant term `hTermZ` (`Π_jW_j^{2t}·(c_J + Σ_jδ_j^{2t}/W_j^{2t})`), its elimination form
`hashElimZ` (the sum over the completions of a prefix, by Gaussian-elimination counts), the printed child sum `hashSum`
(`Σ_xΣ_e F_aux(e,x)·Σ_a hashElimZ`), and the objective `𝒰` of `FinalPass.objQ`.

Results: `coefVal_eq_seedCoeff`, **`valueBits_eq_gen`**, **`dataBits_eq`** (the lists of a seed code are those of its
seed number), `hTermZ_cast`, **`hashElimZ_eq`**, `hashElimZ_nonneg`, **`hashElimZ_le`** (the column range),
**`hashSum_scaled`**, and **`hashLoop_eq`** (the printed decisions are the fixed hash's bits `thrHashBits`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.GF NearCubicWires.WireExponent3_5.Primitive
open Finset

/-! ## The majorant's hash is the reference generator -/

section Levels
variable (MP : MajorantParams)

theorem one_le_ell0 : 1 ≤ MP.ell0 := Nat.one_le_iff_ne_zero.mpr MP.ell0_ne_zero

/-- A coefficient of a seed code is the coefficient of its seed number (bits `[rℓ₀, (r+1)ℓ₀)`). -/
theorem coefVal_eq_seedCoeff (s : Fin (2 * MP.t * MP.ell0) → Bool) (r : Fin (2 * MP.t)) :
    MajorantBits.coefVal MP s r = seedCoeff MP.ell0 (bitsNum _ s) r := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < MP.ell0
  · unfold MajorantBits.coefVal
    rw [testBit_decodeVal MP.ell0 _ ⟨b, hb⟩, testBit_seedCoeff _ _ _ _ hb, testBit_bitsNum]
    have hlt : (r : ℕ) * MP.ell0 + b < 2 * MP.t * MP.ell0 := by
      have := r.isLt
      calc (r : ℕ) * MP.ell0 + b < (r + 1) * MP.ell0 := by nlinarith
        _ ≤ 2 * MP.t * MP.ell0 := Nat.mul_le_mul_right _ this
    rw [dif_pos hlt]
    have hidx : finProdFinEquiv (r, (⟨b, hb⟩ : Fin MP.ell0)) = ⟨(r : ℕ) * MP.ell0 + b, hlt⟩ := by
      apply Fin.ext
      simp only [finProdFinEquiv_apply_val]
      ring
    rw [hidx]
    cases s ⟨(r : ℕ) * MP.ell0 + b, hlt⟩ <;> decide
  · have hle : MP.ell0 ≤ b := by omega
    unfold MajorantBits.coefVal
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (decodeVal_lt MP.ell0 _) (Nat.pow_le_pow_right (by norm_num) hle)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (seedCoeff_lt MP.ell0 _ _) (Nat.pow_le_pow_right (by norm_num) hle))]

/-- **The hash value is the reference generator's value** (P3:2150-2157, 2932-2937). -/
theorem valueBits_eq_gen (s : Fin (2 * MP.t * MP.ell0) → Bool) (i : ℕ) (hi : i < 2 ^ MP.ell0) :
    MajorantBits.valueBits MP s i = JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) (bitsNum _ s) i := by
  have hp := MP.refCert.2.1
  obtain ⟨h1, h2⟩ := hornerBits_spec MP.refMod MP.ell0 hp i hi (2 * MP.t) (MajorantBits.coefVal MP s)
    (MajorantBits.coefVal_lt MP s)
  obtain ⟨h3, h4⟩ := gen_spec MP.refMod MP.ell0 (bitsNum _ s) i hp (one_le_ell0 MP) hi (2 * MP.t)
  rw [gen_eq]
  apply rep_injOn MP.refMod MP.ell0 _ _ hp h1 h3
  rw [h2, h4, ← Fin.sum_univ_eq_sum_range (fun r => rep MP.refMod (seedCoeff MP.ell0 (bitsNum _ s) r) *
    rep MP.refMod i ^ r)]
  refine sum_congr rfl fun r _ => ?_
  rw [coefVal_eq_seedCoeff]

/-- **The level sets at a seed number** (P3:2150-2157): `i < M` is in `L_j` iff the low `j` bits of `gen(σ, i)` vanish. -/
def levelNum (σ j i : ℕ) : Bool :=
  if i < MP.M then decide (JoinElimination.proj j (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ i) = 0) else true

/-- The count lists at a seed number. -/
def dataNum (σ : ℕ) : ListData := ⟨MP.M, MP.J, MP.W, levelNum MP σ⟩

theorem proj_eq_zero_iff (j v ℓ : ℕ) (hv : v < 2 ^ ℓ) :
    JoinElimination.proj j v = 0 ↔ ∀ b < ℓ, b < j → v.testBit b = false := by
  unfold JoinElimination.proj
  constructor
  · intro h b _ hbj
    have := congrArg (fun x => x.testBit b) h
    simp only [Nat.testBit_mod_two_pow, hbj, decide_true, Bool.true_and, Nat.zero_testBit] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro b
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hbj : b < j
    · by_cases hbl : b < ℓ
      · simp [hbj, h b hbl hbj]
      · have hz : v.testBit b = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega : ℓ ≤ b)))
        simp [hbj, hz]
    · simp [hbj]

theorem inLevelBits_eq (s : Fin (2 * MP.t * MP.ell0) → Bool) (j i : ℕ) :
    MajorantBits.inLevelBits MP s j i = levelNum MP (bitsNum _ s) j i := by
  unfold MajorantBits.inLevelBits levelNum
  by_cases hi : i < MP.M
  · rw [if_pos hi, if_pos hi]
    have hi2 : i < 2 ^ MP.ell0 := lt_of_lt_of_le hi MP.M_le_two_pow
    rw [valueBits_eq_gen MP s i hi2]
    have hv := (gen_spec MP.refMod MP.ell0 (bitsNum _ s) i MP.refCert.2.1 (one_le_ell0 MP) hi2 (2 * MP.t)).1
    rw [← gen_eq] at hv
    exact decide_eq_decide.mpr (proj_eq_zero_iff j _ MP.ell0 hv).symm
  · rw [if_neg hi, if_neg hi]

/-- **The lists of a seed code are those of its seed number.** -/
theorem dataBits_eq (s : Fin (2 * MP.t * MP.ell0) → Bool) :
    MajorantBits.dataBits MP s = dataNum MP (bitsNum _ s) := by
  unfold MajorantBits.dataBits dataNum
  congr 1
  funext j i
  exact inLevelBits_eq MP s j i

end Levels

/-! ## The cleared term and its elimination form -/

section Moments
variable (MP : MajorantParams)

/-- `Π_{j<J} W_j^{2t}` (P3:2280-2281, without the seed factor). -/
def prodW : ℕ := ∏ j ∈ range MP.J, MP.W j ^ (2 * MP.t)

/-- `Π_{j'<J, j'≠j} W_{j'}^{2t}`: the cleared denominator of level `j`. -/
def clearW (j : ℕ) : ℕ := ∏ j' ∈ (range MP.J).erase j, MP.W j' ^ (2 * MP.t)

theorem prodW_eq (j : ℕ) (hj : j < MP.J) : prodW MP = MP.W j ^ (2 * MP.t) * clearW MP j :=
  (mul_prod_erase (range MP.J) (fun j' => MP.W j' ^ (2 * MP.t)) (mem_range.mpr hj)).symm

theorem prodW_pos : 0 < prodW MP := prod_pos fun j _ => pow_pos (by have := MP.W_ge j; omega) _

/-- **The cleared majorant term** of one population, an integer: `Π_jW_j^{2t}·(c_J + Σ_jδ_j^{2t}/W_j^{2t})`. -/
def hTermZ (D : ListData) (Z : List Bool) : ℤ :=
  (D.levelCount MP.J Z : ℤ) * prodW MP + ∑ j ∈ range MP.J, D.levelDelta j Z ^ (2 * MP.t) * (clearW MP j : ℤ)

theorem hTermZ_cast (σ : ℕ) (Z : List Bool) :
    (hTermZ MP (dataNum MP σ) Z : ℚ) = termQ (dataNum MP σ) MP.t Z * prodW MP := by
  unfold hTermZ termQ
  push_cast
  rw [add_mul, sum_mul]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hW : (MP.W j : ℚ) ≠ 0 := by have := MP.W_ge j; exact_mod_cast (by omega : MP.W j ≠ 0)
  rw [prodW_eq MP j (mem_range.mp hj)]
  show (dataNum MP σ).levelDelta j Z ^ (2 * MP.t) * ((clearW MP j : ℕ) : ℚ) =
    ((dataNum MP σ).levelDelta j Z : ℚ) ^ (2 * MP.t) / (MP.W j : ℚ) ^ (2 * MP.t) *
      ((MP.W j ^ (2 * MP.t) * clearW MP j : ℕ) : ℚ)
  push_cast
  field_simp

/-- The completion count of a constraint list at width `k`, by Gaussian elimination (`condProbGauss`). -/
def cntG (k plen pre : ℕ) (cons : List (ℕ × ℕ)) : ℕ :=
  (JoinElimination.condProbGauss MP.refMod MP.ell0 (2 * MP.t) k plen pre cons).1

/-- The seed number of completion `r` of a prefix. -/
def compl (plen pre r : ℕ) : ℕ := pre % 2 ^ plen + (r <<< plen)

/-- **The elimination count is the completion count** (`SamplerCond.condProbGauss_eq_brute`). -/
theorem cntG_eq (k plen pre : ℕ) (cons : List (ℕ × ℕ)) (hk : k ≤ MP.ell0) (hplen : plen ≤ 2 * MP.t * MP.ell0)
    (hcons : ∀ c ∈ cons, c.1 < 2 ^ MP.ell0 ∧ c.2 < 2 ^ k) :
    (cntG MP k plen pre cons : ℤ) = ∑ r ∈ range (2 ^ (2 * MP.t * MP.ell0 - plen)),
      if ∀ c ∈ cons, JoinElimination.proj k (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) (compl plen pre r) c.1)
        = c.2 then 1 else 0 := by
  unfold cntG
  rw [condProbGauss_eq_brute MP.refMod MP.ell0 (2 * MP.t) k plen pre cons MP.refCert.2.1 (one_le_ell0 MP) hk hplen
    hcons, condProbBrute_fst, Finset.natCast_card_filter]
  refine sum_congr rfl fun r _ => ?_
  unfold consOk compl
  simp only [List.all_eq_true, decide_eq_true_eq]

/-- `A_{i,j} = 1[i∈L_j] − 2·1[i∈L_{j+1}] = 1[low_{j+1} = 2^j] − 1[low_{j+1} = 0]`. -/
theorem levelA_eq (j g : ℕ) :
    ((if JoinElimination.proj j g = 0 then 1 else 0 : ℤ) - 2 * (if JoinElimination.proj (j + 1) g = 0 then 1 else 0)) =
      (if JoinElimination.proj (j + 1) g = 2 ^ j then 1 else 0) - (if JoinElimination.proj (j + 1) g = 0 then 1 else 0) := by
  unfold JoinElimination.proj
  have hx : g % 2 ^ (j + 1) < 2 * 2 ^ j := by rw [← pow_succ']; exact Nat.mod_lt _ (by positivity)
  have hm : g % 2 ^ j = g % 2 ^ (j + 1) % 2 ^ j := by
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_succ j))]
  have hj : 0 < 2 ^ j := by positivity
  rw [hm]
  generalize g % 2 ^ (j + 1) = x at hx ⊢
  by_cases h0 : x = 0
  · subst h0; simp; omega
  · by_cases h1 : x = 2 ^ j
    · subst h1; simp
    · have : x % 2 ^ j ≠ 0 := by
        intro h
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h
        have : q < 2 := by nlinarith
        interval_cases q <;> simp_all
      simp [h0, h1, this]

/-- The constraints of a moment tuple `ι` with sign pattern `γ` at level `j`: `low_{j+1}(gen(σ, ι_r)) = γ_r ? 2^j : 0`. -/
def momentCons (j : ℕ) {L : ℕ} (ι : Fin (2 * MP.t) → Fin L) (γ : Fin (2 * MP.t) → Bool) : List (ℕ × ℕ) :=
  (List.finRange (2 * MP.t)).map fun r => ((ι r : ℕ), if γ r then 2 ^ j else 0)

/-- **The elimination form** (P3:2253-2283): the sum of the cleared term over the completions of a prefix, as
`Π_jW_j^{2t}·Σ_i Z_i·#[i∈L_J] + Σ_j Π_{j'≠j}W_{j'}^{2t}·Σ_ι Π_rZ_{ι_r}·Σ_γ(−1)^{#{γ_r = 0}}·#[moment constraints]`,
every count by Gaussian elimination. -/
def hashElimZ (Z : List Bool) (plen pre : ℕ) : ℤ :=
  (prodW MP : ℤ) * ∑ i : Fin Z.length, bitZ (Z.get i) * (cntG MP MP.J plen pre [((i : ℕ), 0)] : ℤ) +
    ∑ j ∈ range MP.J, (clearW MP j : ℤ) * ∑ ι : Fin (2 * MP.t) → Fin Z.length, (∏ r, bitZ (Z.get (ι r))) *
      ∑ γ : Fin (2 * MP.t) → Bool, (-1 : ℤ) ^ (univ.filter fun r => γ r = false).card *
        (cntG MP (j + 1) plen pre (momentCons MP j ι γ) : ℤ)

theorem levelCount_sum (D : ListData) (j : ℕ) (Z : List Bool) :
    (D.levelCount j Z : ℤ) = ∑ i : Fin Z.length, bitZ (Z.get i) * (if D.inLevel j i = true then 1 else 0) := by
  unfold ListData.levelCount
  rw [natCast_card_filter, ← Fin.sum_univ_eq_sum_range (fun i => if (Z.getD i false = true ∧ D.inLevel j i = true)
    then (1 : ℤ) else 0)]
  refine sum_congr rfl fun i _ => ?_
  have hg : Z.getD i false = Z.get i := by simp
  rw [hg]
  cases Z.get i <;> simp [bitZ]

theorem inLevel_dataNum (σ j i : ℕ) (hi : i < MP.M) :
    (dataNum MP σ).inLevel j i = decide (JoinElimination.proj j (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ i) = 0) := by
  show levelNum MP σ j i = _
  unfold levelNum
  rw [if_pos hi]

theorem ite_decide_eq (P : Prop) [Decidable P] : (if decide P = true then (1 : ℤ) else 0) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]

theorem levelDelta_sum (σ j : ℕ) (Z : List Bool) (hZ : Z.length ≤ MP.M) :
    ((dataNum MP σ).levelDelta j Z : ℤ) = ∑ i : Fin Z.length, bitZ (Z.get i) *
      ((if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ i) = 2 ^ j then 1 else 0) -
        (if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ i) = 0 then 1 else 0)) := by
  unfold ListData.levelDelta
  rw [levelCount_sum, levelCount_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) < MP.M := lt_of_lt_of_le i.isLt hZ
  rw [inLevel_dataNum MP σ j i hi, inLevel_dataNum MP σ (j + 1) i hi, ite_decide_eq, ite_decide_eq, ← levelA_eq]
  ring

theorem sum_pow_fin {L : ℕ} (f : Fin L → ℤ) (n : ℕ) : (∑ i, f i) ^ n = ∑ ι : Fin n → Fin L, ∏ r, f (ι r) := by
  rw [← Fin.prod_const, prod_univ_sum, Fintype.piFinset_univ]

theorem prod_sub_expand {n : ℕ} (a b : Fin n → ℤ) :
    ∏ r, (a r - b r) = ∑ γ : Fin n → Bool, (-1 : ℤ) ^ (univ.filter fun r => γ r = false).card *
      ∏ r, (if γ r then a r else b r) := by
  have h1 : ∀ r, a r - b r = ∑ c : Bool, (if c then a r else -b r) := fun r => by
    rw [Fintype.sum_bool]; simp only [if_true, Bool.false_eq_true, if_false]; ring
  simp_rw [h1]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun γ _ => ?_
  have h2 : ∀ r, (if γ r then a r else -b r) = (if γ r then 1 else -1) * (if γ r then a r else b r) := fun r => by
    cases γ r <;> simp
  simp_rw [h2]
  rw [prod_mul_distrib, prod_ite, prod_const_one, one_mul, prod_const]
  congr 2
  simp only [Bool.not_eq_true]

theorem prod_indicator_momentCons (σ j : ℕ) {L : ℕ} (ι : Fin (2 * MP.t) → Fin L) (γ : Fin (2 * MP.t) → Bool) :
    ∏ r, (if γ r then (if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ (ι r)) = 2 ^ j
        then (1 : ℤ) else 0) else
        (if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ (ι r)) = 0 then 1 else 0)) =
      if ∀ c ∈ momentCons MP j ι γ,
        JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ c.1) = c.2 then 1 else 0 := by
  have h : ∀ r, (if γ r then (if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ (ι r))
      = 2 ^ j then (1 : ℤ) else 0) else
      (if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ (ι r)) = 0 then 1 else 0)) =
      if JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ (ι r)) =
        (if γ r then 2 ^ j else 0) then 1 else 0 := fun r => by cases γ r <;> simp
  simp_rw [h]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  unfold momentCons
  simp only [List.forall_mem_map, List.mem_finRange, true_implies]

theorem levelCountJ_expand (σ : ℕ) (Z : List Bool) (hZ : Z.length ≤ MP.M) :
    ((dataNum MP σ).levelCount MP.J Z : ℤ) = ∑ i : Fin Z.length, bitZ (Z.get i) *
      (if JoinElimination.proj MP.J (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ i) = 0 then 1 else 0) := by
  rw [levelCount_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [inLevel_dataNum MP σ MP.J i (lt_of_lt_of_le i.isLt hZ), ite_decide_eq]

theorem deltaPow_expand (σ j : ℕ) (Z : List Bool) (hZ : Z.length ≤ MP.M) :
    ((dataNum MP σ).levelDelta j Z) ^ (2 * MP.t) = ∑ ι : Fin (2 * MP.t) → Fin Z.length, (∏ r, bitZ (Z.get (ι r))) *
      ∑ γ : Fin (2 * MP.t) → Bool, (-1 : ℤ) ^ (univ.filter fun r => γ r = false).card *
        (if ∀ c ∈ momentCons MP j ι γ,
          JoinElimination.proj (j + 1) (JoinElimination.gen MP.refMod MP.ell0 (2 * MP.t) σ c.1) = c.2 then 1 else 0) := by
  rw [levelDelta_sum MP σ j Z hZ, sum_pow_fin]
  refine sum_congr rfl fun ι _ => ?_
  rw [prod_mul_distrib, prod_sub_expand]
  congr 1
  refine sum_congr rfl fun γ _ => ?_
  rw [prod_indicator_momentCons]

/-- **The elimination form is the sum of the cleared term over the completions of the prefix** (P3:2253-2283). -/
theorem hashElimZ_eq (Z : List Bool) (hZ : Z.length ≤ MP.M) (plen pre : ℕ) (hplen : plen ≤ 2 * MP.t * MP.ell0) :
    hashElimZ MP Z plen pre =
      ∑ rr ∈ range (2 ^ (2 * MP.t * MP.ell0 - plen)), hTermZ MP (dataNum MP (compl plen pre rr)) Z := by
  have hlab : ∀ i : Fin Z.length, (i : ℕ) < 2 ^ MP.ell0 :=
    fun i => lt_of_lt_of_le (lt_of_lt_of_le i.isLt hZ) MP.M_le_two_pow
  have hJ := MP.J_lt_ell0
  unfold hTermZ hashElimZ
  rw [sum_add_distrib]
  congr 1
  · rw [← sum_mul, mul_comm]
    congr 1
    simp_rw [levelCountJ_expand MP _ Z hZ]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_sum]
    congr 1
    rw [cntG_eq MP MP.J plen pre _ hJ.le hplen (by
      intro c hc; rw [List.mem_singleton] at hc; subst hc; exact ⟨hlab i, Nat.two_pow_pos _⟩)]
    simp only [List.mem_singleton, forall_eq]
  · rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    rw [← sum_mul, mul_comm]
    congr 1
    have hj1 : j + 1 ≤ MP.ell0 := by have := mem_range.mp hj; omega
    simp_rw [deltaPow_expand MP _ j Z hZ]
    rw [sum_comm]
    refine sum_congr rfl fun ι _ => ?_
    rw [← mul_sum]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl fun γ _ => ?_
    rw [← mul_sum]
    congr 1
    refine (cntG_eq MP (j + 1) plen pre _ hj1 hplen ?_)
    intro c hc
    unfold momentCons at hc
    simp only [List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨r, rfl⟩ := hc
    refine ⟨hlab (ι r), ?_⟩
    split_ifs
    · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    · exact Nat.two_pow_pos _

theorem levelCount_le (D : ListData) (j : ℕ) (Z : List Bool) : D.levelCount j Z ≤ Z.length := by
  unfold ListData.levelCount
  exact (card_filter_le _ _).trans (by simp)

theorem hTermZ_nonneg (D : ListData) (Z : List Bool) : 0 ≤ hTermZ MP D Z := by
  unfold hTermZ
  refine add_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sum_nonneg fun j _ => ?_)
  exact mul_nonneg (Even.pow_nonneg ⟨MP.t, by ring⟩ _) (Nat.cast_nonneg _)

theorem clearW_le (j : ℕ) (hj : j < MP.J) : clearW MP j ≤ prodW MP := by
  rw [prodW_eq MP j hj]
  have : 1 ≤ MP.W j ^ (2 * MP.t) := Nat.one_le_pow _ _ (by have := MP.W_ge j; omega)
  nlinarith

/-- The cleared term's unconditional bound (the finite `H_max` of `filt:majorant`, P3:2142, 2200-2202, cleared). -/
theorem hTermZ_le (D : ListData) (Z : List Bool) (hZ : Z.length ≤ MP.M) :
    hTermZ MP D Z ≤ (prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t)) := by
  unfold hTermZ
  have hc : (D.levelCount MP.J Z : ℤ) ≤ MP.M := by exact_mod_cast (levelCount_le D MP.J Z).trans hZ
  have hd : ∀ j ∈ range MP.J, D.levelDelta j Z ^ (2 * MP.t) * (clearW MP j : ℤ) ≤
      (3 * MP.M : ℤ) ^ (2 * MP.t) * (prodW MP : ℤ) := by
    intro j hj
    have h1 : |D.levelDelta j Z| ≤ 3 * MP.M := by
      unfold ListData.levelDelta
      have a1 : (D.levelCount j Z : ℤ) ≤ MP.M := by exact_mod_cast (levelCount_le D j Z).trans hZ
      have a2 : (D.levelCount (j + 1) Z : ℤ) ≤ MP.M := by exact_mod_cast (levelCount_le D (j + 1) Z).trans hZ
      rw [abs_le]; constructor <;> omega
    have h2 : D.levelDelta j Z ^ (2 * MP.t) ≤ (3 * MP.M : ℤ) ^ (2 * MP.t) := by
      rw [← Even.pow_abs ⟨MP.t, by ring⟩]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 _
    exact mul_le_mul h2 (by exact_mod_cast clearW_le MP j (mem_range.mp hj)) (Nat.cast_nonneg _) (by positivity)
  calc (D.levelCount MP.J Z : ℤ) * prodW MP + ∑ j ∈ range MP.J, D.levelDelta j Z ^ (2 * MP.t) * (clearW MP j : ℤ)
      ≤ MP.M * prodW MP + ∑ _j ∈ range MP.J, (3 * MP.M : ℤ) ^ (2 * MP.t) * (prodW MP : ℤ) :=
        add_le_add (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) (sum_le_sum hd)
    _ = (prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t)) := by rw [sum_const, card_range, nsmul_eq_mul]; ring

theorem hashElimZ_nonneg (Z : List Bool) (hZ : Z.length ≤ MP.M) (plen pre : ℕ) (hplen : plen ≤ 2 * MP.t * MP.ell0) :
    0 ≤ hashElimZ MP Z plen pre := by
  rw [hashElimZ_eq MP Z hZ plen pre hplen]
  exact sum_nonneg fun _ _ => hTermZ_nonneg MP _ Z

/-- **The column range** of one population's printed term (filt:column-bound, P3:2291-2293). -/
theorem hashElimZ_le (Z : List Bool) (hZ : Z.length ≤ MP.M) (plen pre : ℕ) (hplen : plen ≤ 2 * MP.t * MP.ell0) :
    hashElimZ MP Z plen pre ≤
      2 ^ (2 * MP.t * MP.ell0 - plen) * ((prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t))) := by
  rw [hashElimZ_eq MP Z hZ plen pre hplen]
  calc ∑ rr ∈ range (2 ^ (2 * MP.t * MP.ell0 - plen)), hTermZ MP (dataNum MP (compl plen pre rr)) Z
      ≤ ∑ _rr ∈ range (2 ^ (2 * MP.t * MP.ell0 - plen)), (prodW MP : ℤ) * (MP.M + MP.J * (3 * MP.M) ^ (2 * MP.t)) :=
        sum_le_sum fun _ _ => hTermZ_le MP _ Z hZ
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

end Moments

/-! ## The printed child sums are the scaled conditional objectives -/

section Objective
variable (MP : MajorantParams) {X E K : Type} [Fintype X] [Fintype E] [Fintype K]
  (F : E → X → Bool) (pops : K → X → List Bool)

/-- **The objective `𝒰`** at a seed number (P3:2239-2241): `E_x a(x)·Σ_k (c_J + Σ_jδ_j^{2t}/W_j^{2t})` with
`a(x) = E_e F_aux(e, x)`. -/
def hashObj (σ : ℕ) : ℚ := qMean fun x => qMean (fun e => bitQ (F e x)) * ∑ k, termQ (dataNum MP σ) MP.t (pops k x)

/-- **The printed child sum** `Σ_z V_p(z) = Σ_xΣ_e F_aux(e,x)·Σ_k hashElimZ(pop_k(x))` (P3:2285-2290, cleared by
`Π_jW_j^{2t}` and summed over the completions instead of averaged). -/
def hashSum (p : List Bool) : ℤ := ∑ x, ∑ e, bitZ (F e x) * ∑ k, hashElimZ MP (pops k x) p.length (listNum p)

theorem bitZ_rat (b : Bool) : ((bitZ b : ℤ) : ℚ) = bitQ b := by cases b <;> simp [bitZ, bitQ]

theorem compl_listNum (q : List Bool) (r : ℕ) : compl q.length (listNum q) r = listNum q + 2 ^ q.length * r := by
  unfold compl
  rw [Nat.mod_eq_of_lt (listNum_lt q), Nat.shiftLeft_eq, mul_comm]

/-- **The child sums are `|X||E|Π_jW_j^{2t}·2^{s_h−|p|−1}` times the conditional objectives** (for nonempty points and
seeds; otherwise both vanish). -/
theorem hashSum_scaled (hpops : ∀ k x, (pops k x).length ≤ MP.M) :
    ∃ c : ℕ → ℚ, ScaledSums (2 * MP.t * MP.ell0) (fun s => hashObj MP F pops (bitsNum _ s)) (hashSum MP F pops) c := by
  set m := 2 * MP.t * MP.ell0
  have hobj : ∀ σ, hashObj MP F pops σ = (∑ x, ∑ e, ∑ k, bitQ (F e x) * termQ (dataNum MP σ) MP.t (pops k x)) /
      ((Fintype.card X : ℚ) * Fintype.card E) := by
    intro σ
    unfold hashObj qMean
    rw [mul_comm (Fintype.card X : ℚ), ← div_div]
    congr 1
    rw [sum_div]
    refine sum_congr rfl fun x _ => ?_
    beta_reduce
    rw [div_mul_eq_mul_div, sum_mul]
    congr 1
    exact sum_congr rfl fun e _ => by rw [mul_sum]
  have key : ∀ q : List Bool, q.length ≤ m →
      (hashSum MP F pops q : ℚ) = (Fintype.card X : ℚ) * Fintype.card E * prodW MP *
        ∑ r ∈ range (2 ^ (m - q.length)), hashObj MP F pops (listNum q + 2 ^ q.length * r) := by
    intro q hq
    have hL : (hashSum MP F pops q : ℚ) = prodW MP * ∑ r ∈ range (2 ^ (m - q.length)), ∑ x, ∑ e, ∑ k,
        bitQ (F e x) * termQ (dataNum MP (listNum q + 2 ^ q.length * r)) MP.t (pops k x) := by
      unfold hashSum
      push_cast
      simp only [hashElimZ_eq MP _ (hpops _ _) _ _ hq, compl_listNum]
      push_cast
      simp only [hTermZ_cast, bitZ_rat, mul_sum]
      calc ∑ x, ∑ e, ∑ k, ∑ r ∈ range (2 ^ (m - q.length)),
            bitQ (F e x) * (termQ (dataNum MP (listNum q + 2 ^ q.length * r)) MP.t (pops k x) * prodW MP)
          = ∑ x, ∑ e, ∑ r ∈ range (2 ^ (m - q.length)), ∑ k,
            bitQ (F e x) * (termQ (dataNum MP (listNum q + 2 ^ q.length * r)) MP.t (pops k x) * prodW MP) :=
            sum_congr rfl fun x _ => sum_congr rfl fun e _ => sum_comm
        _ = ∑ x, ∑ r ∈ range (2 ^ (m - q.length)), ∑ e, ∑ k,
            bitQ (F e x) * (termQ (dataNum MP (listNum q + 2 ^ q.length * r)) MP.t (pops k x) * prodW MP) :=
            sum_congr rfl fun x _ => sum_comm
        _ = ∑ r ∈ range (2 ^ (m - q.length)), ∑ x, ∑ e, ∑ k,
            bitQ (F e x) * (termQ (dataNum MP (listNum q + 2 ^ q.length * r)) MP.t (pops k x) * prodW MP) := sum_comm
        _ = _ := by
            refine sum_congr rfl fun r _ => sum_congr rfl fun x _ => sum_congr rfl fun e _ => sum_congr rfl
              fun k _ => ?_
            ring
    rw [hL]
    simp only [hobj]
    rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
    · have : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
      simp
    rcases Nat.eq_zero_or_pos (Fintype.card E) with hE | hE
    · have : IsEmpty E := Fintype.card_eq_zero_iff.mp hE
      simp
    have hXE : (Fintype.card X : ℚ) * Fintype.card E ≠ 0 := by positivity
    rw [← sum_div, mul_div_assoc', mul_comm _ (prodW MP : ℚ), mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ hXE]
  refine ⟨fun i => max (Fintype.card X : ℚ) 1 * max (Fintype.card E : ℚ) 1 * prodW MP * 2 ^ (m - i - 1),
    fun i => by have := prodW_pos MP; positivity, fun p b hp => ?_⟩
  have hq : (p ++ [b]).length ≤ m := by simp; omega
  have hc := condMean_bits (p ++ [b]) m (hashObj MP F pops) hq
  have hexp : m - p.length - 1 = m - (p ++ [b]).length := by simp; omega
  rw [hc, key _ hq]
  beta_reduce
  rw [hexp]
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
  · have : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
    simp [hobj]
  rcases Nat.eq_zero_or_pos (Fintype.card E) with hE | hE
  · have : IsEmpty E := Fintype.card_eq_zero_iff.mp hE
    simp [hobj]
  rw [max_eq_left (by exact_mod_cast hX), max_eq_left (by exact_mod_cast hE)]
  field_simp

end Objective

/-! ## The threshold-top call's fixed hash -/

section Thr
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime NearCubicWires.SupplierEstimator
open NearCubicWires.ExecutableInterfaces NearCubicWires.WireExponent3_5.Stars
variable (P : StarParams) (σ : P.Translation) {a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit P.n)
  (carriers : List (Carrier P.n)) (FP : GapParams) (algorithm : RepairRepresentation.DecompositionAlgorithm) (den e t J : ℕ)

/-- The call's digit populations have at most `M` coordinates (binary digits, `v_{i,d} ≤ 1`). -/
theorem thrDigitPop_length (g : ThrEq P Cs algorithm) (pr : PrimeIndex (thrCutoff P Cs algorithm den))
    (d : Fin (thrDigits P Cs algorithm den)) (sgn : Bool) (c : BitInput P.n) (u v : P.Errors) :
    (thrDigitPop P Cs algorithm den g pr d sgn c u v).length ≤ (thrMajorant P Cs carriers FP algorithm den e t J).M := by
  unfold thrDigitPop
  refine (length_digitPop_le (thrOccs P Cs) _ _ 1 (fun i => Nat.lt_succ_iff.mp (Nat.mod_lt _ (by norm_num)))).trans ?_
  rw [mul_one]
  exact le_refl _

/-- The auxiliary filter of `filt:soft` at a point. -/
def thrFaux (e' : GapSeed (thrAux P carriers FP e)) (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) : Bool :=
  filterBits (thrAux P carriers FP e) e' (thrZres P carriers pt.1.1 pt.2.1 pt.2.2)

/-- The digit populations of all rows at a point. -/
def thrPopsAt (k : ThrEq P Cs algorithm × PrimeIndex (thrCutoff P Cs algorithm den) × Fin (thrDigits P Cs algorithm den) × Bool)
    (pt : {c // P.IsCenter σ c} × (P.Errors × P.Errors)) : List Bool :=
  thrDigitPop P Cs algorithm den k.1 k.2.1 k.2.2.1 k.2.2.2 pt.1.1 pt.2.1 pt.2.2

/-- **The objective of the fixed hash is `hashObj`** at the seed number of the seed bits. -/
theorem objQ_eq_hashObj (s : Fin (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
      (thrMajorant P Cs carriers FP algorithm den e t J).ell0) → Bool) :
    objQ P σ Cs carriers FP algorithm den e t J s =
      hashObj (thrMajorant P Cs carriers FP algorithm den e t J) (thrFaux P σ carriers FP e)
        (thrPopsAt P σ Cs algorithm den) (bitsNum _ s) := by
  unfold objQ HQ auxQ hashObj thrFaux thrPopsAt
  rw [dataBits_eq]
  congr 1

/-- **The printed child sum of the call's hash fixing** (P3:2285-2290). -/
def thrHashSum (p : List Bool) : ℤ :=
  hashSum (thrMajorant P Cs carriers FP algorithm den e t J) (thrFaux P σ carriers FP e) (thrPopsAt P σ Cs algorithm den) p

/-- **The printed decisions are the fixed hash's bits** (P3:2327-2336): the loop over the call's printed child sums
outputs `thrHashBits`, the THR input of C5's contract. -/
theorem hashLoop_eq :
    greedyLoop (2 * (thrMajorant P Cs carriers FP algorithm den e t J).t *
      (thrMajorant P Cs carriers FP algorithm den e t J).ell0) (thrHashSum P σ Cs carriers FP algorithm den e t J) =
      List.ofFn (thrHashBits P σ Cs carriers FP algorithm den e t J) := by
  obtain ⟨c, hc⟩ := hashSum_scaled (thrMajorant P Cs carriers FP algorithm den e t J) (thrFaux P σ carriers FP e)
    (thrPopsAt P σ Cs algorithm den) (fun k pt => thrDigitPop_length P Cs carriers FP algorithm den e t J _ _ _ _ _ _ _)
  have hfun : (fun s => hashObj (thrMajorant P Cs carriers FP algorithm den e t J) (thrFaux P σ carriers FP e)
      (thrPopsAt P σ Cs algorithm den) (bitsNum _ s)) = objQ P σ Cs carriers FP algorithm den e t J :=
    funext fun s => (objQ_eq_hashObj P σ Cs carriers FP algorithm den e t J s).symm
  unfold thrHashSum
  rw [greedyLoop_eq_greedyQ _ _ _ c hc, hfun]
  rfl

end Thr

end NearCubicWires.WireExponent3_5.SeedFix
