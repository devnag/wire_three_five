import Proof.Wire_3_5.Selection.CosBnd2

/-! # C1.5 widths, part 3: the width `W = 8(L + n + 2)` suffices (P3:1188-1189, 1337-1360)

Paper: the star partition's parameters (`k = rs ≤ n`, P3:1188-1189) and the exact objective (P3:1337-1360). With
`W = 8(L + n + 2)`: every table fits in the rewind bound `8W²`, the output word too, and every exact accumulator word,
key product and row count fits in `W` bits (`D = 2^L`, `M = 2^L·L·2^(n+k)`, `D·(#pops+1)·M + D < 2^(4L+n+k+1) ≤ 2^W`).
Main declarations: `star_le`, `gateTable_le`, `popTable_le`, `outWord_le`, **`fits_W`**, **`keys_W`**. Paper
quantity: the arithmetic width of the selection. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)

/-- The star numbers are at most `n`. -/
theorem star_le (R : SelectionReq) (h : ParamsOk R) : R.r * R.s ≤ R.n ∧ R.s ≤ R.n ∧ (starParamsOf R h).b ≤ R.n ∧
    R.r ≤ R.n ∧ R.r * (starParamsOf R h).b ≤ R.n := by
  have h' := h
  obtain ⟨_, h2, h4⟩ := h'
  set P := starParamsOf R h with hP
  have h2s : 2 ^ R.s ≤ R.n / R.r + 1 := Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
  have hslt : R.s < 2 ^ R.s := Nat.lt_two_pow_self
  have hrq : R.r * (R.n / R.r) ≤ R.n := Nat.mul_div_le R.n R.r
  have hq : R.n / R.r ≤ R.n := Nat.div_le_self _ _
  have hbs : P.b + 1 = 2 ^ R.s := P.b_succ
  refine ⟨le_trans (Nat.mul_le_mul_left _ (by omega)) hrq, by omega, by omega, by omega, P.r_mul_b_le⟩

theorem Lof_ge (R : SelectionReq) : 3 ≤ Lof R := by
  have h := selWord_len R
  rw [natWord_len] at h
  have := natBitLength_pos R.n
  omega

theorem gates_le_L (R : SelectionReq) : R.gates.length ≤ Lof R := by
  have h1 := gInts_len_le R
  rw [gInts_length] at h1
  have : R.gates.length ≤ R.gates.length * (R.n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem pops_le_L (R : SelectionReq) : R.pops.length ≤ Lof R := by
  have h := pops_len_le R
  have : ∀ ps : List (List ℕ × ℚ), 3 * ps.length ≤ (ps.map fun X => X.1.length + 3).sum := by
    intro ps; induction ps with
    | nil => simp
    | cons X ps ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  have := this R.pops
  omega

/-- **The gate table fits the rewind bound.** -/
theorem gateTable_le (R : SelectionReq) : (gateTable (Wof R) R).length ≤ Bof R := by
  rw [gateTable_eq, List.length_flatMap]
  have e : ((gInts R).map fun z => (wRec (Wof R) z).length).sum = (gInts R).length * (2 * Wof R + 2) := by
    have : ∀ l : List ℤ, (l.map fun z => (wRec (Wof R) z).length).sum = l.length * (2 * Wof R + 2) := by
      intro l; induction l with
      | nil => simp
      | cons z l ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
        simp [wRec, frame_eq_frameP]; ring
    exact this _
  rw [e]
  have h1 := gInts_len_le R
  unfold Bof Wof
  nlinarith

/-- **The population table fits the rewind bound.** -/
theorem popTable_le (R : SelectionReq) : (popTable (Wof R) R).length ≤ Bof R := by
  have hpt : (popTable (Wof R) R).length = (R.pops.map fun X => (popRec (Wof R) X).length).sum := by
    simp [popTable, List.length_flatten, Function.comp_def]
  have hle : (R.pops.map fun X => (popRec (Wof R) X).length).sum ≤
      (R.pops.map fun X => X.1.length + 3).sum * (2 * Wof R + 2) := by
    rw [← List.sum_map_mul_right]
    apply List.sum_le_sum
    intro X _
    rw [popRec_length]
    nlinarith
  have h1 := pops_len_le R
  rw [hpt]
  refine le_trans hle ?_
  unfold Bof Wof at *
  nlinarith

theorem natBitLength_le_of_lt (c s : ℕ) (hc : c < 2 ^ s) : natBitLength c ≤ s + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · simp
  · have := Nat.log_lt_of_lt_pow (Nat.pos_iff_ne_zero.mp hpos) hc
    omega

/-- **The output word fits the rewind bound.** -/
theorem outWord_le (R : SelectionReq) (h : ParamsOk R) (N : ℕ) :
    (natListWord (codesOfIdx R.s R.r N)).length ≤ Bof R := by
  obtain ⟨hk, hs, _, hr, _⟩ := star_le R h
  have hcodes : ((codesOfIdx R.s R.r N).map fun c => (natWord c).length).sum ≤ R.r * (2 * R.s + 3) := by
    have : ∀ (r M : ℕ), ((codesOfIdx R.s r M).map fun c => (natWord c).length).sum ≤ r * (2 * R.s + 3) := by
      intro r
      induction r with
      | zero => intro M; simp [codesOfIdx]
      | succ r ih =>
        intro M
        simp only [codesOfIdx, List.map_cons, List.sum_cons]
        have h1 := ih (M % 2 ^ (R.s * r))
        have h2 := natBitLength_le_of_lt (M / 2 ^ (R.s * r) % 2 ^ R.s) R.s (Nat.mod_lt _ (Nat.two_pow_pos _))
        rw [natWord_len]
        nlinarith
    exact this R.r N
  have e : (natListWord (codesOfIdx R.s R.r N)).length =
      (natWord R.r).length + ((codesOfIdx R.s R.r N).map fun c => (natWord c).length).sum := by
    simp [natListWord, codesOfIdx_length, List.length_flatMap, Function.comp_def]
  rw [e, natWord_len]
  have h3 := natBitLength_le R.r
  have hrs : R.r * (2 * R.s + 3) ≤ 2 * R.n + 3 * R.n := by nlinarith
  unfold Bof Wof
  nlinarith

/-! ## The fits in `W` bits -/

theorem pow_facts (L : ℕ) : L + 1 ≤ 2 ^ L := Nat.lt_two_pow_self

/-- The key product bound. -/
theorem big_lt (R : SelectionReq) (h : ParamsOk R) :
    2 ^ Lof R * ((R.pops.length + 1) * (2 ^ Lof R * (Lof R * 2 ^ (R.n + R.r * R.s)))) + 2 ^ Lof R < 2 ^ Wof R ∧
    2 ^ Lof R * (R.pops.length * (2 ^ Lof R * (Lof R * 2 ^ (R.n + R.r * R.s)))) * 2 ^ Lof R < 2 ^ Wof R := by
  obtain ⟨hk, _, _, _, _⟩ := star_le R h
  set L := Lof R
  have hP : R.pops.length + 1 ≤ 2 ^ L := le_trans (by have := pops_le_L R; omega) (pow_facts L)
  have hL : L ≤ 2 ^ L := by have := pow_facts L; omega
  have hE : 2 ^ (R.n + R.r * R.s) ≤ 2 ^ (2 * R.n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hA : 2 ^ L * ((R.pops.length + 1) * (2 ^ L * (L * 2 ^ (R.n + R.r * R.s)))) ≤
      2 ^ L * (2 ^ L * (2 ^ L * (2 ^ L * 2 ^ (2 * R.n)))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hP (Nat.mul_le_mul_left _ (Nat.mul_le_mul hL hE)))
  have hB' : 2 ^ L * (2 ^ L * (2 ^ L * (2 ^ L * 2 ^ (2 * R.n)))) = 2 ^ (4 * L + 2 * R.n) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  have hW : 4 * L + 2 * R.n + 1 ≤ Wof R := by unfold Wof; omega
  have hC : 2 ^ (4 * L + 2 * R.n) + 2 ^ (4 * L + 2 * R.n) ≤ 2 ^ Wof R := by
    rw [← two_mul, ← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hW
  have hL' : 2 ^ L < 2 ^ (4 * L + 2 * R.n) := Nat.pow_lt_pow_right (by norm_num) (by have := Lof_ge R; omega)
  refine ⟨by omega, ?_⟩
  have hA2 : 2 ^ L * (R.pops.length * (2 ^ L * (L * 2 ^ (R.n + R.r * R.s)))) * 2 ^ L ≤
      2 ^ L * ((R.pops.length + 1) * (2 ^ L * (L * 2 ^ (R.n + R.r * R.s)))) * 2 ^ L :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
  have hA3 : 2 ^ L * ((R.pops.length + 1) * (2 ^ L * (L * 2 ^ (R.n + R.r * R.s)))) * 2 ^ L ≤
      2 ^ (4 * L + 2 * R.n) * 2 ^ L := Nat.mul_le_mul_right _ (hB' ▸ hA)
  have hA4 : 2 ^ (4 * L + 2 * R.n) * 2 ^ L ≤ 2 ^ (5 * L + 2 * R.n) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hW5 : 5 * L + 2 * R.n < Wof R := by unfold Wof; omega
  have := Nat.pow_lt_pow_right (show 1 < 2 by norm_num) hW5
  omega

/-- **Every weighted step fits** at `W`. -/
theorem fits_W (R : SelectionReq) (h : ParamsOk R) (N cap : ℕ)
    (hC : ∀ X ∈ R.pops, X.1.length ≤ cap) : PopsFit R h N (Wof R) cap (0, 1) R.pops := by
  obtain ⟨hk, _, _, _, _⟩ := star_le R h
  have hLW : Lof R ≤ Wof R := by unfold Wof; omega
  have hEW : 2 ^ (Lof R + (R.n + R.r * R.s)) < 2 ^ Wof R :=
    Nat.pow_lt_pow_right (by norm_num) (by unfold Wof; omega)
  have hM : ∀ X ∈ R.pops, X.2.num.toNat * popT R h N X ≤ 2 ^ Lof R * (Lof R * 2 ^ (R.n + R.r * R.s)) := by
    intro X hX
    obtain ⟨_, hn, _, hl⟩ := pop_bits R X hX
    have h1 : X.2.num.toNat ≤ 2 ^ Lof R := by
      have := lt_pow_natBitLength X.2.num.natAbs
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
      omega
    have h2 : popT R h N X ≤ Lof R * 2 ^ (R.n + R.r * R.s) :=
      le_trans (popT_le R h N X) (Nat.mul_le_mul_right _ hl)
    exact Nat.mul_le_mul h1 h2
  refine popsFit_all R h N (Wof R) cap _ (2 ^ Lof R) hM (dens_prod_le R) (big_lt R h).1 ?_ ?_ hC
  · intro X hX
    obtain ⟨_, _, _, hl⟩ := pop_bits R X hX
    have h2 : popT R h N X ≤ Lof R * 2 ^ (R.n + R.r * R.s) :=
      le_trans (popT_le R h N X) (Nat.mul_le_mul_right _ hl)
    have h3 : Lof R * 2 ^ (R.n + R.r * R.s) ≤ 2 ^ (Lof R + (R.n + R.r * R.s)) := by
      rw [show 2 ^ (Lof R + (R.n + R.r * R.s)) = 2 ^ Lof R * 2 ^ (R.n + R.r * R.s) from pow_add _ _ _]
      exact Nat.mul_le_mul_right _ (show Lof R ≤ 2 ^ Lof R by have := pow_facts (Lof R); omega)
    omega
  · intro X hX i hi
    have := (pop_bits R X hX).1 i hi
    have h1 := lt_pow_natBitLength i
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (le_trans this hLW)
    omega

/-- **The keys fit** at `W`. -/
theorem keys_W (R : SelectionReq) (h : ParamsOk R) :
    (∀ N < 2 ^ (R.r * R.s), ∀ M < 2 ^ (R.r * R.s),
      (keyAt R h N).1 * (keyAt R h M).2 < 2 ^ Wof R ∧ (keyAt R h M).1 * (keyAt R h N).2 < 2 ^ Wof R) ∧
    (∀ N < 2 ^ (R.r * R.s), (keyAt R h N).2 < 2 ^ Wof R) := by
  have hM : ∀ N, ∀ X ∈ R.pops, X.2.num.toNat * popT R h N X ≤ 2 ^ Lof R * (Lof R * 2 ^ (R.n + R.r * R.s)) := by
    intro N X hX
    obtain ⟨_, hn, _, hl⟩ := pop_bits R X hX
    have h1 : X.2.num.toNat ≤ 2 ^ Lof R := by
      have := lt_pow_natBitLength X.2.num.natAbs
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn
      omega
    exact Nat.mul_le_mul h1 (le_trans (popT_le R h N X) (Nat.mul_le_mul_right _ hl))
  have hb := (big_lt R h).2
  have hLW : 2 ^ Lof R < 2 ^ Wof R := Nat.pow_lt_pow_right (by norm_num) (by unfold Wof; omega)
  have kb : ∀ N, (keyAt R h N).2 ≤ 2 ^ Lof R ∧
      (keyAt R h N).1 ≤ 2 ^ Lof R * (R.pops.length * (2 ^ Lof R * (Lof R * 2 ^ (R.n + R.r * R.s)))) := fun N => by
    obtain ⟨_, a, b⟩ := key_bounds R h N _ (2 ^ Lof R) (hM N) (dens_prod_le R)
    exact ⟨a, b⟩
  refine ⟨fun N _ M _ => ⟨?_, ?_⟩, fun N _ => lt_of_le_of_lt (kb N).1 hLW⟩
  · exact lt_of_le_of_lt (Nat.mul_le_mul (kb N).2 (kb M).1) hb
  · exact lt_of_le_of_lt (Nat.mul_le_mul (kb M).2 (kb N).1) hb

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
