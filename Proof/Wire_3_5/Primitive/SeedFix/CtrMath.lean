import Proof.Wire_3_5.Primitive.SeedFix.C4GeoV
import Proof.Wire_3_5.Primitive.Writers.GeoColsV

/-! # X3, part 1: a center's bits, position by position (P3:1202-1216)

"Use all `2^s` cosets in each block" (P3:1206-1207) and "A fixed linear basis of each code gives polynomial-time
encoding" (P3:1216): the center at table position `(row, col)` is, in every block, the Hamming codeword of the block's
data bits (the row's bits on the left half, the column's on the right) XOR the coset offset, and on the unblocked
coordinates the row's (left) or column's (right) remaining bits XOR the offset (`C4GeoV.centerAt_bit`, `ctrBit`).
The center writer emits the codeword bit by bit: at a parity position `2^t − 1` the parity `parB t` (the XOR of the
data bits whose position `+1` has bit `t`), at a data position the next data bit. Here:

* `nd`, `npar` (data / parity positions before `q`), `dpos_nd`, **`enc_data`**, **`enc_par`**, `npar_pow`;
* the trackers' arithmetic: `PowT` (the next power of two, `powT_par`: `q` is a parity position iff the distance is
  `0`), `BitT` (bit `t` of a counter, `bitT_step`);
* `packB` (parity bits packed little-endian in one register);
* **`cw_left`**, **`cw_right`**, **`cw_unbL`**, **`cw_unbR`**: bit `x` of `List.ofFn (centerAt P σ row col)` in each
  region of the coordinates.

Paper quantity of the main types: the center `C4Geo.centerAt P σ row col` (a cell center of the partition `σ`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo

section Code
variable (P : StarParams)

/-- The data positions before `q`. -/
def nd (q : ℕ) : ℕ := ((List.range q).filter (fun i => !isPar P i)).length

/-- The parity positions before `q`. -/
def npar (q : ℕ) : ℕ := ((List.range q).filter (fun i => isPar P i)).length

theorem nd_succ (q : ℕ) : nd P (q + 1) = nd P q + (if isPar P q then 0 else 1) := by
  unfold nd
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : isPar P q <;> simp [h]

theorem npar_succ (q : ℕ) : npar P (q + 1) = npar P q + (if isPar P q then 1 else 0) := by
  unfold npar
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : isPar P q <;> simp [h]

theorem nd_mono {q q' : ℕ} (h : q ≤ q') : nd P q ≤ nd P q' := by
  induction q' with
  | zero =>
    have : q = 0 := by omega
    subst this
    exact le_rfl
  | succ q' ih =>
    rcases Nat.lt_or_ge q (q' + 1) with h1 | h1
    · have := ih (by omega)
      rw [nd_succ]
      split_ifs <;> omega
    · have : q = q' + 1 := by omega
      subst this
      exact le_rfl

theorem nd_b : nd P P.b = dB P := by
  rw [← PrimAsm.GeoColsV.dataPos_length P]
  rfl

theorem npar_pow (t : ℕ) (ht : t ≤ P.s) : npar P (2 ^ t - 1) = t := by
  unfold npar isPar
  exact PrimAsm.GeoColsV.parCount P.s t ht

theorem npar_b : npar P P.b = P.s := npar_pow P P.s le_rfl

theorem dpos_nd (q : ℕ) (hq : q < P.b) (hd : isPar P q = false) : dpos P (nd P q) = q := by
  obtain ⟨k, hk⟩ : ∃ k, P.b = q + 1 + k := ⟨P.b - q - 1, by omega⟩
  unfold dpos dataPos nd
  rw [hk, List.range_add, List.range_succ, List.filter_append, List.filter_append]
  have hq1 : [q].filter (fun i => !isPar P i) = [q] := by simp [hd]
  rw [hq1, List.append_assoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

theorem dpos_data (m : ℕ) (hm : m < dB P) : isPar P (dpos P m) = false := by
  have hl : m < (dataPos P).length := by rw [PrimAsm.GeoColsV.dataPos_length]; exact hm
  have hmem : dpos P m ∈ dataPos P := by
    unfold dpos
    rw [List.getD_eq_getElem _ _ hl]
    exact List.getElem_mem hl
  unfold dataPos at hmem
  rw [List.mem_filter] at hmem
  simpa using hmem.2

theorem isPar_pow (t : ℕ) (ht : t < P.s) : isPar P (2 ^ t - 1) = true := by
  have h1 := Nat.one_le_two_pow (n := t)
  unfold isPar
  rw [List.any_eq_true]
  refine ⟨t, List.mem_range.2 ht, ?_⟩
  simp only [beq_iff_eq]
  omega

/-- **The parity bit `t`** of a block's data bits: the XOR of the data bits whose position `+1` has bit `t`. -/
def parB (zb : ℕ → Bool) (t : ℕ) : Bool := xr (fun m => zb m && (dpos P m + 1).testBit t) (dB P)

/-- **At the parity position `2^t − 1` the codeword bit is the parity `parB t`.** -/
theorem enc_par (zb : ℕ → Bool) (t : ℕ) (ht : t < P.s) : encB P zb (2 ^ t - 1) = parB P zb t := by
  unfold encB parB
  apply xr_congr
  intro m hm
  have h1 := Nat.one_le_two_pow (n := t)
  have hne : 2 ^ t - 1 ≠ dpos P m := by
    intro e
    have a := dpos_data P m hm
    rw [← e, isPar_pow P t ht] at a
    exact absurd a (by decide)
  rw [PrimAsm.GeoColsV.cwBit_par P (dpos P m) (2 ^ t - 1) t (by omega) ht hne]

/-- **At a data position the codeword bit is the next data bit.** -/
theorem enc_data (zb : ℕ → Bool) (q : ℕ) (hq : q < P.b) (hd : isPar P q = false) :
    encB P zb q = zb (nd P q) := by
  have hlt : nd P q < dB P := by
    have h1 := nd_mono P (show q + 1 ≤ P.b by omega)
    rw [nd_succ, if_neg (by simp [hd]), nd_b] at h1
    omega
  have h := encB_data P zb (nd P q) hlt
  rwa [dpos_nd P q hq hd] at h

/-! ## The next power of two -/

/-- The power tracker at position `q`: the next power of two `np ≥ q + 1` (`np < 2(q+1)`) and the distance `e`. -/
def PowT (q np e : ℕ) : Prop := ∃ u, np = 2 ^ u ∧ e + q + 1 = np ∧ np < 2 * (q + 1)

theorem powT_zero : PowT 0 1 0 := ⟨0, rfl, rfl, by norm_num⟩

/-- **`q` is a parity position iff the distance to the next power of two is `0`.** -/
theorem powT_par {q np e : ℕ} (hq : q < P.b) (h : PowT q np e) : isPar P q = true ↔ e = 0 := by
  obtain ⟨u, hu, he, hlt⟩ := h
  rw [PrimAsm.GeoColsV.isPar_iff P q hq]
  constructor
  · rintro ⟨t, ht⟩
    have h1 : 2 ^ t ≤ 2 ^ u := by omega
    have h2 : 2 ^ u < 2 ^ (t + 1) := by rw [pow_succ]; omega
    have a1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have a2 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
    have : u = t := by omega
    subst this
    omega
  · intro h0
    exact ⟨u, by omega⟩

theorem powT_step0 {q np e : ℕ} (h : PowT q np e) (he : e = 0) : PowT (q + 1) (2 * np) (np - 1) := by
  obtain ⟨u, hu, he', hlt⟩ := h
  refine ⟨u + 1, by rw [pow_succ, ← hu]; ring, ?_, ?_⟩ <;> omega

theorem powT_stepS {q np e : ℕ} (h : PowT q np e) (he : e ≠ 0) : PowT (q + 1) np (e - 1) := by
  obtain ⟨u, hu, he', hlt⟩ := h
  exact ⟨u, hu, by omega, by omega⟩

theorem powT_le {q np e : ℕ} (h : PowT q np e) : np ≤ 2 * (q + 1) ∧ e ≤ np := by
  obtain ⟨u, hu, he', hlt⟩ := h
  omega

end Code

/-! ## Bit `t` of a counter -/

/-- The bit tracker of bit `t` at the counter value `v`: the flag is the bit, `c` the distance to the next flip. -/
def BitT (t v c f : ℕ) : Prop := f = (v.testBit t).toNat ∧ c + v % 2 ^ t = 2 ^ t

theorem bitT_zero (t : ℕ) : BitT t 0 (2 ^ t) 0 := ⟨by simp, by simp⟩

theorem bitT_pos {t v c f : ℕ} (h : BitT t v c f) : 1 ≤ c ∧ c ≤ 2 ^ t ∧ f ≤ 1 := by
  have h1 := Nat.mod_lt v (Nat.two_pow_pos t)
  have h2 := Bool.toNat_le (v.testBit t)
  obtain ⟨hf, hc⟩ := h
  omega

theorem bitT_flip {t v c f : ℕ} (h : BitT t v c f) (hc : c = 1) : BitT t (v + 1) (2 ^ t) (1 - f) := by
  obtain ⟨hf, hcv⟩ := h
  have hpos := Nat.two_pow_pos t
  have hd := Nat.mod_add_div v (2 ^ t)
  have e : v + 1 = 2 ^ t * (v / 2 ^ t + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  refine ⟨?_, ?_⟩
  · rw [hf, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, e,
      Nat.mul_div_cancel_left _ hpos]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ t) with h0 | h0
    · have : (v / 2 ^ t + 1) % 2 = 1 := by omega
      simp [h0, this]
    · have : (v / 2 ^ t + 1) % 2 = 0 := by omega
      simp [h0, this]
  · rw [e, Nat.mul_mod_right, Nat.add_zero]

theorem bitT_keep {t v c f : ℕ} (h : BitT t v c f) (hc : c ≠ 1) : BitT t (v + 1) (c - 1) f := by
  obtain ⟨hf, hcv⟩ := h
  have hpos := Nat.two_pow_pos t
  have hd := Nat.mod_add_div v (2 ^ t)
  have hm := Nat.mod_lt v hpos
  have hlt : v % 2 ^ t + 1 < 2 ^ t := by omega
  have e : v + 1 = (v % 2 ^ t + 1) + 2 ^ t * (v / 2 ^ t) := by omega
  have ediv : (v + 1) / 2 ^ t = v / 2 ^ t := by
    rw [e, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
  have emod : (v + 1) % 2 ^ t = v % 2 ^ t + 1 := by
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_⟩
  · rw [hf, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, ediv]
  · rw [emod]
    omega

/-! ## Packed parity bits -/

/-- A bit list packed little-endian in one number. -/
def packB : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * packB l

theorem packB_append (l : List Bool) (b : Bool) : packB (l ++ [b]) = packB l + b.toNat * 2 ^ l.length := by
  induction l with
  | nil => simp [packB]
  | cons a l ih =>
    simp only [List.cons_append, packB, ih, List.length_cons, pow_succ]
    ring

theorem packB_lt : ∀ l : List Bool, packB l < 2 ^ l.length
  | [] => by simp [packB]
  | b :: l => by
    have := packB_lt l
    have := Bool.toNat_le b
    simp only [packB, List.length_cons, pow_succ]
    omega

theorem packB_mod (b : Bool) (l : List Bool) : packB (b :: l) % 2 = b.toNat := by
  have := Bool.toNat_le b
  simp only [packB]
  omega

theorem packB_div (b : Bool) (l : List Bool) : packB (b :: l) / 2 = packB l := by
  have := Bool.toNat_le b
  simp only [packB]
  omega

/-! ## A center's bits by region -/

section Center
variable (P : StarParams) (σ : P.Translation)

theorem cw_getD (row col x : ℕ) (hx : x < P.n) :
    (List.ofFn (centerAt P σ row col)).getD x false =
      xor (ctrBit P row col x) ((List.ofFn (offset P σ)).getD x false) := by
  have h1 := ofFn_getD (centerAt P σ row col) ⟨x, hx⟩
  have h2 := ofFn_getD (offset P σ) ⟨x, hx⟩
  simp only at h1 h2
  rw [h1, h2, centerAt_bit]

theorem blk_lt (jj q : ℕ) (hj : jj < P.r / 2) (hq : q < P.b) : jj * P.b + q < P.r / 2 * P.b := by
  have : (jj + 1) * P.b ≤ P.r / 2 * P.b := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem dm_blk (jj q : ℕ) (hq : q < P.b) : (jj * P.b + q) / P.b = jj ∧ (jj * P.b + q) % P.b = q := by
  have hb : 0 < P.b := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hq, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]

/-- **Left blocks**: the codeword of the row's data bits of block `jj`. -/
theorem cw_left (row col jj q : ℕ) (hj : jj < P.r / 2) (hq : q < P.b) :
    ctrBit P row col (jj * P.b + q) = encB P (fun m => row.testBit (jj * dB P + m)) q := by
  have hlt := blk_lt P jj q hj hq
  obtain ⟨e1, e2⟩ := dm_blk P jj q hq
  unfold ctrBit
  rw [if_pos hlt, e1, e2]

/-- **Right blocks**: the codeword of the column's data bits of block `jj`. -/
theorem cw_right (row col jj q : ℕ) (hj : jj < P.r / 2) (hq : q < P.b) :
    ctrBit P row col (P.r / 2 * P.b + (jj * P.b + q)) = encB P (fun m => col.testBit (jj * dB P + m)) q := by
  have hlt := blk_lt P jj q hj hq
  have hrb := rb_eq P
  obtain ⟨e1, e2⟩ := dm_blk P jj q hq
  unfold ctrBit
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, e1, e2]

/-- **Unblocked, left**: the row's remaining bits. -/
theorem cw_unbL (row col i : ℕ) (hi : i < hL P) :
    ctrBit P row col (P.r * P.b + i) = row.testBit (P.r / 2 * dB P + i) := by
  have hrb := rb_eq P
  unfold ctrBit
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

/-- **Unblocked, right**: the column's remaining bits. -/
theorem cw_unbR (row col i : ℕ) :
    ctrBit P row col (P.r * P.b + hL P + i) = col.testBit (P.r / 2 * dB P + i) := by
  have hrb := rb_eq P
  unfold ctrBit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 2
  omega

end Center

end NearCubicWires.WireExponent3_5.PrimT.Ctr
