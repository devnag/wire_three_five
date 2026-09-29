import Proof.Wire_3_5.Selection.GateEnum

/-! # C1.4 math: each written point from the counters' bits (P3:1339-1344)

Paper: "For each gate and row, the four threshold predicates have integer scores of the form `a_j(z_L) + b_j(z_R)`
[...] This uses the original integer representation, not an assertion that the predicates are thresholds of the
center bits" (P3:1341-1344). The machine computes a left point `(a, a')` of `(u, z_L)` from the counters' bits: `a` is
the weighted sum of the half's bits in machine order (`halfL`), `a'` the same sum after flipping, in each block, the
bit the error code names (`flipL`), and the point is written only when every block's syndrome (the exclusive-or of
the positions `i + 1` of its set bits, `synBit`) equals the block's code, read from the coset counter's segment
(`okL`); else the null point. Proves **`ptLz_decode`**: `ptLz P σ g (decU u, decX x)` is that point, for the coset
`σ = translationOfCodes (codesOfIdx s r N)`. Paper quantity: a left point `(a_j(z_L))_j`. -/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars Finset
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

variable (P : StarParams)

/-- A weight read at any coordinate (`0` outside the input). -/
def wAt {n : ℕ} (g : NormalizedThresholdGate n) (c : ℕ) : ℤ := if h : c < n then g.weight ⟨c, h⟩ else 0

/-- The left half score from the counter's bits. -/
def halfL {n : ℕ} (g : NormalizedThresholdGate n) (x : ℕ) : ℤ :=
  ((List.range (lw P)).map fun p => wAt g (coordL P p) * if x.testBit p then 1 else 0).sum

/-- Whether position `p` is the bit the error code of its block flips. -/
def flipL (u p : ℕ) : Bool := decide (p < hh P * P.b ∧ errCode P u (hh P - 1 - p / P.b) = p % P.b + 1)

/-- The left half score at the flipped corner. -/
def halfL' {n : ℕ} (g : NormalizedThresholdGate n) (x u : ℕ) : ℤ :=
  ((List.range (lw P)).map fun p => wAt g (coordL P p) * if xor (x.testBit p) (flipL P u p) then 1 else 0).sum

/-- Bit `k` of the syndrome of machine block `t` of `x`: the parity of the set bits `i` with bit `k` of `i + 1`. -/
def synBit (x t k : ℕ) : Bool :=
  ((List.range P.b).map fun i => x.testBit (t * P.b + i) && (i + 1).testBit k).foldl xor false

/-- **The left coset test**: every machine block's syndrome is the code in the coset counter's segment `h + t`. -/
def okL (N x : ℕ) : Prop := ∀ t < hh P, ∀ k < P.s, synBit P x t k = N.testBit (P.s * (hh P + t) + k)

instance (N x : ℕ) : Decidable (okL P N x) := by unfold okL; infer_instance

/-! ## Sums over a half -/

theorem listsum_range (f : ℕ → ℤ) : ∀ n : ℕ, ((List.range n).map f).sum = ∑ p ∈ Finset.range n, f p
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, listsum_range f n, Finset.sum_range_succ]; simp

/-- A sum over the left half is a sum over the machine positions. -/
theorem sumL (F : P.SideL → ℤ) :
    ∑ i, F i = ∑ p ∈ Finset.range (lw P), if hp : p < lw P then F ⟨⟨coordL P p, coordL_lt P p hp⟩, coordL_side P p hp⟩
      else 0 := by
  refine Finset.sum_bij' (fun i _ => posL P i.1.val)
    (fun p hp => ⟨⟨coordL P p, coordL_lt P p (Finset.mem_range.mp hp)⟩, coordL_side P p (Finset.mem_range.mp hp)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_range.mpr (posL_lt P i.1 i.2)
  · intro p _; exact Finset.mem_univ _
  · intro i _; apply Subtype.ext; apply Fin.ext; exact coordL_posL P i.1 i.2
  · intro p hp; exact posL_coordL P p (Finset.mem_range.mp hp)
  · intro i _
    rw [dif_pos (posL_lt P i.1 i.2)]
    congr 1; apply Subtype.ext; apply Fin.ext; exact (coordL_posL P i.1 i.2).symm

theorem halfScoreL_eq {g : NormalizedThresholdGate P.n} (f : P.SideL → Bool) (x : ℕ)
    (hf : ∀ p (hp : p < lw P), f ⟨⟨coordL P p, coordL_lt P p hp⟩, coordL_side P p hp⟩ = x.testBit p) :
    P.halfScoreL g f = halfL P g x := by
  unfold StarParams.halfScoreL halfL
  rw [sumL, listsum_range]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  rw [dif_pos hp', hf p hp']
  unfold wAt
  rw [dif_pos (coordL_lt P p hp')]

/-- **The left half score** of a counter value. -/
theorem halfScoreL_decX (g : NormalizedThresholdGate P.n) (x : ℕ) : P.halfScoreL g (decX P x) = halfL P g x :=
  halfScoreL_eq P _ x fun p hp => by simp only [decX, posL_coordL P p hp]

/-! ## The flipped corner -/

theorem blockCoord_left (j : Fin (P.r / 2)) (i : Fin P.b) : (P.blockCoord (P.leftBlock j) i).val = j.val * P.b + i.val :=
  rfl

theorem errorVector_coordL (u p : ℕ) (hp : p < lw P) :
    P.errorVector P.leftBlock (decU P u) ⟨coordL P p, coordL_lt P p hp⟩ = flipL P u p := by
  have hb := P.b_pos
  have h2 := hb_le_rb P
  unfold StarParams.errorVector flipL
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j, i, hji, hc⟩
    have hc' : j.val * P.b + i.val = coordL P p := by rw [← blockCoord_left]; exact congrArg Fin.val hc
    have hjb : j.val * P.b + i.val < hh P * P.b := blk_lt j.val (hh P) i.val P.b j.isLt i.isLt
    by_cases h : p < hh P * P.b
    · unfold coordL at hc'
      rw [if_pos h] at hc'
      obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
      rw [hq, hmm] at hc' ⊢
      have hqh : q < hh P := by
        by_contra hc2
        have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨d1, d2⟩ := divmod j.val i.val P.b i.isLt
      obtain ⟨d3, d4⟩ := divmod (hh P - 1 - q) m P.b hm
      have ej : j.val = hh P - 1 - q := by rw [← d1, ← d3, hc']
      have ei : i.val = m := by rw [← d2, ← d4, hc']
      refine ⟨h, ?_⟩
      unfold decU at hji
      rw [← ej]
      by_cases h0 : errCode P u j.val = 0
      · rw [dif_pos h0] at hji; exact absurd hji (by simp)
      · rw [dif_neg h0] at hji
        have := congrArg (fun o => o.map Fin.val) hji
        simp only [Option.map_some, Option.some.injEq] at this
        omega
    · unfold coordL at hc'
      rw [if_neg h] at hc'
      omega
  · rintro ⟨h, hcode⟩
    have hqh : p / P.b < hh P := (Nat.div_lt_iff_lt_mul hb).mpr h
    have hm := Nat.mod_lt p hb
    have hpos : 0 < hh P := Nat.lt_of_le_of_lt (Nat.zero_le _) hqh
    refine ⟨⟨hh P - 1 - p / P.b, show hh P - 1 - p / P.b < hh P from
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hpos Nat.one_pos)⟩, ⟨p % P.b, hm⟩, ?_, ?_⟩
    · unfold decU
      rw [dif_neg (by rw [hcode]; exact Nat.succ_ne_zero _)]
      congr 1
      apply Fin.ext
      simp only
      rw [hcode, Nat.add_sub_cancel]
    · apply Fin.ext
      rw [blockCoord_left]
      show (hh P - 1 - p / P.b) * P.b + p % P.b = coordL P p
      unfold coordL
      rw [if_pos h]

/-- **The flipped corner's left half score** of counter values. -/
theorem halfScoreL_flip (g : NormalizedThresholdGate P.n) (x u : ℕ) :
    P.halfScoreL g (StarParams.xorHalf (decX P x) (P.leftPart (P.errorVector P.leftBlock (decU P u)))) =
      halfL' P g x u := by
  unfold halfL'
  have := halfScoreL_eq P (g := g) (StarParams.xorHalf (decX P x) (P.leftPart (P.errorVector P.leftBlock (decU P u))))
  unfold StarParams.halfScoreL at this ⊢
  rw [sumL, listsum_range]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  rw [dif_pos hp']
  unfold wAt
  rw [dif_pos (coordL_lt P p hp')]
  congr 1
  simp only [StarParams.xorHalf, StarParams.leftPart, decX, posL_coordL P p hp']
  rw [errorVector_coordL P u p hp']

/-! ## The coset test -/

theorem codes_testBit (s : ℕ) : ∀ (r N j k : ℕ), j < r → k < s →
    ((codesOfIdx s r N).getD j 0).testBit k = N.testBit (s * (r - 1 - j) + k)
  | 0, _, _, _, hj, _ => absurd hj (by omega)
  | r + 1, N, 0, k, _, hk => by
    simp only [codesOfIdx, List.getD_cons_zero, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp [hk, Nat.add_comm]
  | r + 1, N, j + 1, k, hj, hk => by
    simp only [codesOfIdx, List.getD_cons_succ]
    rw [codes_testBit s r (N % 2 ^ (s * r)) j k (by omega) hk, Nat.testBit_mod_two_pow]
    have e : r + 1 - 1 - (j + 1) = r - 1 - j := by omega
    rw [e]
    have hlt : s * (r - 1 - j) + k < s * r := by
      have : s * (r - 1 - j) + s ≤ s * r := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    simp [hlt]

/-- The parity of a list of bits, as an element of `Fin 2`. -/
theorem sum_fin2 (c : ℕ → Bool) : ∀ m : ℕ,
    (∑ i ∈ Finset.range m, (if c i then (1 : Fin 2) else 0)) =
      if ((List.range m).map c).foldl xor false then 1 else 0
  | 0 => rfl
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_fin2 c m, List.range_succ, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have key : ∀ a b : Bool, ((if a = true then (1 : Fin 2) else 0) + if b = true then 1 else 0) =
        if (xor a b) = true then 1 else 0 := by decide
    exact key _ _

theorem syndrome_bit (y : Fin P.b → Bool) (k : Fin P.s) :
    P.syndrome y k = if ((List.range P.b).map fun i =>
      (if h : i < P.b then y ⟨i, h⟩ else false) && (i + 1).testBit k.val).foldl xor false then 1 else 0 := by
  unfold StarParams.syndrome
  rw [Finset.sum_apply]
  have e : ∀ i : Fin P.b, (if y i then P.column i else 0) k =
      (fun j => if (if h : j < P.b then y ⟨j, h⟩ else false) && (j + 1).testBit k.val then (1 : Fin 2) else 0) i.val := by
    intro i
    simp only [dif_pos i.isLt]
    by_cases hy : y i
    · simp only [hy, if_true, Bool.true_and]
      unfold StarParams.column
      apply Fin.ext
      rw [finFunctionFinEquiv_symm_apply_val, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one ((i.val + 1) / 2 ^ k.val) with h0 | h0 <;> simp [h0]
    · simp [hy]
  rw [Finset.sum_congr rfl (fun i _ => e i), Fin.sum_univ_eq_sum_range
    (fun j => if (if h : j < P.b then y ⟨j, h⟩ else false) && (j + 1).testBit k.val then (1 : Fin 2) else 0) P.b]
  exact sum_fin2 _ P.b

theorem div_two_pow_mod (z k : ℕ) : z / 2 ^ k % 2 = if z.testBit k then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ k) with h | h <;> simp [h]

theorem code_bit (N : ℕ) (j : Fin P.r) (k : Fin P.s) :
    (P.translationOfCodes (codesOfIdx P.s P.r N)) j k = if N.testBit (P.s * (P.r - 1 - j.val) + k.val) then 1 else 0 := by
  unfold StarParams.translationOfCodes
  apply Fin.ext
  rw [finFunctionFinEquiv_symm_apply_val, div_two_pow_mod, Nat.testBit_mod_two_pow,
    codes_testBit P.s P.r N j.val k.val j.isLt k.isLt]
  have hk : k.val < P.s := k.isLt
  simp only [hk, decide_true, Bool.true_and]
  split_ifs <;> rfl

theorem posL_block (j i : ℕ) (hj : j < hh P) (hi : i < P.b) : posL P (j * P.b + i) = (hh P - 1 - j) * P.b + i := by
  obtain ⟨d1, d2⟩ := divmod j i P.b hi
  unfold posL
  rw [if_pos (blk_lt j (hh P) i P.b hj hi), d1, d2]

theorem ite_fin2 (a b : Bool) : ((if a then (1 : Fin 2) else 0) = if b then 1 else 0) ↔ a = b := by
  cases a <;> cases b <;> decide

theorem leftOK_decX (N x : ℕ) :
    P.LeftOK (P.translationOfCodes (codesOfIdx P.s P.r N)) (decX P x) ↔ okL P N x := by
  have hr := hh_two P
  unfold StarParams.LeftOK okL
  constructor
  · intro h t ht k hk
    have hj : hh P - 1 - t < P.r / 2 := by show hh P - 1 - t < hh P; omega
    have h1 := congrFun (h ⟨hh P - 1 - t, hj⟩) ⟨k, hk⟩
    rw [syndrome_bit, code_bit] at h1
    rw [ite_fin2] at h1
    have e1 : P.r - 1 - (P.leftBlock ⟨hh P - 1 - t, hj⟩).val = hh P + t := by
      show P.r - 1 - (hh P - 1 - t) = hh P + t; omega
    rw [e1] at h1
    rw [← h1]
    unfold synBit
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [dif_pos hi']
    congr 1
    show x.testBit (t * P.b + i) = x.testBit (posL P ((hh P - 1 - t) * P.b + i))
    rw [posL_block P _ i (by omega) hi', show hh P - 1 - (hh P - 1 - t) = t by omega]
  · intro h j
    funext k
    rw [syndrome_bit, code_bit, ite_fin2]
    have hjh : j.val < hh P := j.isLt
    have e1 : P.r - 1 - (P.leftBlock j).val = hh P + (hh P - 1 - j.val) := by
      show P.r - 1 - j.val = _; omega
    rw [e1, ← h (hh P - 1 - j.val) (by omega) k.val k.isLt]
    unfold synBit
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [dif_pos hi']
    congr 1
    show x.testBit (posL P (j.val * P.b + i)) = x.testBit ((hh P - 1 - j.val) * P.b + i)
    rw [posL_block P _ i hjh hi']

/-- **The written left point**: the machine's point of `(u, x)` at the coset `N`. -/
theorem ptLz_decode (g : NormalizedThresholdGate P.n) (N u x : ℕ) :
    ptLz P (P.translationOfCodes (codesOfIdx P.s P.r N)) g (decU P u, decX P x) =
      if okL P N x then (halfL P g x, halfL' P g x u) else (0, 0) := by
  unfold ptLz ptL
  simp only
  rw [if_congr (leftOK_decX P N x) rfl rfl, halfScoreL_decX, halfScoreL_flip]

/-! ## The right side -/

/-- The right half score from the counter's bits. -/
def halfR {n : ℕ} (g : NormalizedThresholdGate n) (y : ℕ) : ℤ :=
  ((List.range (rw P)).map fun p => wAt g (coordR P p) * if y.testBit p then 1 else 0).sum

/-- The right half score at the flipped corner (the same flip rule as the left: block `h − 1 − p/b`'s code). -/
def halfR' {n : ℕ} (g : NormalizedThresholdGate n) (y v : ℕ) : ℤ :=
  ((List.range (rw P)).map fun p => wAt g (coordR P p) * if xor (y.testBit p) (flipL P v p) then 1 else 0).sum

/-- **The right coset test**: every machine block's syndrome is the code in the coset counter's segment `t`. -/
def okR (N y : ℕ) : Prop := ∀ t < hh P, ∀ k < P.s, synBit P y t k = N.testBit (P.s * t + k)

instance (N y : ℕ) : Decidable (okR P N y) := by unfold okR; infer_instance

theorem sumR (F : P.SideR → ℤ) :
    ∑ i, F i = ∑ p ∈ Finset.range (rw P), if hp : p < rw P then F ⟨⟨coordR P p, coordR_lt P p hp⟩, coordR_side P p hp⟩
      else 0 := by
  refine Finset.sum_bij' (fun i _ => posR P i.1.val)
    (fun p hp => ⟨⟨coordR P p, coordR_lt P p (Finset.mem_range.mp hp)⟩, coordR_side P p (Finset.mem_range.mp hp)⟩)
    ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_range.mpr (posR_lt P i.1 i.2)
  · intro p _; exact Finset.mem_univ _
  · intro i _; apply Subtype.ext; apply Fin.ext; exact coordR_posR P i.1 i.2
  · intro p hp; exact posR_coordR P p (Finset.mem_range.mp hp)
  · intro i _
    rw [dif_pos (posR_lt P i.1 i.2)]
    congr 1; apply Subtype.ext; apply Fin.ext; exact (coordR_posR P i.1 i.2).symm

theorem halfScoreR_eq {g : NormalizedThresholdGate P.n} (f : P.SideR → Bool) (y : ℕ)
    (hf : ∀ p (hp : p < rw P), f ⟨⟨coordR P p, coordR_lt P p hp⟩, coordR_side P p hp⟩ = y.testBit p) :
    P.halfScoreR g f = halfR P g y := by
  unfold StarParams.halfScoreR halfR
  rw [sumR, listsum_range]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  rw [dif_pos hp', hf p hp']
  unfold wAt
  rw [dif_pos (coordR_lt P p hp')]

theorem halfScoreR_decY (g : NormalizedThresholdGate P.n) (y : ℕ) : P.halfScoreR g (decY P y) = halfR P g y :=
  halfScoreR_eq P _ y fun p hp => by simp only [decY, posR_coordR P p hp]

theorem blockCoord_right (j : Fin (P.r / 2)) (i : Fin P.b) :
    (P.blockCoord (P.rightBlock j) i).val = (hh P + j.val) * P.b + i.val := rfl

theorem errorVector_coordR (v p : ℕ) (hp : p < rw P) :
    P.errorVector P.rightBlock (decU P v) ⟨coordR P p, coordR_lt P p hp⟩ = flipL P v p := by
  have hb := P.b_pos
  have h2 := hb_le_rb P
  have hr := hh_two P
  unfold StarParams.errorVector flipL
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨j, i, hji, hc⟩
    have hc' : (hh P + j.val) * P.b + i.val = coordR P p := by rw [← blockCoord_right]; exact congrArg Fin.val hc
    by_cases h : p < hh P * P.b
    · unfold coordR at hc'
      rw [if_pos h] at hc'
      obtain ⟨q, m, rfl, hm, hq, hmm⟩ := split_pos p P.b hb
      rw [hq, hmm] at hc' ⊢
      have hqh : q < hh P := by
        by_contra hc2
        have : hh P * P.b ≤ q * P.b := Nat.mul_le_mul_right _ (by omega)
        omega
      obtain ⟨d1, d2⟩ := divmod (hh P + j.val) i.val P.b i.isLt
      obtain ⟨d3, d4⟩ := divmod (hh P + (hh P - 1 - q)) m P.b hm
      have ej : hh P + j.val = hh P + (hh P - 1 - q) := by rw [← d1, ← d3, hc']
      have ei : i.val = m := by rw [← d2, ← d4, hc']
      have ej' : j.val = hh P - 1 - q := by omega
      refine ⟨h, ?_⟩
      unfold decU at hji
      rw [← ej']
      by_cases h0 : errCode P v j.val = 0
      · rw [dif_pos h0] at hji; exact absurd hji (by simp)
      · rw [dif_neg h0] at hji
        have := congrArg (fun o => o.map Fin.val) hji
        simp only [Option.map_some, Option.some.injEq] at this
        omega
    · unfold coordR at hc'
      rw [if_neg h] at hc'
      have hjb : (hh P + j.val) * P.b + i.val < P.r * P.b := by
        have := blk_lt (hh P + j.val) P.r i.val P.b (by have := j.isLt; show hh P + j.val < P.r; omega) i.isLt
        exact this
      omega
  · rintro ⟨h, hcode⟩
    have hqh : p / P.b < hh P := (Nat.div_lt_iff_lt_mul hb).mpr h
    have hm := Nat.mod_lt p hb
    have hpos : 0 < hh P := Nat.lt_of_le_of_lt (Nat.zero_le _) hqh
    refine ⟨⟨hh P - 1 - p / P.b, show hh P - 1 - p / P.b < hh P from
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hpos Nat.one_pos)⟩, ⟨p % P.b, hm⟩, ?_, ?_⟩
    · unfold decU
      rw [dif_neg (by rw [hcode]; exact Nat.succ_ne_zero _)]
      congr 1
      apply Fin.ext
      simp only
      rw [hcode, Nat.add_sub_cancel]
    · apply Fin.ext
      rw [blockCoord_right]
      show (hh P + (hh P - 1 - p / P.b)) * P.b + p % P.b = coordR P p
      unfold coordR
      rw [if_pos h]

theorem halfScoreR_flip (g : NormalizedThresholdGate P.n) (y v : ℕ) :
    P.halfScoreR g (StarParams.xorHalf (decY P y) (P.rightPart (P.errorVector P.rightBlock (decU P v)))) =
      halfR' P g y v := by
  unfold halfR'
  unfold StarParams.halfScoreR
  rw [sumR, listsum_range]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.mem_range.mp hp
  rw [dif_pos hp']
  unfold wAt
  rw [dif_pos (coordR_lt P p hp')]
  congr 1
  simp only [StarParams.xorHalf, StarParams.rightPart, decY, posR_coordR P p hp']
  rw [errorVector_coordR P v p hp']

theorem posR_block (j i : ℕ) (hj : j < hh P) (hi : i < P.b) :
    posR P ((hh P + j) * P.b + i) = (hh P - 1 - j) * P.b + i := by
  have hr := hh_two P
  obtain ⟨d1, d2⟩ := divmod (hh P + j) i P.b hi
  unfold posR
  rw [if_pos (blk_lt (hh P + j) P.r i P.b (by omega) hi), d1, d2]
  congr 2
  omega

theorem rightOK_decY (N y : ℕ) :
    P.RightOK (P.translationOfCodes (codesOfIdx P.s P.r N)) (decY P y) ↔ okR P N y := by
  have hr := hh_two P
  unfold StarParams.RightOK okR
  constructor
  · intro h t ht k hk
    have hj : hh P - 1 - t < P.r / 2 := by show hh P - 1 - t < hh P; omega
    have h1 := congrFun (h ⟨hh P - 1 - t, hj⟩) ⟨k, hk⟩
    rw [syndrome_bit, code_bit, ite_fin2] at h1
    have e1 : P.r - 1 - (P.rightBlock ⟨hh P - 1 - t, hj⟩).val = t := by
      show P.r - 1 - (P.r / 2 + (hh P - 1 - t)) = t; show P.r - 1 - (hh P + (hh P - 1 - t)) = t; omega
    rw [e1] at h1
    rw [← h1]
    unfold synBit
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [dif_pos hi']
    congr 1
    show y.testBit (t * P.b + i) = y.testBit (posR P ((hh P + (hh P - 1 - t)) * P.b + i))
    rw [posR_block P _ i (by omega) hi', show hh P - 1 - (hh P - 1 - t) = t by omega]
  · intro h j
    funext k
    rw [syndrome_bit, code_bit, ite_fin2]
    have hjh : j.val < hh P := j.isLt
    have e1 : P.r - 1 - (P.rightBlock j).val = hh P - 1 - j.val := by
      show P.r - 1 - (P.r / 2 + j.val) = _; show P.r - 1 - (hh P + j.val) = _; omega
    rw [e1, ← h (hh P - 1 - j.val) (by omega) k.val k.isLt]
    unfold synBit
    congr 1
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    rw [dif_pos hi']
    congr 1
    show y.testBit (posR P ((hh P + j.val) * P.b + i)) = y.testBit ((hh P - 1 - j.val) * P.b + i)
    rw [posR_block P _ i hjh hi']

/-- **The written right point**: the machine's point of `(v, y)` at the coset `N`. -/
theorem ptRz_decode (g : NormalizedThresholdGate P.n) (N v y : ℕ) :
    ptRz P (P.translationOfCodes (codesOfIdx P.s P.r N)) g (decU P v, decY P y) =
      if okR P N y then (halfR P g y, halfR' P g y v) else (0, 0) := by
  unfold ptRz ptR
  simp only
  rw [if_congr (rightOK_decY P N y) rfl rfl, halfScoreR_decY, halfScoreR_flip]

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
