import Proof.Wire_3_5.Selection.CosPost

/-! # C1.5 widths, part 1: the request word's length bounds its numbers (P3:1326-1330)

Paper: "polynomially many bottom gates, each gate given by a polynomial-bit integer threshold description [...] rational
weights `p_X` [...] with polynomial-bit descriptions" (P3:1326-1330). Every number of the request is a field of the
request word `selWord R`, so its bit length is at most the word's length `L = Lof R`. Consequences: each gate meets
`KeyBound` at the key width `V = L` (`|θ| + Σ|wᵢ| < 2^L`), the gate records and the populations fit in `L`, and the
populations' index and weight bit lengths are at most `L`. Main declarations: `selWord_len`, `sum_lt_pow`,
**`keyBound_L`**, `gInts_bits`, `gInts_len_le`, `pops_len_le`, `pop_bits`. Paper quantity: the request's description
size. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Machine.S0Stub
open NearCubicWires.WireExponent3_5.SelectionMachine NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.UnionMachine.Plan (selWord)
open NearCubicWires.RepairRepresentation (natWord intWord natListWord)
open NearCubicWires.WireExponent3_5 (ratWord)

theorem natWord_len (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := PrimAsm.ParseNat.natWord_length v

theorem intWord_len (z : ℤ) : (intWord z).length = 2 * natBitLength z.natAbs + 2 := by
  simp [intWord, natWord_len]

theorem popWord_len (X : List ℕ × ℚ) : (natListWord X.1 ++ ratWord X.2).length =
    2 * natBitLength X.1.length + 1 + (X.1.map fun i => 2 * natBitLength i + 1).sum +
      (2 * natBitLength X.2.num.natAbs + 2 + (2 * natBitLength X.2.den + 1)) := by
  rw [List.length_append, natListWord, ratWord, List.length_append, List.length_append, intWord_len, natWord_len,
    natWord_len, List.length_flatMap]
  simp only [natWord_len]

/-- **The request word's length**, field by field. -/
theorem selWord_len (R : SelectionReq) : Lof R = (natWord R.n).length + (natWord R.r).length +
    (natWord R.gates.length).length + ((gInts R).map fun z => (intWord z).length).sum +
      (natWord R.pops.length).length + (R.pops.map fun X => (natListWord X.1 ++ ratWord X.2).length).sum := by
  unfold Lof
  rw [selWord_eq, tailG]
  simp only [List.length_append, List.length_flatMap]
  ring

theorem natBitLength_pos (v : ℕ) : 1 ≤ natBitLength v := by unfold natBitLength; omega

theorem lt_pow_natBitLength (v : ℕ) : v < 2 ^ natBitLength v := Nat.lt_pow_succ_log_self (by norm_num) v

/-- A list's sum is below `2` to the sum of its bit lengths. -/
theorem sum_lt_pow : ∀ l : List ℕ, l.sum + 1 ≤ 2 ^ (l.map natBitLength).sum
  | [] => by simp
  | a :: l => by
    have ih := sum_lt_pow l
    have ha := lt_pow_natBitLength a
    have h1 := Nat.one_le_two_pow (n := (l.map natBitLength).sum)
    have h2 := Nat.one_le_two_pow (n := natBitLength a)
    simp only [List.sum_cons, List.map_cons, pow_add]
    nlinarith

theorem sum_map_le_of_mem {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : α), a ∈ l → f a ≤ (l.map f).sum
  | [], _, h => absurd h (by simp)
  | b :: l, a, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | e
    · subst e; omega
    · have := sum_map_le_of_mem f l a e; omega

/-- The numbers of one gate. -/
def gNums {n : ℕ} (g : IntGate n) : List ℤ := List.ofFn g.weights ++ [g.threshold]

theorem gInts_eq (R : SelectionReq) : gInts R = R.gates.flatMap gNums := rfl

theorem sum_flatMap_ge {α β : Type} (f : β → ℕ) (F : α → List β) :
    ∀ (l : List α) (a : α), a ∈ l → ((F a).map f).sum ≤ ((l.flatMap F).map f).sum
  | [], _, h => absurd h (by simp)
  | b :: l, a, h => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append]
    rcases List.mem_cons.mp h with e | e
    · subst e; omega
    · have := sum_flatMap_ge f F l a e; omega

theorem gInts_len_sum (R : SelectionReq) :
    ((gInts R).map fun z => (intWord z).length).sum ≤ Lof R := by
  rw [selWord_len]; omega

/-- **Each gate meets `KeyBound` at the key width `L`.** -/
theorem keyBound_L (R : SelectionReq) (g : IntGate R.n) (hg : g ∈ R.gates) : KeyBound (gateOf g) (Lof R) := by
  unfold KeyBound
  have hs := sum_lt_pow ((gNums g).map Int.natAbs)
  have hsum : (gateOf g).threshold.natAbs + ∑ i, ((gateOf g).weight i).natAbs = ((gNums g).map Int.natAbs).sum := by
    simp [gNums, gateOf, List.sum_ofFn, add_comm]
  have hbits : (((gNums g).map Int.natAbs).map natBitLength).sum ≤ Lof R := by
    have h1 := sum_flatMap_ge (fun z : ℤ => (intWord z).length) gNums R.gates g hg
    have h2 := gInts_len_sum R
    rw [← gInts_eq] at h1
    have h3 : (((gNums g).map Int.natAbs).map natBitLength).sum ≤ ((gNums g).map fun z => (intWord z).length).sum := by
      simp only [List.map_map]
      apply List.sum_le_sum
      intro z _
      show natBitLength z.natAbs ≤ (intWord z).length
      rw [intWord_len]; omega
    omega
  rw [hsum]
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hbits
  omega

/-- Every gate number's bit length is at most `L`. -/
theorem gInts_bits (R : SelectionReq) (z : ℤ) (hz : z ∈ gInts R) : natBitLength z.natAbs ≤ Lof R := by
  have h1 := sum_map_le_of_mem (fun z : ℤ => (intWord z).length) (gInts R) z hz
  have h2 := gInts_len_sum R
  have h1' : 2 * natBitLength z.natAbs + 2 ≤ ((gInts R).map fun z => (intWord z).length).sum := by
    rw [← intWord_len]; exact h1
  omega

/-- The gate numbers are at most `L/4`. -/
theorem gInts_len_le (R : SelectionReq) : 4 * (gInts R).length ≤ Lof R := by
  have h2 := gInts_len_sum R
  have : ∀ l : List ℤ, 4 * l.length ≤ (l.map fun z => (intWord z).length).sum := by
    intro l
    induction l with
    | nil => simp
    | cons z l ih =>
      rw [List.length_cons, List.map_cons, List.sum_cons, intWord_len]
      have := natBitLength_pos z.natAbs
      omega
  have := this (gInts R)
  omega

theorem pops_len_sum (R : SelectionReq) :
    (R.pops.map fun X => (natListWord X.1 ++ ratWord X.2).length).sum ≤ Lof R := by
  rw [selWord_len]; omega

/-- The populations with their indices are at most `L`: `Σ_X (|X| + 3) ≤ L`. -/
theorem pops_len_le (R : SelectionReq) : (R.pops.map fun X => X.1.length + 3).sum ≤ Lof R := by
  have h := pops_len_sum R
  have : ∀ ps : List (List ℕ × ℚ), (ps.map fun X => X.1.length + 3).sum ≤
      (ps.map fun X => (natListWord X.1 ++ ratWord X.2).length).sum := by
    intro ps
    apply List.sum_le_sum
    intro X _
    rw [popWord_len]
    have h1 : X.1.length ≤ (X.1.map fun i => 2 * natBitLength i + 1).sum := by
      have : ∀ l : List ℕ, l.length ≤ (l.map fun i => 2 * natBitLength i + 1).sum := by
        intro l; induction l with
        | nil => simp
        | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
      exact this X.1
    omega
  exact le_trans (this R.pops) h

/-- A population's field is at most `L`. -/
theorem pop_len_le (R : SelectionReq) (X : List ℕ × ℚ) (hX : X ∈ R.pops) :
    (natListWord X.1 ++ ratWord X.2).length ≤ Lof R :=
  le_trans (sum_map_le_of_mem (fun X : List ℕ × ℚ => (natListWord X.1 ++ ratWord X.2).length) R.pops X hX)
    (pops_len_sum R)

/-- A population's index and weight bit lengths are at most `L`. -/
theorem pop_bits (R : SelectionReq) (X : List ℕ × ℚ) (hX : X ∈ R.pops) :
    (∀ i ∈ X.1, natBitLength i ≤ Lof R) ∧ natBitLength X.2.num.natAbs ≤ Lof R ∧ natBitLength X.2.den ≤ Lof R ∧
      X.1.length ≤ Lof R := by
  have h := pop_len_le R X hX
  rw [popWord_len] at h
  refine ⟨fun i hi => ?_, by omega, by omega, ?_⟩
  · have := sum_map_le_of_mem (fun i => 2 * natBitLength i + 1) X.1 i hi
    omega
  · have : ∀ l : List ℕ, l.length ≤ (l.map fun i => 2 * natBitLength i + 1).sum := by
      intro l; induction l with
      | nil => simp
      | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
    have := this X.1
    omega

/-- The `n` and `r` fields are at most `L`. -/
theorem nr_bits (R : SelectionReq) : natBitLength R.n ≤ Lof R ∧ natBitLength R.r ≤ Lof R ∧
    natBitLength R.gates.length ≤ Lof R ∧ natBitLength R.pops.length ≤ Lof R := by
  have h := selWord_len R
  simp only [natWord_len] at h
  omega

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
