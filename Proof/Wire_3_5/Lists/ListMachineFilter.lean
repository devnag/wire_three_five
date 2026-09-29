import Proof.Wire_3_5.Lists.ListMachineRows

/-! # C2g computable refs: the regular filter as one explicit `𝔽₂` polynomial (P3:2063-2104, 2385-2412)

Realizes the expansion of the regular filter `F_e(Z)` of `filt:gap` (P3:2016-2104) that every row carries as one more
Boolean factor: "This fixed Boolean function has an exact `𝔽₂` polynomial of degree at most `128` in the parity bits,
and hence of constant degree in `Z`" (P3:2079-2081), and after the walk amplification "Majority multiplies the Boolean
degree by at most `t`" (P3:2100-2101); "A regular filter is one more Boolean polynomial of degree `O_D(L)`"
(P3:1528-1530).

The construction follows the seed's `gapFilterWith` (the bit-level filter) exactly, generically in the
field operations: each copy's selected parity `P = Σ_i H_i a_i Z_i` is a linear polynomial (`parityPoly`); a symmetric
Boolean function `f(#{true bits})` of `N` polynomial bits is the explicit polynomial `Σ_{k ≤ N} c_k·e_k`, with the
elementary symmetric polynomials `e_k = binom(S, k) mod 2` built by Pascal's rule and the `𝔽₂` binomial inversion
`c_k = ⊕_{i≤k} binom(k,i) f(i)` (`symPolyRef`, `symPolyRef_eval`); the base filter is "at most `32` of `128`"
(`baseFilterPoly`), and the regular filter the majority over the `t` visited base seeds (`gapFilterPoly`).

Main results: **`gapFilterPoly_eval`** (the printed polynomial is `gapFilterWith P o kEq e Z` on EVERY input, for any
field operations `o`, in particular the seed's `GF.bitOps` at `GF.firstPrimitive`, which `Checks/GapFilterBits` shows
equal to the seed's `gapFilter`), and **`gapFilterPoly_size`** (degree `≤ 128·t`, coordinates `< L`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.SupplierWalk NearCubicWires.SupplierToeplitzCore

/-! ## Pascal's rule at the Boolean level -/

/-- The number of true bits among some polynomials at an assignment. -/
def trueCount (ls : List Poly) (ρ : ℕ → Bool) : ℕ := (ls.filter fun ℓ => F2Poly.eval ℓ ρ).length

theorem binomRefN_eval (ls : List Poly) (a : ℤ) (t : ℕ) (ρ : ℕ → Bool) :
    bitF2 (F2Poly.eval (binomRefN ls a t) ρ) = ((Ring.choose (a + trueCount ls ρ) t : ℤ) : ZMod 2) := by
  induction ls generalizing t with
  | nil => simp [binomRefN, trueCount, bitF2_chooseMod2]
  | cons ℓ ls ih =>
    cases t with
    | zero => simp [binomRefN, bitF2]
    | succ t =>
      simp only [binomRefN, eval_nadd, eval_nmul, bitF2_xor, bitF2_and, ih, trueCount, List.filter_cons]
      cases hℓ : F2Poly.eval ℓ ρ
      · simp [bitF2]
      · simp only [↓reduceIte, List.length_cons, bitF2]
        have hstep : a + (((ls.filter fun ℓ => F2Poly.eval ℓ ρ).length + 1 : ℕ) : ℤ) =
            (a + (((ls.filter fun ℓ => F2Poly.eval ℓ ρ).length : ℕ) : ℤ)) + 1 := by push_cast; ring
        rw [hstep, Ring.choose_succ_succ]
        push_cast
        ring

/-! ## Symmetric Boolean functions: the `𝔽₂` binomial inversion -/

/-- `binom(k, i)` is odd. -/
def chooseOdd (k i : ℕ) : Bool := k.choose i % 2 == 1

theorem bitF2_chooseOdd (k i : ℕ) : bitF2 (chooseOdd k i) = ((k.choose i : ℕ) : ZMod 2) := bitF2_nat_mod _

/-- The coefficient `c_k = ⊕_{i≤k} binom(k,i) f(i)` of `e_k` in the symmetric function `f`. -/
def symCoeff (f : ℕ → Bool) (k : ℕ) : Bool := (List.range (k + 1)).foldr (fun i b => xor (chooseOdd k i && f i) b) false

theorem bitF2_symCoeff (f : ℕ → Bool) (k : ℕ) :
    bitF2 (symCoeff f k) = ∑ i ∈ range (k + 1), ((k.choose i : ℕ) : ZMod 2) * bitF2 (f i) := by
  unfold symCoeff
  rw [← sum_range_list]
  generalize List.range (k + 1) = l
  induction l with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, bitF2_xor, bitF2_and, bitF2_chooseOdd, ih, List.map_cons, List.sum_cons]

theorem sum_choose_mul (N n i : ℕ) (hn : n ≤ N) :
    ∑ k ∈ range (N + 1), k.choose i * n.choose k = n.choose i * 2 ^ (n - i) := by
  rcases Nat.lt_or_ge n i with hni | hin
  · rw [Nat.choose_eq_zero_of_lt hni, zero_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases Nat.lt_or_ge k i with hk | hk
    · rw [Nat.choose_eq_zero_of_lt hk, zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (show n < k by omega), mul_zero]
  · rw [← Finset.sum_range_add_sum_Ico _ (show i ≤ N + 1 by omega)]
    rw [Finset.sum_eq_zero (s := range i) (fun k hk => by
      rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hk), zero_mul]), zero_add, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ j, (i + j).choose i * n.choose (i + j) = n.choose i * (n - i).choose j := by
      intro j
      rcases Nat.lt_or_ge n (i + j) with hlt | hle
      · rw [Nat.choose_eq_zero_of_lt hlt, mul_zero, Nat.choose_eq_zero_of_lt (show n - i < j by omega), mul_zero]
      · rw [mul_comm, Nat.choose_mul (n := n) (Nat.le_add_right i j), Nat.add_sub_cancel_left]
    simp_rw [hterm, ← Finset.mul_sum]
    congr 1
    rw [← Nat.sum_range_choose (n - i), ← Finset.sum_range_add_sum_Ico _ (show n - i + 1 ≤ N + 1 - i by omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (n - i + 1) (N + 1 - i)) (fun j hj => by
      rw [Nat.choose_eq_zero_of_lt (by have := (Finset.mem_Ico.mp hj).1; omega)]), add_zero]

theorem sum_choose_mul_mod_two (N n i : ℕ) (hn : n ≤ N) :
    ∑ k ∈ range (N + 1), ((k.choose i : ℕ) : ZMod 2) * ((n.choose k : ℕ) : ZMod 2) = if i = n then 1 else 0 := by
  have h := congrArg (fun x : ℕ => (x : ZMod 2)) (sum_choose_mul N n i hn)
  simp only [Nat.cast_sum, Nat.cast_mul] at h
  rw [h]
  rcases Nat.lt_trichotomy i n with hlt | heq | hgt
  · rw [if_neg (by omega), show n - i = (n - i - 1) + 1 by omega, pow_succ]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, mul_zero, mul_zero]
  · subst heq; simp
  · rw [Nat.choose_eq_zero_of_lt hgt, if_neg (by omega)]; simp

/-- **The `𝔽₂` binomial inversion**: `f(n) = Σ_{k≤N} c_k binom(n,k)` in `𝔽₂` for every `n ≤ N`. -/
theorem symInversion (f : ℕ → Bool) (N n : ℕ) (hn : n ≤ N) :
    bitF2 (f n) = ∑ k ∈ range (N + 1), bitF2 (symCoeff f k) * ((n.choose k : ℕ) : ZMod 2) := by
  have hwiden : ∀ k ∈ range (N + 1), bitF2 (symCoeff f k) =
      ∑ i ∈ range (N + 1), ((k.choose i : ℕ) : ZMod 2) * bitF2 (f i) := by
    intro k hk
    rw [bitF2_symCoeff, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ N + 1 by have := Finset.mem_range.mp hk; omega)]
    rw [Finset.sum_eq_zero (s := Finset.Ico (k + 1) (N + 1)) (fun i hi => by
      rw [Nat.choose_eq_zero_of_lt (by have := (Finset.mem_Ico.mp hi).1; omega)]; simp), add_zero]
  rw [Finset.sum_congr rfl fun k hk => by rw [hwiden k hk]]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((k.choose i : ℕ) : ZMod 2) * bitF2 (f i) * ((n.choose k : ℕ) : ZMod 2) =
      bitF2 (f i) * (if i = n then 1 else 0) := by
    intro i _
    rw [← sum_choose_mul_mod_two N n i hn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl this]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (range (N + 1)) n, if_pos (Finset.mem_range.mpr (by omega))]

theorem bitF2_inj {a b : Bool} (h : bitF2 a = bitF2 b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- **A symmetric Boolean function of `N` polynomial bits**, `f(#{true bits})`, as the explicit polynomial
`Σ_{k ≤ N} c_k·e_k` (reduced). -/
def symPolyRef (f : ℕ → Bool) (N : ℕ) (bs : List Poly) : Poly :=
  nsum ((List.range (N + 1)).map fun k => if symCoeff f k then binomRefN bs 0 k else pzero)

theorem symPolyRef_eval (f : ℕ → Bool) (N : ℕ) (bs : List Poly) (ρ : ℕ → Bool) (hN : trueCount bs ρ ≤ N) :
    F2Poly.eval (symPolyRef f N bs) ρ = f (trueCount bs ρ) := by
  have h := symInversion f N (trueCount bs ρ) hN
  have hb : bitF2 (F2Poly.eval (symPolyRef f N bs) ρ) = bitF2 (f (trueCount bs ρ)) := by
    rw [h]
    unfold symPolyRef
    rw [eval_nsum, eval_psum, ← sum_range_list]
    generalize List.range (N + 1) = l
    induction l with
    | nil => rfl
    | cons k l ih =>
      rw [List.map_cons, List.foldr_cons, bitF2_xor, ih, List.map_cons, List.sum_cons]
      congr 1
      split_ifs with hc
      · rw [binomRefN_eval, zero_add, hc]
        simp [bitF2, Ring.choose_natCast]
      · simp only [Bool.not_eq_true] at hc
        rw [eval_pzero, hc]; simp [bitF2]
  exact bitF2_inj hb

theorem binomRefN_size' (ls : List Poly) (L δ : ℕ) (hd : ∀ ℓ ∈ ls, DegLe ℓ δ) (ha : ∀ ℓ ∈ ls, AtomsLt ℓ L)
    (a : ℤ) (t : ℕ) : DegLe (binomRefN ls a t) (δ * t) ∧ AtomsLt (binomRefN ls a t) L := by
  induction ls generalizing t with
  | nil => exact ⟨degLe_pconst _ _, atomsLt_pconst _ _⟩
  | cons ℓ ls ih =>
    have hd' : ∀ ℓ' ∈ ls, DegLe ℓ' δ := fun ℓ' h => hd ℓ' (List.mem_cons_of_mem _ h)
    have ha' : ∀ ℓ' ∈ ls, AtomsLt ℓ' L := fun ℓ' h => ha ℓ' (List.mem_cons_of_mem _ h)
    cases t with
    | zero => exact ⟨degLe_pone _, atomsLt_pone L⟩
    | succ t =>
      have hm := degLe_pmul (hd ℓ (List.mem_cons_self ..)) (ih hd' ha' t).1
      refine ⟨degLe_normalize (degLe_padd (ih hd' ha' (t + 1)).1 (degLe_normalize (hm.mono (by rw [Nat.mul_succ]; omega)))),
        atomsLt_normalize (atomsLt_padd (ih hd' ha' (t + 1)).2
          (atomsLt_normalize (atomsLt_pmul (ha ℓ (List.mem_cons_self ..)) (ih hd' ha' t).2)))⟩

theorem symPolyRef_size (f : ℕ → Bool) (N L δ : ℕ) (bs : List Poly) (hd : ∀ b ∈ bs, DegLe b δ)
    (ha : ∀ b ∈ bs, AtomsLt b L) : DegLe (symPolyRef f N bs) (δ * N) ∧ AtomsLt (symPolyRef f N bs) L := by
  unfold symPolyRef nsum
  refine ⟨degLe_normalize (degLe_psum ?_), atomsLt_normalize (atomsLt_psum ?_)⟩ <;> intro q hq <;>
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq <;> split_ifs
  · exact ((binomRefN_size' bs L δ hd ha 0 k).1).mono (Nat.mul_le_mul_left δ (by have := List.mem_range.mp hk; omega))
  · exact degLe_pzero _
  · exact (binomRefN_size' bs L δ hd ha 0 k).2
  · exact atomsLt_pzero L

/-! ## The filter's pieces -/

section Filter

end Filter

end NearCubicWires.WireExponent3_5.ListMachine
