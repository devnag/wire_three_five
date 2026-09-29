import Proof.Wire_3_5.Selection.MathPlan

/-! # C1.1 R1: the argmin order of `selectCodes` is the coset counter's (P3:1359-1360)

Paper: "There are `2^k` candidate cosets, so the total is bounded as claimed. Select a minimum objective"
(P3:1359-1360); the reference `selectCodes` keeps the FIRST minimizer over `allCodes s r`, so the machine's order and
tie rule must be exactly these. Proves **`r1Fold : R1Fold`**: `allCodes s r` is the list of the `s`-bit digit
expansions (`codesOfIdx`) of the counter values `0, …, 2^(sr) − 1` (`allCodes_eq_map_range`), so `argminFold` over it
from `replicate r 0` is the counter's strict-`<` running minimum `argminIdx` under any key with the same strict order.
Paper quantity: the selected coset (`selectCodes`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Math.Order
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

/-- `range (a·b)` is `a` consecutive blocks of `range b`. -/
theorem range_mul_eq (a b : ℕ) :
    List.range (a * b) = (List.range a).flatMap fun i => (List.range b).map (i * b + ·) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, List.range_add, ih, List.range_succ, List.flatMap_append]
    simp

/-- The counter value `a·2^(sr) + m` has leading code `a` and the codes of `m` after it. -/
theorem codesOfIdx_succ_block (s r a m : ℕ) (ha : a < 2 ^ s) (hm : m < 2 ^ (s * r)) :
    codesOfIdx s (r + 1) (a * 2 ^ (s * r) + m) = a :: codesOfIdx s r m := by
  have hp : 0 < 2 ^ (s * r) := Nat.two_pow_pos _
  simp only [codesOfIdx]
  have h1 : (a * 2 ^ (s * r) + m) / 2 ^ (s * r) = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hm, Nat.zero_add]
  have h2 : (a * 2 ^ (s * r) + m) % 2 ^ (s * r) = m := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm]
  rw [h1, h2, Nat.mod_eq_of_lt ha]

/-- **`allCodes` is the counter order**: the code lists are the digit expansions of `0, …, 2^(sr) − 1`, the first
code most significant. -/
theorem allCodes_eq_map_range (s : ℕ) :
    ∀ r : ℕ, StarParams.allCodes s r = (List.range (2 ^ (s * r))).map (codesOfIdx s r)
  | 0 => by simp [StarParams.allCodes, codesOfIdx]
  | r + 1 => by
    have hpow : 2 ^ (s * (r + 1)) = 2 ^ s * 2 ^ (s * r) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [StarParams.allCodes, allCodes_eq_map_range s r, hpow, range_mul_eq, List.map_flatMap]
    apply List.flatMap_congr
    intro a ha
    rw [List.mem_range] at ha
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro m hm
    rw [List.mem_range] at hm
    exact (codesOfIdx_succ_block s r a m ha hm).symm

/-- The zero counter value is the all-zero coset. -/
theorem codesOfIdx_zero (s : ℕ) : ∀ r : ℕ, codesOfIdx s r 0 = List.replicate r 0
  | 0 => rfl
  | r + 1 => by simp [codesOfIdx, codesOfIdx_zero s r, List.replicate_succ]

/-- Folding the first-minimizer update over a mapped list is mapping the counter's update, when the keys order the
values as `f` does. -/
theorem foldl_map_argmin (f : List ℕ → ℚ) (φ : ℕ → List ℕ) {κ : Type} (lt : κ → κ → Bool) (key : ℕ → κ) (M : ℕ)
    (hkey : ∀ N, N < M → ∀ N', N' < M → (f (φ N) < f (φ N') ↔ lt (key N) (key N') = true)) :
    ∀ (xs : List ℕ) (b : ℕ), b < M → (∀ x ∈ xs, x < M) →
      (xs.map φ).foldl (fun best l => if f l < f best then l else best) (φ b) =
        φ (xs.foldl (fun best N => if lt (key N) (key best) then N else best) b)
  | [], _, _, _ => rfl
  | x :: xs, b, hb, hxs => by
    have hx : x < M := hxs x List.mem_cons_self
    have hstep : (if f (φ x) < f (φ b) then φ x else φ b) =
        φ (if lt (key x) (key b) then x else b) := by
      by_cases h : lt (key x) (key b) = true
      · rw [if_pos ((hkey x hx b hb).mpr h), if_pos h]
      · rw [if_neg (fun h' => h ((hkey x hx b hb).mp h')), if_neg h]
    simp only [List.map_cons, List.foldl_cons]
    rw [hstep]
    apply foldl_map_argmin f φ lt key M hkey xs
    · split_ifs <;> assumption
    · exact fun y hy => hxs y (List.mem_cons_of_mem _ hy)

/-- **R1**: the first minimizer over `allCodes s r` is the counter's running minimum. -/
theorem r1Fold : R1Fold := by
  intro s r f κ lt key hkey
  rw [allCodes_eq_map_range, ← codesOfIdx_zero s r]
  unfold StarParams.argminFold argminIdx
  exact foldl_map_argmin f (codesOfIdx s r) lt key (2 ^ (s * r)) hkey _ 0 (Nat.two_pow_pos _)
    (fun x hx => List.mem_range.mp hx)

end NearCubicWires.WireExponent3_5.SelectionMachine.Math.Order
