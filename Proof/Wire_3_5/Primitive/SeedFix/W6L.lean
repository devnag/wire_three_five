import Proof.Wire_3_5.Primitive.SeedFix.W6K

/-! # W6, part 12: the prime rows (port `17`), their count and their sum

P3:2551-2553 (row:prime: the primes `p ≤ cutoff`, listed increasingly: `Joins.primesList`), P3:2618-2620 (`Σ_{p ≤ cut} p`,
`ThrQ.primeSum`): the listing loop runs the candidates `x = 2 … cut` (`pBody`, `W6K`), so after `k` rounds stream `sPr`
holds `Data.unaryList (primesList (k+1))`, `r58` the count and `r59` the sum:
* `primesList_succ`, `unaryList_succ`, `primesList_length`/`primesList_sum` (against `primesUpTo`, `primeSum`);
* **`primes_exec`**: from `r56 = cut` (scratch `20 … 34`, `r58`, `r59`, `r74` at `0`, `sPr` blank) to `sPr` =
  `Data.unaryList (primesList cut)`, `r58 = |primesUpTo cut|`, `r59 = primeSum cut`, every other register as found.

Paper quantities of the main type: the prime rows' list, `|primes|` and `Σ p`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

/-! ## The lists -/

theorem primesList_succ (m : ℕ) :
    PrimThrW.Joins.primesList (m + 1) = PrimThrW.Joins.primesList m ++ (if Nat.Prime (m + 1) then [m + 1] else []) := by
  unfold PrimThrW.Joins.primesList
  rw [List.range_succ, List.filter_append]
  by_cases h : Nat.Prime (m + 1) <;> simp [h]

theorem unaryList_append (a b : List ℕ) : Data.unaryList (a ++ b) = Data.unaryList a ++ Data.unaryList b := by
  simp [Data.unaryList, List.flatMap_append]

theorem unaryList_succ (m : ℕ) :
    Data.unaryList (PrimThrW.Joins.primesList (m + 1)) = Data.unaryList (PrimThrW.Joins.primesList m) ++ pw (m + 1) := by
  rw [primesList_succ, unaryList_append]
  unfold pw
  by_cases h : Nat.Prime (m + 1) <;> simp [h, Data.unaryList]

theorem primesList_one : PrimThrW.Joins.primesList 1 = [] := by
  unfold PrimThrW.Joins.primesList
  simp [List.range_succ, Nat.not_prime_zero, Nat.not_prime_one]

theorem primesUpTo_succ (m : ℕ) : SupplierPrime.primesUpTo (m + 1) =
    if Nat.Prime (m + 1) then insert (m + 1) (SupplierPrime.primesUpTo m) else SupplierPrime.primesUpTo m := by
  unfold SupplierPrime.primesUpTo
  rw [Finset.range_add_one, Finset.filter_insert]

theorem succ_notMem_primesUpTo (m : ℕ) : m + 1 ∉ SupplierPrime.primesUpTo m := by
  unfold SupplierPrime.primesUpTo
  simp

theorem primesList_length (c : ℕ) : (PrimThrW.Joins.primesList c).length = (SupplierPrime.primesUpTo c).card := by
  induction c with
  | zero => simp [PrimThrW.Joins.primesList, SupplierPrime.primesUpTo, Finset.filter_singleton, Nat.not_prime_zero]
  | succ m ih =>
    rw [primesList_succ, primesUpTo_succ, List.length_append, ih]
    by_cases h : Nat.Prime (m + 1)
    · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (succ_notMem_primesUpTo m)]; rfl
    · rw [if_neg h, if_neg h]; rfl

theorem primesList_sum (c : ℕ) : (PrimThrW.Joins.primesList c).sum = ThrQ.primeSum c := by
  induction c with
  | zero => simp [PrimThrW.Joins.primesList, ThrQ.primeSum, SupplierPrime.primesUpTo, Finset.filter_singleton, Nat.not_prime_zero]
  | succ m ih =>
    rw [primesList_succ, List.sum_append, ih]
    unfold ThrQ.primeSum
    rw [primesUpTo_succ]
    by_cases h : Nat.Prime (m + 1)
    · rw [if_pos h, if_pos h, Finset.sum_insert (succ_notMem_primesUpTo m)]; simp; omega
    · rw [if_neg h, if_neg h]; simp

theorem primesList_length_le (c : ℕ) : (PrimThrW.Joins.primesList c).length ≤ c + 1 := by
  unfold PrimThrW.Joins.primesList
  exact (List.length_filter_le _ _).trans (by simp)

/-- Monotonicity of the listing along the rounds. -/
theorem prefix_mono (k d : ℕ) :
    (Data.unaryList (PrimThrW.Joins.primesList k)).length ≤ (Data.unaryList (PrimThrW.Joins.primesList (k + d))).length ∧
      (PrimThrW.Joins.primesList k).sum ≤ (PrimThrW.Joins.primesList (k + d)).sum := by
  induction d with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ d ih =>
    rw [← Nat.add_assoc, unaryList_succ, primesList_succ, List.length_append, List.sum_append]
    exact ⟨ih.1.trans (Nat.le_add_right _ _), ih.2.trans (Nat.le_add_right _ _)⟩

/-! ## The listing loop -/

/-- The registers after `k` rounds (`n = cut - 1` rounds in all). -/
def pR (g0 : Fin 80 → ℕ) (n k : ℕ) : Fin 80 → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update g0 20 (n - k)) 21 (k + 2)) 58
    (PrimThrW.Joins.primesList (k + 1)).length) 59 (PrimThrW.Joins.primesList (k + 1)).sum) 74
    (Data.unaryList (PrimThrW.Joins.primesList (k + 1))).length

def pLoop : WP := .whr 20 (.seq (.dec 20) pBody)

theorem pLoop_exec (σ0 : WL) (g0 : Fin 80 → ℕ) (n : ℕ) (z22 : g0 22 = 0) (z23 : g0 23 = 0) (z24 : g0 24 = 0) (z25 : g0 25 = 0) (z26 : g0 26 = 0) (z27 : g0 27 = 0) (z28 : g0 28 = 0) (z29 : g0 29 = 0) (z30 : g0 30 = 0) (z31 : g0 31 = 0) (z33 : g0 33 = 0) (z34 : g0 34 = 0)
    (bU : (Data.unaryList (PrimThrW.Joins.primesList (n + 1))).length + n + 4 ≤ cap)
    (bS : (PrimThrW.Joins.primesList (n + 1)).sum + n + 3 ≤ cap) (bn : n + 3 ≤ cap) :
    WExec cap pLoop (pSt σ0 (Data.unaryList (PrimThrW.Joins.primesList 1)) (pR g0 n 0))
      (pSt σ0 (Data.unaryList (PrimThrW.Joins.primesList (n + 1))) (pR g0 n n))
      (n * ((n + 2) * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1) + 4) + 1) := by
  have hl := UnionMachine.Round.wloop cap 20 pBody ((n + 2) * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1)) n
    (fun k => pSt σ0 (Data.unaryList (PrimThrW.Joins.primesList (k + 1))) (pR g0 n k))
    (fun k hk => by show pR g0 n k 20 = n - k; unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by omega) (fun k hk => ?_)
  · exact hl
  have hm := prefix_mono (k + 1) (n - k)
  have e1 : k + 1 + (n - k) = n + 1 := by omega
  rw [e1] at hm
  have hlen := primesList_length_le (k + 1)
  have hb := pBody_exec cap σ0 (Data.unaryList (PrimThrW.Joins.primesList (k + 1))) (Function.update (pR g0 n k) 20 (n - k - 1))
    (k + 2) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by omega) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add])
    (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z22]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z23]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z24]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z25]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z26]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z27]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z28]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z29]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z30]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z31]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z33]) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z34])
    (by omega) (by omega) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)
  refine WExec.cast cap hb ?_ ?_
  · have eU : Data.unaryList (PrimThrW.Joins.primesList (k + 2)) =
        Data.unaryList (PrimThrW.Joins.primesList (k + 1)) ++ pw (k + 2) := unaryList_succ (k + 1)
    have eP : PrimThrW.Joins.primesList (k + 2) =
        PrimThrW.Joins.primesList (k + 1) ++ (if Nat.Prime (k + 2) then [k + 2] else []) := primesList_succ (k + 1)
    have e2 : n - k - 1 = n - (k + 1) := by omega
    unfold pg pR
    rw [show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega, eU, eP]
    congr 1
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, e2, List.length_append, List.sum_append]
    by_cases hp : Nat.Prime (k + 2) <;> simp only [hp, if_true, if_false, List.length_singleton, List.length_nil, List.sum_singleton, List.sum_nil] <;>
      split_ifs <;> subst_vars <;> simp_all <;> omega
  · have : (k + 2) * (8 * (opU cap + 1) + 4) ≤ (n + 2) * (8 * (opU cap + 1) + 4) := Nat.mul_le_mul_right _ (by omega)
    omega

/-! ## The listing -/

theorem primes_cost (m W X : ℕ) : m * ((m + 2) * W + X + 4) ≤ (m + 1) * ((m + 1) * W + X + 4) := by
  have h1 : m * (m + 2) ≤ (m + 1) * (m + 1) := by nlinarith
  have h2 : m * ((m + 2) * W) ≤ (m + 1) * ((m + 1) * W) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h1
  have h3 : m * (X + 4) ≤ (m + 1) * (X + 4) := Nat.mul_le_mul_right _ (Nat.le_succ m)
  calc m * ((m + 2) * W + X + 4) = m * ((m + 2) * W) + m * (X + 4) := by ring
    _ ≤ (m + 1) * ((m + 1) * W) + (m + 1) * (X + 4) := Nat.add_le_add h2 h3
    _ = (m + 1) * ((m + 1) * W + X + 4) := by ring

/-- `r20 := cut - 1` (the rounds), `r21 := 2` (the first candidate). -/
def pInit : WP := .seq (wcopyR 56 20 33) (.seq (.dec 20) (StarNums.incN 21 2))

def pFin : WP := .seq (WM.clear 21) (WM.clear 74)

/-- **The prime rows**: the primes `≤ r56` listed on `sPr` (`1^p 0` each), counted in `r58` and summed in `r59`. -/
def primesW : WP := .seq pInit (.seq pLoop pFin)

theorem primes_exec (σ : WL) (c : ℕ) (hc : σ.val 56 = c) (h1c : 1 ≤ c) (z20 : σ.val 20 = 0) (z21 : σ.val 21 = 0) (z22 : σ.val 22 = 0) (z23 : σ.val 23 = 0) (z24 : σ.val 24 = 0) (z25 : σ.val 25 = 0) (z26 : σ.val 26 = 0) (z27 : σ.val 27 = 0) (z28 : σ.val 28 = 0) (z29 : σ.val 29 = 0) (z30 : σ.val 30 = 0) (z31 : σ.val 31 = 0) (z33 : σ.val 33 = 0) (z34 : σ.val 34 = 0) (z58 : σ.val 58 = 0) (z59 : σ.val 59 = 0) (z74 : σ.val 74 = 0)
    (hst : σ.st sPr = []) (hsh : σ.sh sPr = 0)
    (bU : (Data.unaryList (PrimThrW.Joins.primesList c)).length + c + 3 ≤ cap)
    (bS : (PrimThrW.Joins.primesList c).sum + c + 2 ≤ cap) :
    WExec cap primesW σ (pSt σ (Data.unaryList (PrimThrW.Joins.primesList c))
      (Function.update (Function.update σ.val 58 (SupplierPrime.primesUpTo c).card) 59 (ThrQ.primeSum c)))
      (c * (c * (8 * (opU cap + 1) + 4) + 14 * (opU cap + 1) + 4) + 8 * (opU cap + 1)) := by
  have hU := lin_le_opU cap
  have hn : c - 1 + 1 = c := by omega
  have hlen := primesList_length_le c
  have i1 := (wcopy_rr cap 56 20 33 (by decide) (by decide) (by decide) σ.val c hc z20 z33 (by rw [hc]; omega)).seq cap
    ((dec_rr cap 20 (Function.update σ.val 20 c) (c - 1) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)).seq cap
    (incN_rr cap 21 2 (Function.update (Function.update σ.val 20 c) 20 (c - 1)) 2 (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z21]) (by simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add, z21]; omega)))
  have e0 : (⟨σ.sh, σ.st, Function.update (Function.update (Function.update σ.val 20 c) 20 (c - 1)) 21 2, σ.cell⟩ : WL) =
      pSt σ (Data.unaryList (PrimThrW.Joins.primesList 1)) (pR σ.val (c - 1) 0) := by
    rw [primesList_one]
    unfold pSt pR
    apply WState.eq
    · simp only [Data.unaryList, List.flatMap_nil, List.length_nil]
      rw [← hsh, Function.update_eq_self]
    · simp only [Data.unaryList, List.flatMap_nil]
      rw [← hst, Function.update_eq_self]
    · simp only [primesList_one, Data.unaryList, List.flatMap_nil, List.length_nil, List.sum_nil, Nat.sub_zero]
      funext r
      simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
      split_ifs <;> subst_vars <;> simp_all [primesList_one]
    · rfl
  have i1' := i1 σ rfl
  rw [e0] at i1'
  have l := pLoop_exec cap σ σ.val (c - 1) z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 z33 z34 (by rw [hn]; omega) (by rw [hn]; omega) (by omega)
  have f1 := RegRun.onP cap ((clear_rr cap 21 (pR σ.val (c - 1) (c - 1)) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; omega)).seq cap
    (clear_rr cap 74 (Function.update (pR σ.val (c - 1) (c - 1)) 21 0) (by unfold pR; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rw [hn]; omega)))
    σ (Data.unaryList (PrimThrW.Joins.primesList (c - 1 + 1)))
  refine WExec.cast cap (WExec.seq i1' (WExec.seq l f1)) ?_ ?_
  · rw [hn]
    congr 1
    unfold pR
    rw [hn, primesList_length, primesList_sum, Nat.sub_self]
    funext r
    simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]
    split_ifs <;> subst_vars <;> simp_all
  · have h1 := primes_cost (c - 1) (8 * (opU cap + 1) + 4) (14 * (opU cap + 1))
    rw [hn] at h1
    omega

end NearCubicWires.WireExponent3_5.PrimT.W6
