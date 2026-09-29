import Proof.Wire_3_5.Primitive.SeedFix.W6ZB

/-! # W6, part 29: the THR call's basic sizes

P3:2543-2558 (row:threshold-rows: `|𝒢| = |Sel|`, the family's magnitude envelope) and P3:3114-3115 ("All powers of `n`
are fixed before a fixed `r`"): at a THR call (`a' ≤ 4`, `descriptionBits ≤ (n+1)^{26}`), with `s` the algorithm's
source child bound at `(n+1)^{26}` and **`thrN alg P capT = s + (n+1)^{26} + cap_T + 16`**:
* `pw_mul`, `pw_add`, `pw_mono`, `pw_pow` (bounds `x ≤ N^a`);
* **`thr_basic`**: `|𝒢| ≤ N^4` (base `selection_count`), `E ≤ N^2` (base `familyMagnitudeExponent_le`),
  `|thrOccs| ≤ N^2`, every support size `≤ N`, the top word `≤ N^2`, `n ≤ N`, `cap_T ≤ N`, `16 ≤ N`.

Paper quantities of the main type: `|𝒢|`, the magnitude exponent, `M`, the payloads' sizes, all polynomial in `n`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared

section Pw
variable {N : ℕ}

theorem pw_mul {x y a b : ℕ} (hx : x ≤ N ^ a) (hy : y ≤ N ^ b) : x * y ≤ N ^ (a + b) := by
  rw [pow_add]; exact Nat.mul_le_mul hx hy

theorem pw_mono (hN : 1 ≤ N) {x a b : ℕ} (hx : x ≤ N ^ a) (h : a ≤ b) : x ≤ N ^ b :=
  hx.trans (Nat.pow_le_pow_right hN h)

theorem pw_add (hN : 2 ≤ N) {x y a b : ℕ} (hx : x ≤ N ^ a) (hy : y ≤ N ^ b) : x + y ≤ N ^ (max a b + 1) := by
  have h1 : x ≤ N ^ max a b := pw_mono (by omega) hx (le_max_left _ _)
  have h2 : y ≤ N ^ max a b := pw_mono (by omega) hy (le_max_right _ _)
  rw [pow_succ]
  nlinarith

theorem pw_pow {x a : ℕ} (hx : x ≤ N ^ a) (k : ℕ) : x ^ k ≤ N ^ (a * k) := by
  rw [pow_mul]; exact Nat.pow_le_pow_left hx k

end Pw

variable (alg : DecompositionAlgorithm)

/-- **The call's base**: the source child bound at the description cap, the cap itself, `cap_T`, and `16`. -/
def thrN (P : StarParams) (capT : ℕ) : ℕ :=
  RepairSource.CloseoutRawRows.sourceChildBound alg ((P.n + 1) ^ 26) + (P.n + 1) ^ 26 + capT + 16

theorem thr_basic (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (capT : ℕ)
    (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) :
    Fintype.card (Primitive.ThrEq P Cs alg) ≤ thrN alg P capT ^ 4 ∧
      familyMagnitudeExponent (Primitive.thrRealize P Cs alg) ≤ thrN alg P capT ^ 2 ∧
      (Primitive.thrOccs P Cs).length ≤ thrN alg P capT ^ 2 ∧ (∀ j, szOf Cs j ≤ thrN alg P capT) ∧
      (payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3).length ≤ thrN alg P capT ^ 2 ∧
      P.n ≤ thrN alg P capT ∧ capT ≤ thrN alg P capT ∧ 16 ≤ thrN alg P capT := by
  set s := RepairSource.CloseoutRawRows.sourceChildBound alg ((P.n + 1) ^ 26) with hs
  set D0 := (P.n + 1) ^ 26 with hD0
  have hN : thrN alg P capT = s + D0 + capT + 16 := rfl
  have hn : P.n ≤ D0 := by
    have : P.n + 1 ≤ (P.n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
    omega
  have hfour : (Primitive.thrRequest P Cs).circuits.length ≤ 4 := by
    show (List.ofFn Cs).length ≤ 4; rw [List.length_ofFn]; exact ha
  have hdesc : ∀ c ∈ (Primitive.thrRequest P Cs).circuits, c.descriptionBits ≤ D0 := by
    intro c hc
    have hc' : c ∈ List.ofFn Cs := hc
    rw [List.mem_ofFn] at hc'
    obtain ⟨i, rfl⟩ := hc'
    exact hd i
  have hsupp : ∀ i : Fin a', (Cs i).top.support.card ≤ D0 + 1 := fun i => by
    have := RepairSource.CloseoutRawRows.top_source_parameter (Cs i) D0 (hd i)
    omega
  have hsz : ∀ j, szOf Cs j ≤ D0 + 1 := fun j => by
    unfold szOf
    split_ifs with h
    · exact hsupp _
    · omega
  have hpay : ∀ j, (payF alg Cs j).length ≤ 4 * D0 + 2 * s + 15 := fun j => by
    unfold payF
    split_ifs with h
    · unfold PrimThrW.TopFront.payOf
      rw [frame_length, List.length_append, PrimAsm.ParseNat.natWord_length]
      have h1 := RepairSource.CloseoutRawRows.top_output_bytes alg (Cs ⟨j.val, h⟩) D0 (hd _)
      have h2 := PolynomialClock.natBitLength_le_succ ((Cs ⟨j.val, h⟩).top.support.card)
      have h3 := hsupp ⟨j.val, h⟩
      omega
    · simp
  have N16 : 16 ≤ s + D0 + capT + 16 := by omega
  have NN : s + D0 + capT + 16 ≤ (s + D0 + capT + 16) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine ⟨?_, ?_, ?_, fun j => ?_, ?_, ?_, ?_, ?_⟩
  · have h := RepairSource.CloseoutRawRows.selection_count alg (Primitive.thrRequest P Cs) D0 hfour hdesc
    refine h.trans ?_
    rw [hN]
    exact Nat.pow_le_pow_left (by omega) 4
  · have h := RepairOrdinary.CloseoutFinalC10PrimeWindow.familyMagnitudeExponent_le alg (Primitive.thrRequest P Cs) D0
      hfour hdesc
    refine h.trans ?_
    unfold RepairOrdinary.CloseoutFinalC10PrimeWindow.tupleExponentBound RepairSource.CloseoutRawRows.thresholdMagnitudeExponent
    have hc : Nat.clog 2 (s + 1) ≤ s + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    rw [hN]
    nlinarith
  · rw [M_sum P Cs ha, hN]
    have := hsz 0; have := hsz 1; have := hsz 2; have := hsz 3
    have e : ∀ j : Fin 4, (if j.val < a' then szOf Cs j else 0) ≤ D0 + 1 := fun j => by
      split_ifs <;> [exact hsz j; omega]
    have := e 0; have := e 1; have := e 2; have := e 3
    nlinarith
  · rw [hN]; have := hsz j; omega
  · have h0 := hpay 0; have h1 := hpay 1; have h2 := hpay 2; have h3 := hpay 3
    simp only [List.length_append]
    rw [hN]
    nlinarith
  · rw [hN]; omega
  · rw [hN]; omega
  · rw [hN]; omega

end NearCubicWires.WireExponent3_5.PrimT.W6
