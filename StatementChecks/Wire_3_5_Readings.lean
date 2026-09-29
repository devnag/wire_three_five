import Statement_Wire_3_5
import StatementChecks.Theorem2_5_PreparedCircuits

/-! # Statement check: the wire reading

P3:213-216 counts the wires of a depth-two circuit as the bottom support plus one top incidence per bottom gate.
`WireExponent3_5` (the statement file) deletes the THR tops of weight zero: its THR∘THR count is
`∑ i, if topWeight i = 0 then 0 else support + 1`. This module proves that this gives the same theorem:
the statement is equivalent to `WireExponent3_5Raw`, the same statement with every top incidence counted
(`thrRawWires`), at every `c, K_T, K_S`, hence at row B (`rowB_iff_raw`).

* `ours_eq_wireCount`: the statement's THR count is Theorem 2.5's `wireCount`.
* `ours_le_raw`: it never exceeds the raw count, so a bound on the raw count is the stronger hypothesis.
* `raw_thrPrepare_le`: the prepared circuit of Theorem 2.5's statement check (`thrPrepare`, zero tops deleted and
  constants propagated; the same function, `thrPrepare_eval`) has raw count at most the statement's count of the
  original circuit, so the raw reading also bounds every circuit the statement quantifies over.

Main declarations: `thrRawWires`, `WireExponent3_5HardRaw`, `WireExponent3_5Raw`, **`hard_iff_raw`**,
**`rowB_iff_raw`**. Paper quantity: the wire count `W(C)` of P3:213-216.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Readings

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.WireExponent3_5
open NearCubicWires.Theorem2_5_PreparedCircuits

/-- The THR∘THR wire count with every top incidence counted, zero-weight tops included (P3:213-216, raw). -/
def thrRawWires {n : ℕ} (circuit : ThresholdThresholdCircuit n) : ℕ :=
  ∑ i : Fin circuit.bottomCount, ((circuit.bottom i).support.card + 1)

/-- The statement's THR∘THR wire count, as `WireExponent3_5Hard` writes it. -/
noncomputable def thrStatementWires {n : ℕ} (circuit : ThresholdThresholdCircuit n) : ℕ :=
  ∑ i : Fin circuit.bottomCount,
    if circuit.topWeight i = 0 then 0 else (circuit.bottom i).support.card + 1

/-- `WireExponent3_5Hard` with the raw THR∘THR count. -/
noncomputable def WireExponent3_5HardRaw (c KT KS : ℝ) (language : Language) : Prop :=
  ∀ AT AS : ℝ, 0 < AT → 0 < AS →
    ∃ onset : ℕ, ∀ n : ℕ, onset ≤ n →
      (∀ circuit : ThresholdThresholdCircuit n,
        ((thrRawWires circuit : ℕ) : ℝ) ≤
          AT * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KT →
        ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) <
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c)) ∧
      (∀ circuit : SymmetricThresholdCircuit n,
        ((∑ i : Fin circuit.bottomCount,
            ((circuit.bottom i).support.card + 1) : ℕ) : ℝ) ≤
          AS * (n : ℝ) ^ ((7 : ℝ) / 2) / (Nat.clog 2 (n + 2) : ℝ) ^ KS →
        ((Finset.univ.filter fun x => circuit.eval x = language n x).card : ℝ) /
            (Fintype.card (Fin n → Bool) : ℝ) <
          1 / 2 + (Nat.clog 2 (n + 2) : ℝ) ^ (-c))

/-- `WireExponent3_5` with the raw THR∘THR count. -/
noncomputable def WireExponent3_5Raw (c KT KS : ℝ) : Prop :=
  ∃ language : Language,
    (∃ oracle : ℕ → Bool, Nonempty (EncodedNPVerifier oracle) ∧
        Nonempty (OrdinaryENPCertificate oracle language)) ∧
    WireExponent3_5HardRaw c KT KS language

theorem ours_eq_wireCount {n : ℕ} (circuit : ThresholdThresholdCircuit n) :
    thrStatementWires circuit = circuit.wireCount := by
  unfold thrStatementWires ThresholdThresholdCircuit.wireCount
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : circuit.topWeight i = 0 <;> simp [h]

theorem ours_le_raw {n : ℕ} (circuit : ThresholdThresholdCircuit n) :
    thrStatementWires circuit ≤ thrRawWires circuit := by
  unfold thrStatementWires thrRawWires
  refine Finset.sum_le_sum fun i _ => ?_
  split_ifs <;> omega

theorem raw_thrPrepare_le {n : ℕ} (circuit : ThresholdThresholdCircuit n) :
    thrRawWires (thrPrepare circuit) ≤ thrStatementWires circuit := by
  have hall : thrRawWires (thrPrepare circuit) = (thrPrepare circuit).wireCount := by
    unfold thrRawWires ThresholdThresholdCircuit.wireCount
    rw [Finset.filter_true_of_mem fun j _ => (thrPrepare_prepared circuit j).1]
  rw [hall, ours_eq_wireCount]
  exact thrPrepare_wireCount circuit

/-- The agreement expression depends on the circuit only through its function. -/
theorem agreement_thrPrepare {n : ℕ} (circuit : ThresholdThresholdCircuit n) (f : BitInput n → Bool) :
    (Finset.univ.filter fun x => (thrPrepare circuit).eval x = f x) =
      Finset.univ.filter fun x => circuit.eval x = f x := by
  refine Finset.filter_congr fun x _ => ?_
  rw [thrPrepare_eval]

/-- **SC2**: the statement's reading and the raw reading give the same hardness statement, for every language. -/
theorem hard_iff_raw (c KT KS : ℝ) (language : Language) :
    WireExponent3_5Hard c KT KS language ↔ WireExponent3_5HardRaw c KT KS language := by
  constructor
  · intro h AT AS hAT hAS
    obtain ⟨onset, hon⟩ := h AT AS hAT hAS
    refine ⟨onset, fun n hn => ⟨fun circuit hW => ?_, (hon n hn).2⟩⟩
    refine (hon n hn).1 circuit (le_trans ?_ hW)
    have := ours_le_raw circuit
    unfold thrStatementWires at this
    exact_mod_cast this
  · intro h AT AS hAT hAS
    obtain ⟨onset, hon⟩ := h AT AS hAT hAS
    refine ⟨onset, fun n hn => ⟨fun circuit hW => ?_, (hon n hn).2⟩⟩
    have hle : ((thrRawWires (thrPrepare circuit) : ℕ) : ℝ) ≤
        ((∑ i : Fin circuit.bottomCount,
          if circuit.topWeight i = 0 then 0 else (circuit.bottom i).support.card + 1 : ℕ) : ℝ) := by
      have := raw_thrPrepare_le circuit
      unfold thrStatementWires at this
      exact_mod_cast this
    have key := (hon n hn).1 (thrPrepare circuit) (le_trans hle hW)
    rwa [agreement_thrPrepare] at key

/-- **SC2 at every row**: `WireExponent3_5 c K_T K_S ↔ WireExponent3_5Raw c K_T K_S`. -/
theorem wireExponent3_5_iff_raw (c KT KS : ℝ) :
    NearCubicWires.WireExponent3_5 c KT KS ↔ WireExponent3_5Raw c KT KS := by
  unfold NearCubicWires.WireExponent3_5 WireExponent3_5Raw
  exact exists_congr fun language => and_congr Iff.rfl (hard_iff_raw c KT KS language)

/-- **SC2 at row B.** -/
theorem rowB_iff_raw : rowB ↔ WireExponent3_5Raw (1 / 8) (11 / 2) (9 / 2) :=
  wireExponent3_5_iff_raw (1 / 8) (11 / 2) (9 / 2)

end NearCubicWires.WireExponent3_5.Readings
