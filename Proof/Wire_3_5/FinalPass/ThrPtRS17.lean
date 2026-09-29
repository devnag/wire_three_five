import Proof.Wire_3_5.FinalPass.ThrPtRS16

/-! # S2 (THR per point), part 31: the scratch's formats

Facts about the formats the setup writes: `binary_zero`, `frameP_rep` (stage 2's zero accumulator is `(1 0)^h`),
`flat_rep_false`, `pairW_len`, `gateW_len`, **`gatesW_len`** (the gate table's length, `cw_spec`'s `hgh`), and the
register lemmas `tw_val_mid` (stage 2's registers belong to the base). Paper quantity: none beyond the machine model. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

theorem binary_zero : ∀ h : ℕ, RepairOrdinary.SignedSortKey.binary h 0 = List.replicate h false
  | 0 => rfl
  | h + 1 => by
    rw [RepairOrdinary.SignedSortKey.binary, binary_zero h]
    rfl

theorem frameP_rep : ∀ h : ℕ, frameP (List.replicate h false) = (List.replicate h [true, false]).flatten
  | 0 => rfl
  | h + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ← frameP_rep h]
    rfl

theorem flat_rep_false (k : ℕ) : ∀ n : ℕ, (List.replicate n (List.replicate k false)).flatten = List.replicate (n * k) false
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ, List.flatten_cons, flat_rep_false k n, ← List.replicate_add, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

theorem pairW_len (h : ℕ) (z : ℤ) : (Corner.pairW h z).length = 2 * (2 * h + 1) := by
  simp only [Corner.pairW, List.length_append, frame_len, frameP_length, List.length_singleton,
    Corner.binary_length']
  ring

theorem gateW_len {n : ℕ} (h : ℕ) (g : NormalizedThresholdGate n) :
    (Corner.gateW h g).length = 1 + (n + 1) * (2 * (2 * h + 1)) := by
  simp [Corner.gateW, pairW_len, List.length_flatMap, List.sum_replicate, Function.comp_def, List.ofFn_const]
  ring

theorem gatesW_len {n : ℕ} (h : ℕ) (G : List (NormalizedThresholdGate n)) :
    (Corner.gatesW h G).length = G.length * (1 + (n + 1) * (2 * (2 * h + 1))) + 1 := by
  simp [Corner.gatesW, List.length_flatMap, gateW_len, List.sum_replicate]

theorem tw_val_mid (σB : WState 16 118) (t : TSt) (q : Fin 118) (h1 : 93 ≤ q.val) (h2 : q.val ≤ 108) :
    (t.w σB).val q = σB.val q :=
  tw_val_other σB t q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
