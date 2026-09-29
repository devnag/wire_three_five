import Proof.Wire_3_5.Primitive.Writers.SBFieldB

/-! # SB, part 9: the field phase's word tail (zero words, trace mask, erase, clears)

From the state after the modulus dock (the modulus frame on `Fs 1`, the machine's other tapes on `Fs 2 … 17` of length
`≤ 4ℓ + 6`, `Fs 0` and `Fs 18 … 22` blank, every head of `Fs` at `0`, `Rb 0 = ℓ`, the rest of `Rb` at `0`):

* **`w3_spec`**: `Fs 0 = frame (binary ℓ (GF2.tau p ℓ))`, `Fs 1` kept, `Fs j = 0^{4ℓ+6}` (`j ≥ 2`), heads `0`, `Rb` at
  `0`, everything outside `Fs`, `Rb` and the cell unchanged, within `w3Cost`.

Paper quantity of the main type: the trace mask word (S4's word `4`, P3:2053-2055). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBField
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SBWords
open NearCubicWires.WireExponent3_5.PrimAsm.SBFieldA

section Tail
variable {ns nr : ℕ} (cap : ℕ) (Fs : Fin 23 ↪ Fin (ns + 1)) (Rb : Fin 16 ↪ Fin nr)

theorem fsne {a b : Fin 23} (h : a ≠ b) : Fs a ≠ Fs b := Fs.injective.ne h
theorem rbne {a b : Fin 16} (h : a ≠ b) : Rb a ≠ Rb b := Rb.injective.ne h

theorem rg4 : rgOf Rb 4 = Rb 11 := rfl

theorem rgOf_eq (j : Fin 9) : rgOf Rb j = Rb ⟨7 + j.val, by omega⟩ := rfl

theorem zeroL_nodup : (zeroL Fs).Nodup := by
  have e : zeroL Fs = ([0, 18, 19, 20, 21, 22] : List (Fin 23)).map Fs := rfl
  rw [e]
  exact List.Nodup.map Fs.injective (by decide)

theorem mem_zeroL (i : Fin (ns + 1)) : i ∈ zeroL Fs ↔ ∃ k : Fin 23, (k.val = 0 ∨ 18 ≤ k.val) ∧ Fs k = i := by
  constructor
  · intro h
    simp only [zeroL, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h
    · exact ⟨0, by decide, h.symm⟩
    · exact ⟨18, by decide, h.symm⟩
    · exact ⟨19, by decide, h.symm⟩
    · exact ⟨20, by decide, h.symm⟩
    · exact ⟨21, by decide, h.symm⟩
    · exact ⟨22, by decide, h.symm⟩
  · rintro ⟨k, hk, rfl⟩
    simp only [zeroL, List.mem_cons, List.not_mem_nil, or_false]
    have hk23 := k.isLt
    rcases hk with h0 | h18
    · left; exact congrArg Fs (Fin.ext h0)
    · right
      obtain ⟨m, hm⟩ : ∃ m, k.val = 18 + m := ⟨k.val - 18, by omega⟩
      have : m < 5 := by omega
      interval_cases m
      · left; exact congrArg Fs (Fin.ext hm)
      · right; left; exact congrArg Fs (Fin.ext hm)
      · right; right; left; exact congrArg Fs (Fin.ext hm)
      · right; right; right; left; exact congrArg Fs (Fin.ext hm)
      · right; right; right; right; exact congrArg Fs (Fin.ext hm)

end Tail

end NearCubicWires.WireExponent3_5.PrimAsm.SBField
