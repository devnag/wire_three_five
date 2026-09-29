import Proof.Wire_3_5.Recovery.CaseTwoRuns

/-! # The hybrid Case-2 machine's five cold input words (P3:3758-3759; D1.6 C)

Realizes, for the hybrid slice's Case 2 ("The resulting slice is computable in `E^NP`", P3:3758), the docking interface
of the hybrid Case-2 machine (`CaseTwoExec.htwo`) in the shape of base's `CloseoutCaseTwo.DirectInput`: the
machine reads exactly five cold words (hierarchy word, recovered description, address, `1^R`, `1^B`) on tapes `0-4`
(`htwoIn`), every other tape starts blank, and its Boolean result is on `outSlot 1`. The common program's Case-2
aliases (base `CommonProgramTwo*`) are restated against this interface.

Donors checked: base `DirectInput.{words, input_port, input_empty, entry_eq}` (the same statements
for the Theorem 2.5 repository's fixed-copies machine; `words` used); `htwoIn` (used).

Paper quantity of the main type (`input_port`): the hybrid Case-2 machine's cold input words. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.RepairSource.HybridProgram.HDirect
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.Transfer

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm) (k D : ℕ)

/-- The hybrid Case-2 machine's tapes. -/
def tapes : ℕ := CaseTwoExec.G source a k D

theorem tapes_ge : 140 ≤ tapes source a k D := by
  have := CaseTwoExec.layout_all source a k D
  unfold tapes; omega

def ports (j : Fin 5) : Fin (tapes source a k D) := ⟨j.val, by have := j.isLt; have := tapes_ge source a k D; omega⟩
def outputPort : Fin (tapes source a k D) := CaseTwoExec.outSlot source a k D 1
def input (hierarchy description address : List Bool) (R B : ℕ) : Fin (tapes source a k D) → List Bool :=
  CaseTwoExec.htwoIn source a k D hierarchy description address R B

theorem port_value (j : Fin 5) : (ports source a k D j).val = j.val := rfl

theorem output_value : (outputPort source a k D).val = CaseTwoExec.b6 source a k D + 3 := by
  simp [outputPort, CaseTwoExec.outSlot]

theorem output_large : 5 ≤ (outputPort source a k D).val := by
  rw [output_value]
  have := CaseTwoExec.layout_all source a k D
  omega

theorem prepared_low (hierarchy description address : List Bool) (R B : ℕ) (i : Fin 140) (hi : i.val < 135) :
    PreparedFrames.input hierarchy description address R B i = Cold.input hierarchy description address R B ⟨i.val, hi⟩ := by
  have e : i = Fin.castAdd 5 (⟨i.val, hi⟩ : Fin 135) := Fin.ext rfl
  conv_lhs => rw [e]
  simp only [PreparedFrames.input, Fin.addCases_left]

theorem input_port (hierarchy description address : List Bool) (R B : ℕ) (j : Fin 5) :
    input source a k D hierarchy description address R B (ports source a k D j) =
      DirectInput.words hierarchy description address R B j := by
  have hj := j.isLt
  have h140 : (ports source a k D j).val < 140 := by rw [port_value]; omega
  simp only [input, CaseTwoExec.htwoIn, dif_pos h140]
  rw [prepared_low hierarchy description address R B _ (by simp only [port_value]; omega)]
  fin_cases j <;> simp [Cold.input, DirectInput.words, ports]

theorem input_empty (hierarchy description address : List Bool) (R B : ℕ)
    (i : Fin (tapes source a k D)) (hi : 5 ≤ i.val) :
    input source a k D hierarchy description address R B i = [] := by
  simp only [input, CaseTwoExec.htwoIn]
  split_ifs with h
  · by_cases h' : i.val < 135
    · rw [prepared_low hierarchy description address R B _ h']
      have hn : ∀ m : Fin 135, m.val < 5 → (⟨i.val, h'⟩ : Fin 135) ≠ m := fun m hm he => by
        have := congrArg Fin.val he
        simp only [Fin.val_mk] at this
        omega
      simp only [Cold.input, if_neg (hn 0 (by decide)), if_neg (hn 1 (by decide)), if_neg (hn 2 (by decide)),
        if_neg (hn 3 (by decide)), if_neg (hn 4 (by decide))]
    · rw [show (⟨i.val, h⟩ : Fin 140) = Fin.natAdd 135 (⟨i.val - 135, by omega⟩ : Fin 5) from
        Fin.ext (by simp; omega)]
      simp only [PreparedFrames.input, Fin.addCases_right]
  · rfl

end

end NearCubicWires.RepairSource.HybridProgram.HDirect
