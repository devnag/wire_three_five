import Proof.Wire_3_5.UnionMachine.FrontOracleField
import Proof.Wire_3_5.Primitive.Writers.WriteNat

/-! # C6 front, U1a: the oracle's arity in binary (P3:3669-3671, 3637-3641)

Realizes the arity of "one size-`q^G` general oracle" (P3:3669-3671) in the form the Theorem 2.5 repository's cold oracle decoder reads it
(`CloseoutWitness.Oracle.cold_run`: `decodeBooleanCircuit (value arityBits) (value bits)`, with `frame arityBits` and
`1^{value arityBits}` on its parser inputs): from the width `1^q` (`FrontWidth.qMachine_ready`, the padded width
`q(N)`, P3:3637-3641), a register program leaves `frame (binary ℓ q)` (`ℓ = natBitLength q`, low bit first), whose
`value` is `q`.

Program: read `q` (`readU`), PA's `bitLenM` (`ℓ`) and `payM` (the payload of `natWord q`, framed), the
terminator, every register cleared and every head rewound. Main statement: **`arP_spec`**. Paper quantity: the
oracle's arity `q(N)`, in binary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontArity
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

abbrev AS := WState 1 9

local notation "sA" => (0 : Fin 2)
local notation "sO" => (1 : Fin 2)
local notation "rc" => (8 : Fin 9)

/-- PA's writer registers `R 0 … R 7` are registers `0 … 7`; register `8` counts `A`'s head. -/
def R : Fin 8 ↪ Fin 9 := ⟨![0, 1, 2, 3, 4, 5, 6, 7], by decide⟩

/-- **The arity program.** -/
def arP : WM 1 9 :=
  .seq (WM.readU sA rc (R 0)) (.seq (bitLenM R) (.seq (payM sO R) (.seq (.wr sO false) (.seq (WM.clear (R 0))
    (.seq (WM.clear (R 4)) (.seq (WM.rewind sO (R 7)) (WM.rewind sA rc)))))))

def arCost (q : ℕ) : ℕ :=
  11 * q + 7 + 1 + (60 * q + 60 + 1 + (natBitLength q * (10 * q + 40) + 40 * q + 40 * natBitLength q + 20 + 1 +
    (1 + 1 + (3 * q + 1 + 1 + (3 * natBitLength q + 1 + 1 + (5 * (2 * natBitLength q) + 1 + 1 +
      (5 * (q + 1) + 1)))))))

/-- The program's input state: `1^q` on `A`, `O` blank, every head and register at `0`. -/
def arIn (q : ℕ) (c0 : Bool) : AS := ⟨fun _ => 0, ![List.replicate q true, []], fun _ => 0, c0⟩

/-- The program's output state: `frame (binary ℓ q)` on `O`. -/
def arOut (q : ℕ) (c0 : Bool) : AS :=
  ⟨fun _ => 0, ![List.replicate q true, frame (binary (natBitLength q) q)], fun _ => 0, c0⟩

theorem natBitLength_le (q : ℕ) : natBitLength q ≤ q + 1 := by
  unfold natBitLength
  have := Nat.log_le_self 2 q
  omega

/-- **The arity in binary**: from `1^q`, `frame (binary ℓ q)` (`ℓ = natBitLength q`), every head and register at `0`,
within `arCost q` steps, at a capacity `q + 3ℓ + 2`. -/
theorem arP_spec (q : ℕ) (c0 : Bool) (cap : ℕ) (hcap : q + 3 * natBitLength q + 2 ≤ cap) :
    WExec cap arP (arIn q c0) (arOut q c0) (arCost q) := by
  set ℓ := natBitLength q with hℓ
  have hℓq := natBitLength_le q
  have hvℓ : q < 2 ^ ℓ := Round.natBitLength_lt q
  -- read `q`
  have h1 := wreadU_spec cap sA rc (R 0) (by decide) q (arIn q c0)
    (by intro k hk; simp [arIn, readTapeBit, hk])
    (by simp [arIn, readTapeBit])
    (by simp [arIn]; omega) (by simp [arIn, R]; omega)
  set σ1 := ((((arIn q c0).seth sA ((arIn q c0).sh sA + q + 1)).setv rc ((arIn q c0).val rc + q + 1)).setv (R 0)
    ((arIn q c0).val (R 0) + q)) with hσ1
  have hv1 : ∀ i : Fin 9, σ1.val i = if i = 0 then q else if i = 8 then q + 1 else 0 := by
    intro i; fin_cases i <;> simp [σ1, arIn, R, Function.update_apply]
  -- `ℓ`
  have h2 := bitLenM_spec cap R σ1 (by rw [hv1]; simp [R]) (by rw [hv1]; simp [R]) (by rw [hv1]; simp [R])
    (by rw [hv1]; simp [R]) (by rw [hv1]; simp [R]) (by rw [hv1]; simp [R]; omega)
  have hR0 : σ1.val (R 0) = q := by rw [hv1]; simp [R]
  rw [hR0, ← hℓ] at h2
  set σ2 := σ1.setv (R 4) ℓ with hσ2
  have hv2 : ∀ i : Fin 9, σ2.val i = if i = 0 then q else if i = 4 then ℓ else if i = 8 then q + 1 else 0 := by
    intro i; fin_cases i <;> simp [σ2, hv1, R, Function.update_apply]
  -- the payload, framed
  have h3 := payM_spec cap sO R σ2 (by rw [hv2]; simp [R]) (by rw [hv2]; simp [R]) (by rw [hv2]; simp [R])
    (by rw [hv2]; simp [R]) (by rw [hv2]; simp [R]) (by simp [σ2, σ1, arIn])
    (by rw [hv2, hv2]; simpa [R] using hvℓ) (by rw [hv2, hv2, hv2]; simp [R]; omega)
  have hR4 : σ2.val (R 4) = ℓ := by rw [hv2]; simp [R]
  have hR0' : σ2.val (R 0) = q := by rw [hv2]; simp [R]
  rw [hR4, hR0'] at h3
  set u := Streaming.marks (WilliamsPublishedForm.fixedWidthNatBits ℓ q) with hu
  have hul : u.length = 2 * ℓ := by
    rw [hu, Round.testBit_eq_binary]
    exact (FrontOracleField.frameP_length _).trans (by rw [binary_length])
  set σ3 := appendO σ2 sO (R 7) u with hσ3
  -- the terminator
  have h4 := WExec.wr (cap := cap) sO false σ3
  have hO3 : σ3.st sO = u := by simp [σ3, σ2, σ1, arIn]
  have hh3 : σ3.sh sO = u.length := by simp [σ3, σ2, σ1, arIn]
  rw [hO3, hh3, writeTapeBit_end'] at h4
  set σ4 := σ3.sets sO (u ++ [false]) with hσ4
  -- clear `q`, `ℓ`
  have h5 := wclear_spec cap (R 0) q σ4 (by simp [σ4, σ3, R, Function.update_apply, hv2]) (by
    simp [σ4, σ3, R, Function.update_apply, hv2]; omega)
  have h6 := wclear_spec cap (R 4) ℓ (σ4.setv (R 0) 0) (by
    simp [σ4, σ3, R, Function.update_apply, hv2]) (by simp [σ4, σ3, R, Function.update_apply, hv2]; omega)
  -- rewind `O` and `A`
  set σ6 := (σ4.setv (R 0) 0).setv (R 4) 0 with hσ6
  have h7 := wrewind_spec cap sO (R 7) (2 * ℓ) σ6 (by simp [σ6, σ4, σ3, R, Function.update_apply, hv2, hul])
    (by simp [σ6, σ4, σ3, R, Function.update_apply, hv2, hul]; omega)
  set σ7 := (σ6.setv (R 7) 0).seth sO (σ6.sh sO - 2 * ℓ) with hσ7
  have h8 := wrewind_spec cap sA rc (q + 1) σ7 (by simp [σ7, σ6, σ4, σ3, R, Function.update_apply, hv2])
    (by simp [σ7, σ6, σ4, σ3, R, Function.update_apply, hv2]; omega)
  refine WExec.cast cap (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ rfl
    · funext i; fin_cases i <;> simp [σ7, σ6, σ4, σ3, σ2, σ1, arIn, arOut, Function.update_apply, hul]
    · funext i; fin_cases i <;> simp [σ7, σ6, σ4, σ3, σ2, σ1, arIn, arOut, Function.update_apply, hu,
        Round.testBit_eq_binary, frame_eq_frameP, frameP, Streaming.marks, hℓ]
    · funext i; fin_cases i <;> simp [σ7, σ6, σ4, σ3, σ2, σ1, arIn, arOut, R, Function.update_apply, hv2]
  · simp only [arCost, hℓ]; omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontArity
