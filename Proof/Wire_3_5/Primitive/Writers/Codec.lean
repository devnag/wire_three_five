import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Foundations.SkeletonBase

/-! # PA library (a), part 4: the PrimRequest codec — the word's fields, the writer and the parser

A primitive call arrives as `frame req.word` ("The algorithm receives polynomial-bit integer circuit descriptions",
P3:3119-3120), where `req.word` is the Skeleton's framed encoding of the call (P3:3071-3091): the length `n`, the class
mode, the arity `a`, the `a` circuits by their canonical codes, the named carriers by their codes, and the common
translation's syndrome codes. This module states the field decomposition of `frame req.word` (**`frame_word_eq`**) on
which the codec's writer (docked by the union machine's request writer) and parser both rest.

Paper quantity of the main type: the call's description `req.word`, field by field. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Codec
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The class mode's bit in the word: `THR` is `true`. -/
def modeBit : Mode → Bool
  | .thr => true
  | .sym => false

/-- The circuits' codes, in order. -/
def codeList (r : PrimRequest) : List ℕ := List.ofFn fun i => r.mode.code (r.circuits i)

/-- The carriers' codes, in order. -/
def carrierCodes (r : PrimRequest) : List ℕ := r.carriers.map Stars.Carrier.code

theorem flatten_ofFn_natWord {a : ℕ} (g : Fin a → ℕ) :
    (List.ofFn fun i => RepairRepresentation.natWord (g i)).flatten =
      (List.ofFn g).flatMap RepairRepresentation.natWord := by
  rw [List.flatMap, List.map_ofFn]
  rfl

/-- **The fields of a call's word.** -/
theorem word_eq (r : PrimRequest) :
    r.word = RepairRepresentation.natWord r.n ++ [modeBit r.mode] ++ RepairRepresentation.natWord r.a ++
      (codeList r).flatMap RepairRepresentation.natWord ++ RepairRepresentation.natListWord (carrierCodes r) ++
        RepairRepresentation.natListWord r.translation := by
  obtain ⟨n, mode, a, ha, circuits, carriers, translation⟩ := r
  cases mode <;> (unfold PrimRequest.word codeList carrierCodes; rw [flatten_ofFn_natWord]; rfl)

/-- The codes list has the call's arity as its length. -/
theorem codeList_length (r : PrimRequest) : (codeList r).length = r.a := by simp [codeList]


/-! ## The writer -/

section Writer
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ} (cap : ℕ)


theorem word_length (r : PrimRequest) : r.word.length = (RepairRepresentation.natWord r.n).length + 1 +
    (RepairRepresentation.natWord r.a).length + ((codeList r).flatMap RepairRepresentation.natWord).length +
      (RepairRepresentation.natListWord (carrierCodes r)).length + (RepairRepresentation.natListWord r.translation).length := by
  rw [word_eq]; simp; ring

end Writer


/-! ## The parser -/

section Parser
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ} (cap : ℕ)


@[simp] theorem stp_true : stp true = 2 := rfl

end Parser


/-! ## The round trip -/

section RoundTrip
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

end RoundTrip

end NearCubicWires.WireExponent3_5.PrimAsm.Codec
