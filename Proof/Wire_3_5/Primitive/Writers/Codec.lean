import Proof.Wire_3_5.Primitive.Writers.CopyNat

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

/-- The parser's register maps: `n` read with scratch `W 3, W 4, W 5, W 8`; the copies with `Q 0 = W 10`, scratch
`W 3 … W 8`, `Q 8 = W 11`, and their own position counter `Q 7`: `W 9` (codes), `W 12` (carriers), `W 13`
(translation). -/
def pQc : Fin 9 ↪ Fin 14 := ⟨![10, 3, 4, 5, 6, 7, 8, 9, 11], by decide⟩
def pQk : Fin 9 ↪ Fin 14 := ⟨![10, 3, 4, 5, 6, 7, 8, 12, 11], by decide⟩
def pQt : Fin 9 ↪ Fin 14 := ⟨![10, 3, 4, 5, 6, 7, 8, 13, 11], by decide⟩

@[simp] theorem pQc_apply (i : Fin 9) : pQc i = ![10, 3, 4, 5, 6, 7, 8, 9, 11] i := rfl
@[simp] theorem pQk_apply (i : Fin 9) : pQk i = ![10, 3, 4, 5, 6, 7, 8, 12, 11] i := rfl
@[simp] theorem pQt_apply (i : Fin 9) : pQt i = ![10, 3, 4, 5, 6, 7, 8, 13, 11] i := rfl
@[simp] theorem stp_true : stp true = 2 := rfl

end Parser

/-! ## The round trip -/

section RoundTrip
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat

variable {ns nr : ℕ} (cap : ℕ)

/-- The writer's registers inside the parser's: `W 0 … W 11`. -/
def eR : Fin 12 ↪ Fin 14 := Fin.castLEEmb (by norm_num)

@[simp] theorem eR_apply (i : Fin 12) : eR i = Fin.castLE (by norm_num) i := rfl

end RoundTrip

end NearCubicWires.WireExponent3_5.PrimAsm.Codec
