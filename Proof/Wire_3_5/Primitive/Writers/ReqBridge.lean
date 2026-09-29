import Proof.Wire_3_5.Primitive.Writers.Codec
import Proof.Wire_3_5.Primitive.Writers.DataRun

/-! # PA (d): the request bridge (the data stage reads exactly the call's word)

P3:3068-3084 (lem:primitive): the primitive is called on the fixed filters, the translation and the carriers; the
call's input is its word `PrimRequest.word` (the circuits and the carriers by their canonical codes, then the
translation's syndrome codes). PA's per-call data stage (`Data.data_step`) states its input as
`Data.reqW n mb codes cc tl`. This file identifies the two:

* **`reqW_word`**: at any call's fields, `reqW` with the translation's list word and any suffix is the call's word with
  that suffix;
* **`reqW_symReq`**: the SYM writer's input (`tl = natListWord translation`) is `(symReq …).word`;
* **`reqW_thrReq`**: the THR writer's input (`tl = natListWord translation ++ sfx`, e.g. the framed hash bits) is
  `(thrReq …).word ++ sfx`.

Paper quantity of the main type: the call's word `PrimRequest.word` (the request of lem:primitive). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ReqBridge
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.SupplierPipeline

/-- **The bridge at any call**: the data stage's input word at the call's fields is the call's word (any suffix). -/
theorem reqW_word (r : PrimRequest) (sfx : List Bool) :
    Data.reqW r.n (Codec.modeBit r.mode) (Codec.codeList r) (Codec.carrierCodes r)
      (RepairRepresentation.natListWord r.translation ++ sfx) = r.word ++ sfx := by
  rw [Codec.word_eq, Data.reqW, Codec.codeList_length]
  simp only [List.append_assoc]

/-- **The SYM bridge** (the consumer): the SYM writer's input word is the call's word. -/
theorem reqW_symReq {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ) :
    Data.reqW n false (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation) = (Primitive.symReq n a' ha' Cs carriers translation).word := by
  have h := reqW_word (Primitive.symReq n a' ha' Cs carriers translation) []
  rw [List.append_nil, List.append_nil] at h
  exact h

/-- The THR call's codes, in order. -/
def thrCodes {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) : List ℕ :=
  List.ofFn fun i => encodeNormalizedThresholdThresholdCircuit (Cs i)

/-- **The THR bridge**: the THR writer's input word (the call's word, then any suffix) at the data stage's fields. -/
theorem reqW_thrReq {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ) (sfx : List Bool) :
    Data.reqW n true (thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++ sfx) =
        (Primitive.thrReq n a' ha' Cs carriers translation).word ++ sfx :=
  reqW_word (Primitive.thrReq n a' ha' Cs carriers translation) sfx

end NearCubicWires.WireExponent3_5.PrimAsm.ReqBridge
