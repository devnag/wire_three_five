import Lean
import Proof.Wire_3_5.UnionMachine.FrontAtomStageL
import Proof.Wire_3_5.UnionMachine.FrontDescLoop
import Proof.Wire_3_5.UnionMachine.FrontEntriesRef
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.UnionCodec
import Proof.Wire_3_5.UnionMachine.FrontDecodeBase


noncomputable section


/-! # The front's decode bridge: the chain's checks are the guess decoder (paper v2, §H.5)

"It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid" (paper v2, §H.5). The
chain checks the guess word with the walker (`okOf`: the pair field's scan), the pair reader of the cold front end
(`Front35.pairOf` on the field's payload), the entries' scan (`entScan E r`: `E` grid entries of canonical codes, then
zeros) and the atom stage (every atom decodes, within the description envelope). This module relates them to
`Transfer.decodeGuess` (the tag bit, `readNat`, the pair reader, `readVec (readVec readEntry)`, zero padding):
* `entsOf E u`: the entries parsed off `u`; **`restAfter_decomp`**: a successful parse of `E` entries cuts `u` into
  their words (`gridWord b x ++ 1^k 0 p`) and the rest;
* the entries' positions and payloads for the atom stage (`posOf`, `payOf`) and their shapes.

Paper quantity: the parsed guess (its entries' signs and atom codes). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef

/-! ## One scanned field -/

/-! ## The parsed entries -/

/-! ## Encoded entries -/

/-! ## Double-indexed vectors as lists -/

/-! ## The guess word, forward -/

section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N}

/-- A guess's entries: each grid entry's sign and atom code, variable-major. -/
def entsG (g : UnionGuess S z) : List (ℤ × ℕ) := linE (fun X a => (g.sign X a, g.mode.code (g.atom X a)))

theorem entsG_length (g : UnionGuess S z) :
    (entsG g).length = (g.pcpp.systematicBits + g.pcpp.auxiliaryBits) * g.s := linE_length _

theorem entriesWord_ents (g : UnionGuess S z) : entriesWord g = ((entsG g).map encE).flatten := by
  unfold entriesWord
  rw [encVec_encVec, entsG, linE_map, linE_map]; rfl

/-- **A decoded word's walk, pair field and entries.** -/
theorem decode_fwd (g : UnionGuess S z) (w : List Bool) (h : decodeGuess S z w = some g) :
    ∃ t k, w = modeTag g.mode :: t ∧ scanOK t = true ∧
      NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some g.pair ∧
      restOf t = ((entsG g).map encE).flatten ++ List.replicate k false := by
  obtain ⟨v, k, hw, hB⟩ := decodeGuess_sound h
  set t := natWord v ++ (entriesWord g ++ List.replicate k false) with ht
  have hr : readNat t = some (v, entriesWord g ++ List.replicate k false) := readNat_natWord _ _
  have hs := scan_of_readNat t _ _ hr
  have hr2 := readNat_of_scan t hs
  rw [hr] at hr2
  simp only [Option.some.injEq, Prod.mk.injEq] at hr2
  refine ⟨t, k, hw, hs, ?_, ?_⟩
  · rw [← NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf_payload t hs, ← hr2.1]; exact hB
  · rw [← hr2.2, entriesWord_ents]

theorem signs_iff (g : UnionGuess S z) (tr : List ℕ) :
    (g.checkData tr).signsOk = true ↔ ∀ e ∈ entsG g, e.1 ∈ gridSet := by
  rw [entsG, forall_mem_linE]
  simp [UnionCheckData.signsOk, UnionGuess.checkData, gridSet]

/-- **The entries' scan decides the grid signs.** -/
theorem entScan_fwd (g : UnionGuess S z) (tr : List ℕ) (k : ℕ) :
    (entScan (entsG g).length (((entsG g).map encE).flatten ++ List.replicate k false)).isSome =
      (g.checkData tr).signsOk := by
  rw [entScan_isSome]
  by_cases hs : (g.checkData tr).signsOk = true
  · rw [hs, (restAfter_enc (entsG g) _ ((signs_iff g tr).1 hs)).1]
    simp [List.all_eq_true]
  · rw [restAfter_enc_bad (entsG g) _ (by
      by_contra hc
      push Not at hc
      exact hs ((signs_iff g tr).2 hc))]
    simp only [Bool.not_eq_true] at hs
    rw [hs]

/-- On a word with grid signs, the entries' payloads are the atoms' codes. -/
theorem pay_fwd (g : UnionGuess S z) (Z : List Bool) (hg : ∀ e ∈ entsG g, e.1 ∈ gridSet) :
    ∀ j, j < (entsG g).length → ∃ X a, value (payOf (((entsG g).map encE).flatten ++ Z) (entsG g).length j) =
      g.mode.code (g.atom X a) := by
  intro j hj
  have h2 := (restAfter_enc (entsG g) Z hg).2
  have hlen : (entsOf (entsG g).length (((entsG g).map encE).flatten ++ Z)).length = (entsG g).length := by
    rw [← List.length_map (f := fun e : (Bool × Bool) × List Bool => (gridVal e.1.1 e.1.2, value e.2)), h2]
  have hmem : (entsG g)[j] ∈ entsG g := List.getElem_mem _
  obtain ⟨X, a, hXa⟩ : ∃ X a, (entsG g)[j] = (g.sign X a, g.mode.code (g.atom X a)) := by
    obtain ⟨X, a, h⟩ := (mem_linE _ _).1 hmem
    exact ⟨X, a, h.symm⟩
  refine ⟨X, a, ?_⟩
  have e1 : (((entsOf (entsG g).length (((entsG g).map encE).flatten ++ Z)).map
      (fun e => (gridVal e.1.1 e.1.2, value e.2))).getD j ((0 : ℤ), 0)).2 = ((entsG g).getD j ((0 : ℤ), 0)).2 := by
    rw [h2]
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; omega), List.getElem_map,
    List.getD_eq_getElem _ _ hj, hXa] at e1
  unfold payOf
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact e1

end Guess

/-! ## The guess word, backward -/

section Back
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (S : UnionSetup I) {N : ℕ}
  (z : BitInput N)

/-- The entry count at a pair. -/
def entN (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) : ℕ :=
  ((S.pcppOf z O).systematicBits + (S.pcppOf z O).auxiliaryBits) * S.gridSize (S.request z O).arity

/-- The parsed entries' signs and codes. -/
def plOf (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (r : List Bool) : List (ℤ × ℕ) :=
  (entsOf (entN S z O) r).map (fun e => (gridVal e.1.1 e.1.2, value e.2))

/-- **The guess the chain's checks read**: the pair, the tag's mode, the parsed signs, the decoded atoms. -/
def gOf (b : Bool) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (r : List Bool) : UnionGuess S z :=
  ⟨O, modeOf b, fun X a => ((plOf S z O r).getD (X.val * S.gridSize (S.request z O).arity + a.val) (0, 0)).1,
    fun X a => (decodeAtom (modeOf b) (S.request z O).arity
      (value (payOf r (entN S z O) (X.val * S.gridSize (S.request z O).arity + a.val)))).getD
        (S.constAtom (modeOf b) (S.request z O).arity)⟩

variable {S z}

theorem gOf_atom (b : Bool) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (r : List Bool)
    (hat : ∀ j, j < entN S z O → ∃ C : (modeOf b).Circuit (S.request z O).arity,
      decodeAtom (modeOf b) (S.request z O).arity (value (payOf r (entN S z O) j)) = some C)
    (X : PcppVar (S.pcppOf z O)) (a : Fin (S.gridSize (S.request z O).arity)) :
    decodeAtom (modeOf b) (S.request z O).arity
      (value (payOf r (entN S z O) (X.val * S.gridSize (S.request z O).arity + a.val))) = some ((gOf S z b O r).atom X a) := by
  obtain ⟨C, hC⟩ := hat _ (idx_lt X a)
  show _ = some ((decodeAtom (modeOf b) (S.request z O).arity
    (value (payOf r (entN S z O) (X.val * S.gridSize (S.request z O).arity + a.val)))).getD _)
  rw [hC]; rfl

theorem gOf_ents (b : Bool) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N)) (r v : List Bool)
    (hr : restAfter (entN S z O) r = some v)
    (hat : ∀ j, j < entN S z O → ∃ C : (modeOf b).Circuit (S.request z O).arity,
      decodeAtom (modeOf b) (S.request z O).arity (value (payOf r (entN S z O) j)) = some C) :
    entsG (gOf S z b O r) = plOf S z O r := by
  obtain ⟨hlen, -, -⟩ := restAfter_decomp (entN S z O) r v hr
  have hPLlen : (plOf S z O r).length = entN S z O := by rw [plOf, List.length_map, hlen]
  unfold entsG
  have e : (fun (X : PcppVar (S.pcppOf z O)) (a : Fin (S.gridSize (S.request z O).arity)) =>
      ((gOf S z b O r).sign X a, (gOf S z b O r).mode.code ((gOf S z b O r).atom X a))) =
      (fun X a => (plOf S z O r).getD (X.val * S.gridSize (S.request z O).arity + a.val) (0, 0)) := by
    funext X a
    have hj := idx_lt X a
    have hE : entN S z O = ((S.pcppOf z O).systematicBits + (S.pcppOf z O).auxiliaryBits) *
      S.gridSize (S.request z O).arity := rfl
    have hc := code_of_decodeAtom (gOf_atom b O r hat X a)
    refine Prod.ext rfl ?_
    refine hc.trans ?_
    rw [List.getD_eq_getElem _ _ (by omega)]
    simp only [plOf, List.getElem_map]
    unfold payOf
    rw [List.getD_eq_getElem _ _ (by omega)]
  exact (congrArg linE e).trans (linE_getD (0, 0) _ _ (plOf S z O r) hPLlen)

/-- **The chain's checks passing give the decoded guess.** -/
theorem gOf_decode (b : Bool) (t : List Bool) (hsc : scanOK t = true) (O : NearCubicGates.Close.Outer.OuterGuess (S.width N))
    (hO : NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N) (payload t) = some O)
    (v : List Bool) (hv : v.all (fun b => !b) = true) (hr : restAfter (entN S z O) (restOf t) = some v)
    (hat : ∀ j, j < entN S z O → ∃ C : (modeOf b).Circuit (S.request z O).arity,
      decodeAtom (modeOf b) (S.request z O).arity (value (payOf (restOf t) (entN S z O) j)) = some C) :
    decodeGuess S z (b :: t) = some (gOf S z b O (restOf t)) := by
  have hents := gOf_ents b O (restOf t) v hr hat
  have ht2 := decomp_encE (entN S z O) (restOf t) v hr
  have hrest : restOf t = entriesWord (gOf S z b O (restOf t)) ++ v := by
    rw [entriesWord_ents, hents]
    conv_lhs => rw [ht2]
    rfl
  have hrd : readNat t = some (value (payload t), entriesWord (gOf S z b O (restOf t)) ++ v) := by
    rw [readNat_of_scan t hsc, ← hrest]
  have key : readVec (readVec (readEntry (if b then Mode.thr else Mode.sym) (S.request z O).arity)
      (S.gridSize (S.request z O).arity)) ((S.pcppOf z O).systematicBits + (S.pcppOf z O).auxiliaryBits)
      (entriesWord (gOf S z b O (restOf t)) ++ v) =
        some (fun X a => ((gOf S z b O (restOf t)).sign X a, (gOf S z b O (restOf t)).atom X a), v) :=
    readVec_encVec _ _ (fun b' t' => readVec_encVec _ _ (readEntry_encEntry _ _) _ b' t') _ _ v
  show decodeBody S z (if b then Mode.thr else Mode.sym) t = _
  unfold decodeBody
  rw [hrd, Option.bind_some]
  dsimp only
  rw [NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf_payload t hsc, hO, Option.bind_some]
  refine (congrArg (fun o => Option.bind o _) key).trans ?_
  show (if (v.all fun b => !b) = true then _ else none) = _
  rw [if_pos hv]
  rfl

end Back

end NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode

end
