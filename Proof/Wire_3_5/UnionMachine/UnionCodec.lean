import Lean
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.Front35.Pair
import Proof.Circuits.CanonicalWitnessCodec
import Proof.Wire_3_5.UnionMachine.UnionCodecBase




/-! # The union machine's guess codec (paper v2, §H.5)

Realizes the parsing step of the weak machine (paper v2, §H.5): "The weak machine guesses the two circuits `Γ_src` and
`Γ_pf` above, a class tag, and one sparse grid sum for each distinct PCPP variable. It rejects malformed descriptions,
oversized atoms, and coefficients outside the fixed grid [...] Every guess has `q^{O(1)} = o(N)` bits [...] At the
finitely many source lengths where this fixed envelope exceeds the refuter's `N/10` guess budget, the machine rejects
outright".

Paper quantity: the guess word `UnionGuess.word` (the class tag, the pair field `pairWord Γ` carrying the canonical codes
of `Γ_src` and `Γ_pf`, and per PCPP variable its `s(q)` grid signs and atom codes, in framed binary), whose length is the
`⌊N/16⌋` bound of `UnionAccepts`.

* `encodeGuess g` is exactly `g.word` (`encodeGuess_length_le_iff`: its length bound IS the `UnionAccepts` word bound).
* `decodeGuess S z w` reads the tag bit, the pair field (a framed natural read canonically by `readNat`; its payload
  `rawOf v` is read by `pairOf`: two bit fields, each decoded by the canonical Boolean-circuit decoder at the width
  `q(N)`), then the `(σ, atom code)` entries variable-major, each atom decoded by its mode's canonical decoder, and
  accepts trailing zero padding only.
* Round trip: `decodeGuess S z (encodeGuess g ++ replicate k false) = some g` (`decodeGuess_encodeGuess`).
* `decodeBody_sound`: a decoded body is the pair field `natWord v` (whose payload reads as the pair), then the guess's
  entries, then zeros; a decoded guess from a word of at most `⌊N/16⌋` bits meets the word bound
  (`word_le_of_decodeGuess`), since no payload that reads as `Γ` is shorter than `pairRaw Γ` (`Front35.pairRaw_length_le`).

The readers are generic (`readNat` for the framed naturals `natWord`, `readInt` for `intWord`, `readVec` for
fixed-length vectors), each with both directions (`readNat_natWord` / `readNat_sound`, …). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation

section Readers

end Readers

section Atoms

end Atoms

noncomputable section Guess
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- The guess after its tag bit: the pair field, the entries variable-major, then zero padding only. -/
def decodeBody (S : UnionSetup I) {N : ℕ} (z : BitInput N) (m : Mode) (w : List Bool) : Option (UnionGuess S z) :=
  (readNat w).bind fun p =>
    (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N)
        (NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf p.1)).bind fun B =>
      (readVec (readVec (readEntry m (S.request z B).arity) (S.gridSize (S.request z B).arity))
          ((S.pcppOf z B).systematicBits + (S.pcppOf z B).auxiliaryBits) p.2).bind fun r =>
        if r.2.all (fun b => !b) then
          some ⟨B, m, fun X a => (r.1 X a).1, fun X a => (r.1 X a).2⟩
        else none

/-- **The guess decoder** of the union machine: the tag bit, then the body. -/
def decodeGuess (S : UnionSetup I) {N : ℕ} (z : BitInput N) : List Bool → Option (UnionGuess S z)
  | [] => none
  | b :: w => decodeBody S z (if b then .thr else .sym) w

/-- **The guess encoder**: the guess word of `UnionAccepts`. -/
def encodeGuess {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z) : List Bool := g.word

variable {S : UnionSetup I} {N : ℕ} {z : BitInput N}

/-- The guess's entries as a word (signs and atom codes, variable-major). -/
def entriesWord (g : UnionGuess S z) : List Bool :=
  encVec (encVec (encEntry g.mode g.q)) (fun X a => (g.sign X a, g.atom X a))

theorem word_eq (g : UnionGuess S z) :
    g.word = modeTag g.mode :: (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairWord g.pair ++
      entriesWord g) := by
  obtain ⟨pair, m, sign, atom⟩ := g
  cases m <;> rfl

theorem readNat_pairWord {q : ℕ} (B : NearCubicGates.Close.Outer.OuterGuess q) (t : List Bool) :
    readNat (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairWord B ++ t) =
      some (RepairOrdinary.RadixSemantics.value (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairRaw B), t) :=
  readNat_natWord _ t

/-- **Round trip**: a guess word, padded with zeros, decodes to the guess. -/
theorem decodeGuess_encodeGuess (g : UnionGuess S z) (k : ℕ) :
    decodeGuess S z (encodeGuess g ++ List.replicate k false) = some g := by
  unfold encodeGuess
  rw [word_eq, List.cons_append]
  obtain ⟨pair, m, sign, atom⟩ := g
  have hm : (if modeTag m then Mode.thr else Mode.sym) = m := by cases m <;> rfl
  simp only [decodeGuess, hm]
  unfold decodeBody entriesWord
  rw [List.append_assoc, readNat_pairWord, Option.bind_some,
    NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf_pairRaw,
    NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf_pairRaw, Option.bind_some,
    readVec_encVec _ _ (fun b t => readVec_encVec _ _ (readEntry_encEntry m _) _ b t),
    Option.bind_some, all_replicate_false, if_pos rfl]

/-- **A decoded body**: the pair field `natWord v` whose payload `rawOf v` reads as the guess's pair, then the guess's
entries, then zeros. -/
theorem decodeBody_sound (m : Mode) {w : List Bool} {g : UnionGuess S z} (h : decodeBody S z m w = some g) :
    g.mode = m ∧ ∃ v k, w = natWord v ++ (entriesWord g ++ List.replicate k false) ∧
      NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N)
        (NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf v) = some g.pair := by
  simp only [decodeBody, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, B, hB, r, hr, hg⟩ := h
  split_ifs at hg with hpad
  simp only [Option.some.injEq] at hg
  subst hg
  refine ⟨rfl, p.1, r.2.length, ?_, hB⟩
  have hpad' : r.2 = List.replicate r.2.length false :=
    List.eq_replicate_iff.2 ⟨rfl, fun b hb => by simpa using (List.all_eq_true.1 hpad) b hb⟩
  have hw := readNat_sound hp
  have hv := readVec_sound _ _ (fun w b r h => readVec_sound _ _ (readEntry_sound m _) _ w b r h) _ _ _ _ hr
  rw [hw, hv, ← hpad']
  unfold entriesWord
  rfl

/-- **A decoded word**: the tag, the pair field, the entries, zeros. -/
theorem decodeGuess_sound {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    ∃ v k, w = modeTag g.mode :: (natWord v ++ (entriesWord g ++ List.replicate k false)) ∧
      NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairOf (S.width N)
        (NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf v) = some g.pair := by
  match w, h with
  | b :: w, h =>
      have hb : modeTag (if b then Mode.thr else Mode.sym) = b := by cases b <;> rfl
      obtain ⟨hm, v, k, hw, hB⟩ := decodeBody_sound _ h
      refine ⟨v, k, ?_, hB⟩
      rw [hm, hb, hw]

/-- A decoded guess's word is no longer than the decoded word. -/
theorem word_length_le_of_decodeGuess {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g) :
    g.word.length ≤ w.length := by
  obtain ⟨v, k, rfl, hB⟩ := decodeGuess_sound h
  have hl := NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairRaw_length_le _ _ hB
  have hraw : (NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf v).length = natBitLength v := by
    unfold NearCubicWires.WireExponent3_5.UnionMachine.Front35.rawOf
    exact RepairOrdinary.SignedSortKey.binary_length _ _
  have hp : (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairWord g.pair).length =
      2 * (NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairRaw g.pair).length + 1 := by
    rw [NearCubicWires.WireExponent3_5.UnionMachine.Front35.pairWord_eq]; simp; omega
  have hn := NearCubicWires.WireExponent3_5.UnionMachine.Front35.natWord_length v
  rw [word_eq]
  simp only [List.length_cons, List.length_append, List.length_replicate]
  omega

/-- A guess decoded from a word within the refuter's `⌊N/16⌋` budget meets `UnionAccepts`' word bound. -/
theorem word_le_of_decodeGuess {w : List Bool} {g : UnionGuess S z} (h : decodeGuess S z w = some g)
    (hw : w.length ≤ N / 16) : g.word.length ≤ N / 16 :=
  (word_length_le_of_decodeGuess h).trans hw

end Guess

end NearCubicWires.WireExponent3_5.Transfer

