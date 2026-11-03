import Worker.Format
import Proof.Wire_3_5.UnionMachine.FrontWalkRef

/-!
# The two guessed circuits of the outer step, as one field of the guess word

Paper v2, §H.5, the outer step of the weak machine: "the weak machine guesses a circuit `Γ_src` with `q` inputs and at most
`q^G` gates [...] and guesses a second circuit `Γ_pf` with `q` inputs and at most `q^G` gates"; "It rejects malformed
descriptions". The guess word carries the pair `Γ = (Γ_src, Γ_pf)` as one framed field whose payload is `pairRaw Γ`, the
two canonical circuit codes framed one after the other. The payload is read by the worker's field reader
(`Worker.Format.readField`, twice) and each code by the canonical circuit decoder; `pairOf q raw = some Γ` is exactly
`Worker.Decodes q raw Γ`, the reader of the cold front end that runs the source check.

* `pairRaw`, `pairWord` (the framed field), `pairOf`;
* `pairOf_iff_decodes`, `pairOf_pairRaw` (round trip), `pairRaw_length_le` (no decodable payload is shorter than the
  canonical one), `payload_pairWord` and `rawOf_payload` (the walker's payload of the field is `pairRaw`).

Paper quantity: the guessed pair `Γ` (`Outer.OuterGuess q`).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Front35

open _root_.NearCubicWires _root_.NearCubicWires.RepairRepresentation _root_.NearCubicWires.RepairOrdinary.RadixSemantics
open _root_.NearCubicWires.ExecutableInterfaces _root_.NearCubicWires.CanonicalWitnessCodec
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef
open _root_.NearCubicWires.WireExponent3_5.Transfer (readNat_natWord)
open NearCubicGates.Close

/-- The payload of the pair field: the canonical codes of `Γ_src` and `Γ_pf`, each framed. -/
def pairRaw {q : ℕ} (B : Outer.OuterGuess q) : List Bool :=
  natWord (encodeBooleanCircuit B.src) ++ natWord (encodeBooleanCircuit B.pf)

/-- The pair field of the guess word: the payload `pairRaw Γ`, framed as one natural number. -/
def pairWord {q : ℕ} (B : Outer.OuterGuess q) : List Bool := natWord (value (pairRaw B))

/-- The pair read off a payload: two bit fields (`Worker.Format.readField`), each decoded at arity `q`. -/
def pairOf (q : ℕ) (raw : List Bool) : Option (Outer.OuterGuess q) :=
  (decodeBooleanCircuit q (value (Worker.Format.readField raw).1)).bind fun s =>
    (decodeBooleanCircuit q (value (Worker.Format.readField (Worker.Format.readField raw).2).1)).map fun p =>
      ⟨s, p⟩

theorem pairOf_iff_decodes (q : ℕ) (raw : List Bool) (B : Outer.OuterGuess q) :
    pairOf q raw = some B ↔ Worker.Decodes q raw B := by
  unfold pairOf Worker.Decodes
  constructor
  · intro h
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, p, hp, rfl⟩ := h
    exact ⟨hs, hp⟩
  · rintro ⟨hs, hp⟩
    rw [hs, Option.bind_some, hp, Option.map_some]

open _root_.NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-- The payload of a framed natural `v`: its `natBitLength v` low bits. -/
def rawOf (v : ℕ) : List Bool := binary (natBitLength v) v

theorem natWord_numWord (x : ℕ) : natWord x = Worker.Format.numWord x := by
  rw [_root_.NearCubicWires.WireExponent3_5.UnionMachine.Round.natWord_eq]
  simp [Worker.Format.numWord, Worker.Format.fieldWord, Worker.Format.countWord, binary_length]

theorem readField_natWord (x : ℕ) (r : List Bool) :
    value (Worker.Format.readField (natWord x ++ r)).1 = x ∧ (Worker.Format.readField (natWord x ++ r)).2 = r := by
  have h := Worker.Format.readNum_word x r
  rw [← natWord_numWord] at h
  unfold Worker.Format.readNum at h
  simp only [Prod.mk.injEq] at h
  exact h

/-- **Round trip**: the canonical payload of a pair reads back as the pair. -/
theorem pairOf_pairRaw {q : ℕ} (B : Outer.OuterGuess q) : pairOf q (pairRaw B) = some B := by
  unfold pairOf pairRaw
  obtain ⟨h1, h2⟩ := readField_natWord (encodeBooleanCircuit B.src) (natWord (encodeBooleanCircuit B.pf))
  rw [h1, decodeBooleanCircuit_encode, Option.bind_some, h2]
  have h3 := (readField_natWord (encodeBooleanCircuit B.pf) []).1
  rw [List.append_nil] at h3
  rw [h3, decodeBooleanCircuit_encode, Option.map_some]

/-- A decodable circuit code is positive (the decoder rejects `0`). -/
theorem encode_pos {q : ℕ} (C : BooleanCircuit q) : 1 ≤ encodeBooleanCircuit C := by
  by_contra h
  have h0 : encodeBooleanCircuit C = 0 := by omega
  have := decodeBooleanCircuit_encode C
  rw [h0, decodeBooleanCircuit_zero] at this
  simp at this

theorem natWord_length (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := by
  rw [_root_.NearCubicWires.WireExponent3_5.UnionMachine.Round.natWord_eq]
  simp [binary_length]; omega

/-- The pair's payload is canonical: nonempty, its last bit `1` (the top bit of `Γ_pf`'s positive code). -/
theorem pairRaw_canonical {q : ℕ} (B : Outer.OuterGuess q) :
    1 ≤ (pairRaw B).length ∧ (pairRaw B).getD ((pairRaw B).length - 1) false = true := by
  have hv := encode_pos B.pf
  have hL : 1 ≤ natBitLength (encodeBooleanCircuit B.pf) := by unfold natBitLength; omega
  have hb := binary_last (encodeBooleanCircuit B.pf) hv
  unfold pairRaw
  rw [_root_.NearCubicWires.WireExponent3_5.UnionMachine.Round.natWord_eq (encodeBooleanCircuit B.pf)]
  set L := natBitLength (encodeBooleanCircuit B.pf)
  set A := natWord (encodeBooleanCircuit B.src)
  have hbl : (binary L (encodeBooleanCircuit B.pf)).length = L := binary_length _ _
  have e0 : A ++ (List.replicate L true ++ false :: binary L (encodeBooleanCircuit B.pf)) =
      (A ++ List.replicate L true ++ [false]) ++ binary L (encodeBooleanCircuit B.pf) := by simp
  have hpl : (A ++ List.replicate L true ++ [false]).length = A.length + L + 1 := by simp; omega
  rw [e0]
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  rw [List.length_append, hpl, hbl, show A.length + L + 1 + L - 1 = (A.length + L + 1) + (L - 1) by omega,
    List.getD_append_right _ _ _ _ (by rw [hpl]; omega), hpl, Nat.add_sub_cancel_left]
  exact hb

/-- **The pair field**: `pairWord Γ = 1^{|pairRaw Γ|} 0 pairRaw Γ`. -/
theorem pairWord_eq {q : ℕ} (B : Outer.OuterGuess q) :
    pairWord B = List.replicate (pairRaw B).length true ++ false :: pairRaw B := by
  obtain ⟨h1, h2⟩ := pairRaw_canonical B
  exact natWord_value (pairRaw B) h1 (Or.inr h2)

theorem ones_frame (u r : List Bool) :
    ones ((List.replicate u.length true ++ false :: u) ++ r) = u.length := by
  rw [List.append_assoc, List.cons_append, ones_rep]

theorem drop_frame (u r : List Bool) :
    ((List.replicate u.length true ++ false :: u) ++ r).drop (u.length + 1) = u ++ r := by
  have e : (List.replicate u.length true ++ false :: u) ++ r = (List.replicate u.length true ++ [false]) ++ (u ++ r) := by
    simp
  rw [e, List.drop_left' (by simp)]

/-- **The walker reads the pair field**: on `pairWord Γ ++ r` the scan passes, the payload is `pairRaw Γ` and the rest
is `r`. -/
theorem scan_pairWord {q : ℕ} (B : Outer.OuterGuess q) (r : List Bool) :
    scanOK (pairWord B ++ r) = true ∧ payload (pairWord B ++ r) = pairRaw B ∧ restOf (pairWord B ++ r) = r := by
  have hr := readNat_natWord (value (pairRaw B)) r
  have hs := scan_of_readNat _ _ _ hr
  refine ⟨hs, ?_, ?_⟩
  · rw [pairWord_eq]
    unfold payload
    rw [ones_frame]
    rw [drop_frame, List.take_left' rfl]
  · rw [pairWord_eq]
    unfold restOf
    rw [ones_frame, show 2 * (pairRaw B).length + 1 = ((pairRaw B).length + 1) + (pairRaw B).length by omega,
      ← List.drop_drop, drop_frame, List.drop_left' rfl]

/-- **The payload is the raw field**: on a passing scan, `rawOf` of the read value is the payload. -/
theorem rawOf_payload (t : List Bool) (h : scanOK t = true) : rawOf (value (payload t)) = payload t := by
  simp only [scanOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hlen := payload_length t h2
  have hn := natBitLength_value (payload t) (by omega) (by
    rcases h3 with h3 | h3
    · left; omega
    · right; rw [payload_last t h1 h2]; exact h3)
  unfold rawOf
  rw [hn]
  exact _root_.NearCubicWires.RepairSource.VerifierDecoding.binary_value_word _

theorem rawOf_pairRaw {q : ℕ} (B : Outer.OuterGuess q) : rawOf (value (pairRaw B)) = pairRaw B := by
  have := rawOf_payload (pairWord B ++ []) (scan_pairWord B []).1
  rw [(scan_pairWord B []).2.1] at this
  exact this

/-! ## No decodable payload is shorter than the canonical one -/

theorem value_append_false (r : List Bool) (m : ℕ) : value (r ++ List.replicate m false) = value r := by
  rw [value_append]; simp

theorem natBitLength_le_of_lt (c k : ℕ) (hc : 1 ≤ c) (h : c < 2 ^ k) : natBitLength c ≤ k := by
  unfold natBitLength
  have := (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) (by omega : c ≠ 0)).2 h
  omega

/-- One field whose value is positive takes at least the canonical `2·natBitLength + 1` bits. -/
theorem readField_room (w : List Bool) (hc : 1 ≤ value (Worker.Format.readField w).1) :
    (Worker.Format.readField w).2.length + (2 * natBitLength (value (Worker.Format.readField w).1) + 1) ≤
      w.length := by
  have hsnd := Worker.Format.readField_snd w
  have hfst : (Worker.Format.readField w).1 =
      List.ofFn (fun i : Fin (Worker.Format.readCount w).1 =>
        (w.drop ((Worker.Format.readCount w).1 + 1)).getD i.val false) := by
    unfold Worker.Format.readField Worker.Format.readBits
    rw [Worker.Format.readCount_snd]
  generalize (Worker.Format.readField w) = F at hc hsnd hfst ⊢
  generalize (Worker.Format.readCount w).1 = k at hsnd hfst
  obtain ⟨F1, F2⟩ := F
  simp only at hsnd hfst hc ⊢
  subst hsnd hfst
  rw [List.length_drop]
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp [value] at hc
    · exact h0
  by_cases hw : 2 * k + 1 ≤ w.length
  · have h1 := value_lt (List.ofFn (fun i : Fin k => (w.drop (k + 1)).getD i.val false))
    rw [List.length_ofFn] at h1
    have h2 := natBitLength_le_of_lt _ k hc h1
    omega
  · -- the field runs past the end: its bits are the tail, padded with `false`
    have hrl : (w.drop (k + 1)).length < k := by rw [List.length_drop]; omega
    have hpad : List.ofFn (fun i : Fin k => (w.drop (k + 1)).getD i.val false) =
        w.drop (k + 1) ++ List.replicate (k - (w.drop (k + 1)).length) false := by
      apply List.ext_getElem (by simp; omega)
      intro i h1 h2
      simp only [List.getElem_ofFn]
      by_cases hi : i < (w.drop (k + 1)).length
      · rw [List.getD_eq_getElem _ _ hi, List.getElem_append_left hi]
      · rw [List.getD_eq_default _ _ (by omega), List.getElem_append_right (by omega)]
        simp
    rw [hpad, value_append_false] at hc ⊢
    have h1 := value_lt (w.drop (k + 1))
    have h2 := natBitLength_le_of_lt _ _ hc h1
    have hd : 1 ≤ (w.drop (k + 1)).length := by
      by_contra h0
      have e0 : (w.drop (k + 1)).length = 0 := by omega
      rw [e0] at h1
      simp at h1
      omega
    rw [List.length_drop] at h2 hd
    omega

/-- **No decodable payload is shorter than the canonical one** (`|pairRaw Γ| ≤ |raw|`). -/
theorem pairRaw_length_le {q : ℕ} (raw : List Bool) (B : Outer.OuterGuess q) (h : pairOf q raw = some B) :
    (pairRaw B).length ≤ raw.length := by
  rw [pairOf_iff_decodes] at h
  obtain ⟨h1, h2⟩ := h
  have e1 := encodeBooleanCircuit_of_decode h1
  have e2 := encodeBooleanCircuit_of_decode h2
  have p1 := encode_pos B.src
  have p2 := encode_pos B.pf
  rw [e1] at p1
  rw [e2] at p2
  have r1 := readField_room raw p1
  have r2 := readField_room _ p2
  unfold pairRaw
  rw [List.length_append, natWord_length, natWord_length, e1, e2]
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.Front35
