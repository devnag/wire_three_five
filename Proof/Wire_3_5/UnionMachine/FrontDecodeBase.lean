import Proof.Wire_3_5.UnionMachine.FrontAtomStageL
import Proof.Wire_3_5.UnionMachine.FrontDescLoop
import Proof.Wire_3_5.UnionMachine.FrontEntriesRef

/-! # C6 front, the decode bridge: the chain's checks are the decoder (P3:3669-3674)

The chain checks the guess word with the walker (`okOf`: the oracle field's scan), the oracle decoder, the entries'
scan (`entScan E r`: `E` grid entries of canonical codes, then zeros) and the atom stage (every atom decodes, within
the description envelope). This module relates them to `Transfer.decodeGuess` (the tag bit, `readNat`, the canonical
circuit decoder, `readVec (readVec readEntry)`, zero padding):
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

theorem scan_natWord (t : List Bool) (h : scanOK t = true) :
    natWord (value (payload t)) = List.replicate (payload t).length true ++ false :: payload t := by
  have e1 := readNat_sound (readNat_of_scan t h)
  have hs := h
  simp only [scanOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  have hlen := payload_length t hs.1.2
  have e2 := decomp t (by omega)
  rw [hlen]
  have e3 : natWord (value (payload t)) ++ restOf t =
      (List.replicate (ones t) true ++ false :: payload t) ++ restOf t := by
    rw [← e1]; simpa using e2
  exact List.append_cancel_right e3

theorem scan_pos (t : List Bool) (h : scanOK t = true) : 1 ≤ (payload t).length := by
  have hs := h
  simp only [scanOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  rw [payload_length t hs.1.2]; exact hs.1.1

/-! ## The parsed entries -/

/-- The entries parsed off a word, at most `E`: sign bits and payloads. -/
def entsOf : ℕ → List Bool → List ((Bool × Bool) × List Bool)
  | 0, _ => []
  | E + 1, u => match entStep u with
    | none => []
    | some e => (e.1, e.2.1) :: entsOf E e.2.2

/-- A parsed entry's word: the grid sign word, then the code's field. -/
def entWord (e : (Bool × Bool) × List Bool) : List Bool :=
  gridWord e.1.1 e.1.2 ++ (List.replicate e.2.length true ++ false :: e.2)

/-- A parsed entry is a grid sign and a canonical field. -/
def EntOK (e : (Bool × Bool) × List Bool) : Prop :=
  gridOK e.1.1 e.1.2 = true ∧ 1 ≤ e.2.length ∧ natWord (value e.2) = List.replicate e.2.length true ++ false :: e.2

theorem entStep_parts (u : List Bool) (s : Bool × Bool) (p r : List Bool) (h : entStep u = some (s, p, r)) :
    EntOK (s, p) ∧ u = entWord (s, p) ++ r := by
  match u, h with
  | b :: true :: false :: x :: t, h =>
    simp only [entStep] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [Bool.and_eq_true] at hc
    have hw := scan_natWord t hc.2
    refine ⟨⟨hc.1, scan_pos t hc.2, hw⟩, ?_⟩
    have e := readNat_sound (readNat_of_scan t hc.2)
    have e2 : t = List.replicate (payload t).length true ++ false :: (payload t ++ restOf t) := by
      conv_lhs => rw [e, hw]
      simp
    simp only [entWord, gridWord, List.cons_append, List.nil_append, List.append_assoc]
    rw [← e2]

/-- **A successful parse cuts the word into its entries' words and the rest.** -/
theorem restAfter_decomp : ∀ (E : ℕ) (u v : List Bool), restAfter E u = some v →
    (entsOf E u).length = E ∧ u = ((entsOf E u).map entWord).flatten ++ v ∧ ∀ e ∈ entsOf E u, EntOK e
  | 0, u, v, h => by
    simp only [restAfter, Option.some.injEq] at h
    subst h
    simp [entsOf]
  | E + 1, u, v, h => by
    simp only [restAfter] at h
    cases hs : entStep u with
    | none => rw [hs] at h; simp at h
    | some e =>
      rw [hs, Option.bind_some] at h
      obtain ⟨s, p, r⟩ := e
      obtain ⟨hok, hu⟩ := entStep_parts u s p r hs
      obtain ⟨h1, h2, h3⟩ := restAfter_decomp E r v h
      have he : entsOf (E + 1) u = (s, p) :: entsOf E r := by simp only [entsOf, hs]
      rw [he]
      refine ⟨by simp [h1], ?_, ?_⟩
      · rw [hu]; simp only [List.map_cons, List.flatten_cons, List.append_assoc]; rw [← h2]
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | h'
        · exact hok
        · exact h3 e' h'

/-- The entries' positions and payloads (the atom stage's `pos`, `pay`). -/
def posOf (u : List Bool) (E j : ℕ) : ℕ := (((entsOf E u).take j).map entWord).flatten.length
def payOf (u : List Bool) (E j : ℕ) : List Bool := ((entsOf E u).getD j ((false, false), [])).2

theorem entWord_length (e : (Bool × Bool) × List Bool) : (entWord e).length = 2 * e.2.length + 5 := by
  simp [entWord, gridWord]; omega

theorem flat_split {α : Type} (f : α → List Bool) (L : List α) (j : ℕ) (hj : j < L.length) :
    (L.map f).flatten = ((L.take j).map f).flatten ++ (f (L[j]) ++ ((L.drop (j + 1)).map f).flatten) := by
  have h := List.take_append_drop j L
  rw [List.drop_eq_getElem_cons hj] at h
  conv_lhs => rw [← h]
  rw [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]

/-- **The atom stage's entry shapes** on a successful parse. -/
theorem atom_shapes (E : ℕ) (u v : List Bool) (h : restAfter E u = some v) :
    posOf u E 0 = 0 ∧
    (∀ j, j < E → ∃ b x rest, u.drop (posOf u E j) =
      gridWord b x ++ (List.replicate (payOf u E j).length true ++ false :: payOf u E j) ++ rest) ∧
    (∀ j, j < E → 1 ≤ (payOf u E j).length) ∧
    (∀ j, j < E → posOf u E (j + 1) = posOf u E j + 2 * (payOf u E j).length + 5) := by
  obtain ⟨hl, hu, hok⟩ := restAfter_decomp E u v h
  set es := entsOf E u with hes
  have hget : ∀ j (hj : j < E), es.getD j ((false, false), []) = es[j]'(by omega) := fun j hj =>
    List.getD_eq_getElem _ _ (by omega)
  refine ⟨by simp [posOf], fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have e0 := flat_split entWord es j (by omega)
    refine ⟨(es[j]'(by omega)).1.1, (es[j]'(by omega)).1.2, (((es.drop (j + 1)).map entWord).flatten ++ v), ?_⟩
    have e1 : u = ((es.take j).map entWord).flatten ++ (entWord (es[j]'(by omega)) ++
        (((es.drop (j + 1)).map entWord).flatten ++ v)) := hu.trans (by rw [e0]; simp [List.append_assoc])
    unfold posOf payOf
    rw [← hes, hget j hj]
    conv_lhs => rw [e1]
    rw [List.drop_left]
    simp [entWord, List.append_assoc]
  · unfold payOf; rw [← hes, hget j hj]; exact (hok _ (List.getElem_mem _)).2.1
  · unfold posOf payOf
    rw [← hes, hget j hj, List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append, entWord_length]
    omega

/-! ## Encoded entries -/

/-- One entry's word in the codec: the sign's `intWord`, the code's `natWord`. -/
def encE (e : ℤ × ℕ) : List Bool := intWord e.1 ++ natWord e.2

/-- The grid signs. -/
def gridSet : Finset ℤ := {-1, 0, 1}

theorem entStep_encE (e : ℤ × ℕ) (he : e.1 ∈ gridSet) (rest : List Bool) :
    ∃ s p, entStep (encE e ++ rest) = some (s, p, rest) ∧ gridVal s.1 s.2 = e.1 ∧ value p = e.2 := by
  have hri : readInt (encE e ++ rest) = some (e.1, natWord e.2 ++ rest) := by
    unfold encE; rw [List.append_assoc]; exact readInt_intWord _ _
  obtain ⟨b, x, hok, hu, hz⟩ := (gridInt_iff (encE e ++ rest) e.1 (natWord e.2 ++ rest)).1 ⟨hri, he⟩
  have hsc : scanOK (natWord e.2 ++ rest) = true :=
    scan_of_readNat _ e.2 rest (readNat_natWord e.2 rest)
  have hrn := readNat_of_scan _ hsc
  rw [readNat_natWord] at hrn
  simp only [Option.some.injEq, Prod.mk.injEq] at hrn
  refine ⟨(b, x), payload (natWord e.2 ++ rest), ?_, hz.symm, hrn.1.symm⟩
  rw [hu]
  simp only [gridWord, List.cons_append, List.nil_append, entStep, hok, hsc, Bool.and_self, if_true]
  rw [← hrn.2]

theorem entStep_encE_bad (e : ℤ × ℕ) (he : e.1 ∉ gridSet) (rest : List Bool) : entStep (encE e ++ rest) = none := by
  cases h : entStep (encE e ++ rest) with
  | none => rfl
  | some r =>
    exfalso
    have hs : (entStep (encE e ++ rest)).isSome = true := by rw [h]; rfl
    obtain ⟨z, r1, v, r', hz, hmem, -⟩ := (entStep_iff _).1 hs
    have hri : readInt (encE e ++ rest) = some (e.1, natWord e.2 ++ rest) := by
      unfold encE; rw [List.append_assoc]; exact readInt_intWord _ _
    rw [hri] at hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hz
    rw [← hz.1] at hmem
    exact he hmem

/-- **A list of encoded grid entries parses**, its signs and codes read back. -/
theorem restAfter_enc : ∀ (PL : List (ℤ × ℕ)) (Z : List Bool), (∀ e ∈ PL, e.1 ∈ gridSet) →
    restAfter PL.length ((PL.map encE).flatten ++ Z) = some Z ∧
      (entsOf PL.length ((PL.map encE).flatten ++ Z)).map (fun e => (gridVal e.1.1 e.1.2, value e.2)) = PL
  | [], Z, _ => by simp [restAfter, entsOf]
  | e :: PL, Z, h => by
    obtain ⟨s, p, hs, hg, hv⟩ := entStep_encE e (h e (List.mem_cons_self ..)) ((PL.map encE).flatten ++ Z)
    obtain ⟨ih1, ih2⟩ := restAfter_enc PL Z (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    have hw : ((e :: PL).map encE).flatten ++ Z = encE e ++ ((PL.map encE).flatten ++ Z) := by
      simp [List.append_assoc]
    rw [hw]
    refine ⟨?_, ?_⟩
    · simp only [List.length_cons, restAfter, hs, Option.bind_some]; exact ih1
    · simp only [List.length_cons, entsOf, hs, List.map_cons]
      rw [ih2, hg, hv]

theorem restAfter_enc_bad : ∀ (PL : List (ℤ × ℕ)) (Z : List Bool), (∃ e ∈ PL, e.1 ∉ gridSet) →
    restAfter PL.length ((PL.map encE).flatten ++ Z) = none
  | [], Z, h => by obtain ⟨e, he, -⟩ := h; simp at he
  | e :: PL, Z, h => by
    have hw : ((e :: PL).map encE).flatten ++ Z = encE e ++ ((PL.map encE).flatten ++ Z) := by
      simp [List.append_assoc]
    rw [hw]
    by_cases he : e.1 ∈ gridSet
    · obtain ⟨s, p, hs, -, -⟩ := entStep_encE e he ((PL.map encE).flatten ++ Z)
      simp only [List.length_cons, restAfter, hs, Option.bind_some]
      obtain ⟨e', he', hne⟩ := h
      rcases List.mem_cons.mp he' with rfl | h'
      · exact absurd he hne
      · exact restAfter_enc_bad PL Z ⟨e', h', hne⟩
    · simp only [List.length_cons, restAfter, entStep_encE_bad e he, Option.bind_none]

/-- A parsed entry's word is its sign's and code's encoding. -/
theorem entWord_encE (e : (Bool × Bool) × List Bool) (h : EntOK e) :
    entWord e = encE (gridVal e.1.1 e.1.2, value e.2) := by
  unfold entWord encE
  simp only
  rw [intWord_grid _ _ h.1, h.2.2]

theorem decomp_encE (E : ℕ) (u v : List Bool) (h : restAfter E u = some v) :
    u = (((entsOf E u).map (fun e => (gridVal e.1.1 e.1.2, value e.2))).map encE).flatten ++ v := by
  obtain ⟨-, hu, hok⟩ := restAfter_decomp E u v h
  conv_lhs => rw [hu]
  congr 2
  rw [List.map_map]
  exact List.map_congr_left (fun e he => entWord_encE e (hok e he))

/-! ## Double-indexed vectors as lists -/

/-- A double-indexed vector, variable-major (the order of the `encVec (encVec …)`). -/
def linE {β : Type} {nv s : ℕ} (f : Fin nv → Fin s → β) : List β := (List.ofFn fun X => List.ofFn fun a => f X a).flatten

theorem linE_succ {β : Type} {nv s : ℕ} (f : Fin (nv + 1) → Fin s → β) :
    linE f = List.ofFn (fun a => f 0 a) ++ linE (fun X a => f X.succ a) := by
  unfold linE; rw [List.ofFn_succ, List.flatten_cons]

theorem linE_length {β : Type} : ∀ {nv s : ℕ} (f : Fin nv → Fin s → β), (linE f).length = nv * s
  | 0, s, f => by simp [linE]
  | nv + 1, s, f => by
    rw [linE_succ, List.length_append, List.length_ofFn, linE_length]; ring

theorem linE_map {β γ : Type} : ∀ {nv s : ℕ} (f : Fin nv → Fin s → β) (h : β → γ),
    (linE f).map h = linE (fun X a => h (f X a))
  | 0, s, f, h => by simp [linE]
  | nv + 1, s, f, h => by
    rw [linE_succ, linE_succ, List.map_append, List.map_ofFn, linE_map]; rfl

theorem encVec_encVec {β : Type} (enc : β → List Bool) : ∀ {nv s : ℕ} (f : Fin nv → Fin s → β),
    encVec (encVec enc) f = ((linE f).map enc).flatten
  | 0, s, f => by simp [encVec, linE]
  | nv + 1, s, f => by
    have h := encVec_encVec enc (fun (X : Fin nv) a => f X.succ a)
    rw [linE_succ, List.map_append, List.flatten_append, ← h]
    simp only [encVec, List.ofFn_succ, List.flatten_cons, List.map_ofFn]
    rfl

theorem linE_getD {β : Type} (d : β) : ∀ (nv s : ℕ) (L : List β), L.length = nv * s →
    linE (fun (X : Fin nv) (a : Fin s) => L.getD (X.val * s + a.val) d) = L
  | 0, s, L, h => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this; simp [linE]
  | nv + 1, s, L, h => by
    rw [linE_succ]
    have hs : s ≤ L.length := by rw [h]; nlinarith
    have h1 : List.ofFn (fun a : Fin s => L.getD ((0 : Fin (nv + 1)).val * s + a.val) d) = L.take s := by
      apply List.ext_getElem
      · simp; omega
      · intro n h1 h2
        simp only [List.getElem_ofFn, List.getElem_take, Fin.val_zero, zero_mul, zero_add]
        rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]
    have h2 : (fun (X : Fin nv) (a : Fin s) => L.getD (X.succ.val * s + a.val) d) =
        (fun X a => (L.drop s).getD (X.val * s + a.val) d) := by
      funext X a
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, Fin.val_succ]
      congr 2
      ring
    rw [h1, h2, linE_getD d nv s (L.drop s) (by rw [List.length_drop, h]; rw [Nat.add_mul, one_mul]; omega)]
    exact List.take_append_drop s L

theorem mem_linE {β : Type} {nv s : ℕ} (f : Fin nv → Fin s → β) (e : β) : e ∈ linE f ↔ ∃ X a, f X a = e := by
  unfold linE
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, he⟩
    rw [List.mem_ofFn] at hl
    obtain ⟨X, rfl⟩ := hl
    rw [List.mem_ofFn] at he
    obtain ⟨a, rfl⟩ := he
    exact ⟨X, a, rfl⟩
  · rintro ⟨X, a, rfl⟩
    exact ⟨_, (List.mem_ofFn).2 ⟨X, rfl⟩, (List.mem_ofFn).2 ⟨a, rfl⟩⟩

theorem forall_mem_linE {β : Type} {nv s : ℕ} (f : Fin nv → Fin s → β) (P : β → Prop) :
    (∀ e ∈ linE f, P e) ↔ ∀ X a, P (f X a) := by
  constructor
  · intro h X a; exact h _ ((mem_linE f _).2 ⟨X, a, rfl⟩)
  · intro h e he; obtain ⟨X, a, rfl⟩ := (mem_linE f e).1 he; exact h X a

/-! ## The guess word, forward -/

section Guess

end Guess

/-! ## The guess word, backward -/

section Back
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {N : ℕ}
 (z : BitInput N)

theorem idx_lt {nv s : ℕ} (X : Fin nv) (a : Fin s) : X.val * s + a.val < nv * s := by
  have h1 := X.isLt
  have h2 := a.isLt
  have : X.val * s + s ≤ nv * s := by
    have := Nat.mul_le_mul_right s (show X.val + 1 ≤ nv by omega)
    simpa [Nat.add_mul] using this
  omega

/-- The tag's mode. -/
def modeOf (b : Bool) : Mode := if b then Mode.thr else Mode.sym

end Back

end NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
