import Proof.Wire_3_5.Primitive.SeedFix.CarWM
import Proof.Wire_3_5.Primitive.SeedFix.TabDock
import Proof.Wire_3_5.Primitive.Writers.ParseNat

/-! # C6 front, U5, the code writers: the word passes over the circuits' codes

The carrier writer reads the codes of the circuits it collects: its input is `frame u` with
`u = codesWord m cs`, the codes' self-delimiting fields `natWord (m.code c)` one after another
("It then selects the common star translation, constructs the shared coordinate filters", P3:3673-3674; a call names
its carriers by their codes, `PrimRequest.word`, P3:3071-3094). Base's circuit decoders read a circuit's code as
`frame bits` with `value bits` the code, so the writer copies each field's PAYLOAD `pay x` (the `L` little-endian bits
after `1^L 0`) to a fresh tape. This module gives the word passes, in C5's word layer `WM`, streams only (no
registers), with a unary ruler that the pass erases back to `false`:
* `prefW` (count the field's `1^L` onto the ruler), `paySkipW` / `payCopyW` (skip / copy one payload cell pair per
  ruler cell), **`skipNatW_spec`**, **`copyNatW_spec`**;
* the loop-A crop **`cropAW_spec`**: skip `i` fields along the round counter, copy field `i`'s payload, advance the
  counter in place; it also writes the constant `frame []` the circuit header reads;
* the circuit count **`countW_spec`**: `false :: 1^c` for the `c` fields of the input.

Paper quantity of the main types: the code `m.code c` of circuit `i` as base's decoders read it (`frame (pay x)`,
`value (pay x) = x`, **`value_pay`**), and the number of circuits. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts fwd_facts emitW rd_shift)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (natWord_getD_one natWord_getD_zero natWord_getD_payload)

/-! ## The payload of a field -/

/-- The payload of `natWord x`: its `L = natBitLength x` little-endian bits. -/
def pay (x : ℕ) : List Bool := WilliamsPublishedForm.fixedWidthNatBits (natBitLength x) x

theorem pay_length (x : ℕ) : (pay x).length = natBitLength x := by
  simp [pay, WilliamsPublishedForm.fixedWidthNatBits]

theorem natWord_pay (x : ℕ) : natWord x = List.replicate (natBitLength x) true ++ false :: pay x := rfl

theorem natWord_len (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 := by
  rw [natWord_pay, List.length_append, List.length_replicate, List.length_cons, pay_length]; omega

theorem natBitLength_pos (x : ℕ) : 1 ≤ natBitLength x := by unfold natBitLength; omega

theorem natWord_getD_pay (x j : ℕ) : (natWord x).getD (natBitLength x + 1 + j) false = (pay x).getD j false := by
  rw [natWord_pay, List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, show natBitLength x + 1 + j - natBitLength x = j + 1 by omega, List.getD_cons_succ]

/-- **The payload's value is the field's number.** -/
theorem value_pay (x : ℕ) : RadixSemantics.value (pay x) = x := by
  unfold pay
  rw [NearCubicWires.WireExponent3_5.UnionMachine.Round.testBit_eq_binary]
  exact RepairOrdinary.SignedSortKey.binary_value _ _ (NearCubicWires.WireExponent3_5.UnionMachine.Round.natBitLength_lt x)

/-- The framed field `frameP (natWord x)`. -/
def nf (x : ℕ) : List Bool := frameP (natWord x)

theorem nf_length (x : ℕ) : (nf x).length = 4 * natBitLength x + 2 := by
  simp [nf, natWord_len]; ring

/-- Cells of `frameP w` inside a tape. -/
theorem rd_mark (pre w rest : List Bool) (j : ℕ) (hj : j < w.length) :
    readTapeBit (pre ++ (frameP w ++ rest)) (pre.length + 2 * j) = true := by
  rw [rd_shift]
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => simp [readTapeBit]
    | succ j =>
      have := ih j (by simp at hj; omega)
      simpa [readTapeBit, show 2 * (j + 1) = 2 * j + 2 by ring] using this

theorem rd_bit (pre w rest : List Bool) (j : ℕ) (hj : j < w.length) :
    readTapeBit (pre ++ (frameP w ++ rest)) (pre.length + (2 * j + 1)) = w.getD j false := by
  rw [rd_shift]
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => simp [readTapeBit]
    | succ j =>
      have := ih j (by simp at hj; omega)
      simpa [readTapeBit, show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring] using this

/-! ## The ruler -/

/-- A ruler: `k` marked cells, then `false` up to length `M`. -/
def ruler (k M : ℕ) : List Bool := List.replicate k true ++ List.replicate (M - k) false

theorem ruler_zero (M : ℕ) : ruler 0 M = List.replicate M false := by simp [ruler]

theorem ruler_write_true (k M : ℕ) : writeTapeBit (ruler k M) k true = ruler (k + 1) M := by
  unfold ruler
  by_cases h : k < M
  · rw [show M - k = (M - (k + 1)) + 1 by omega, List.replicate_succ]
    have := NearCubicWires.WireExponent3_5.PrimT.CarWM.write_counter k (List.replicate (M - (k + 1)) false)
    rw [this]
  · rw [show M - k = 0 by omega, show M - (k + 1) = 0 by omega, List.replicate_zero, List.append_nil,
      List.append_nil]
    have := NearCubicWires.WireExponent3_5.FinalPass.Tm.writeTapeBit_end' (List.replicate k true) true
    rw [List.length_replicate] at this
    rw [this, ← List.replicate_succ']

theorem ruler_write_false (k M : ℕ) (h : k + 1 ≤ M) : writeTapeBit (ruler (k + 1) M) k false = ruler k M := by
  unfold ruler
  rw [List.replicate_succ', List.append_assoc, List.singleton_append,
    show M - k = (M - (k + 1)) + 1 by omega, List.replicate_succ]
  have := NearCubicWires.WireExponent3_5.FinalPass.Tm.writeTapeBit_mid' (List.replicate k true)
    (List.replicate (M - (k + 1)) false) true false
  rw [List.length_replicate] at this
  exact this

theorem ruler_read_lt (k M i : ℕ) (hi : i < k) : readTapeBit (ruler k M) i = true := by
  unfold ruler readTapeBit
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [hi]

theorem ruler_read_ge (k M i : ℕ) (hi : k ≤ i) : readTapeBit (ruler k M) i = false := by
  unfold ruler readTapeBit
  rw [List.getD_append_right _ _ _ _ (by simpa using hi)]
  simp

section Words
variable {ns nr : ℕ} (cap : ℕ)

/-! ## The prefix: `1^L` onto the ruler -/

/-- One prefix cell: two cells forward on `S`, one ruler cell marked. -/
def prefBody (S R : Fin (ns + 1)) : WM ns nr := .seq (.fwd S) (.seq (.fwd S) (.seq (.wr R true) (.fwd R)))

theorem prefLoop_spec (S R : Fin (ns + 1)) (hSR : S ≠ R) (p L M : ℕ) :
    ∀ (d k : ℕ) (σ : WState ns nr), k + d = L →
      (∀ j < L, readTapeBit (σ.st S) (p + 1 + 2 * j) = true) → readTapeBit (σ.st S) (p + 1 + 2 * L) = false →
      σ.sh S = p + 1 + 2 * k → σ.st R = ruler k M → σ.sh R = k →
      ∃ τ, WExec cap (.whs S (prefBody S R)) σ τ (d * 9 + 1) ∧ τ.st S = σ.st S ∧ τ.sh S = p + 1 + 2 * L ∧
        τ.st R = ruler L M ∧ τ.sh R = L ∧ (∀ j, j ≠ S → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, hkd, _, hz, hSh, hR, hRh => by
    have hk : k = L := by omega
    subst hk
    refine ⟨σ, WExec.mono (WExec.whsF (by simpa [wbit, hSh] using hz)) (by omega), rfl, hSh, hR, hRh,
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | d + 1, k, σ, hkd, hT, hz, hSh, hR, hRh => by
    have hRS : R ≠ S := fun e => hSR e.symm
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap S σ
    obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap S σ1
    have R2 := (o1 R hRS).trans' (o2 R hRS)
    have s3 := WExec.wr (cap := cap) R true σ2
    set σ3 := σ2.sets R (writeTapeBit (σ2.st R) (σ2.sh R) true) with hσ3
    obtain ⟨σ4, s4, a4, a4h, o4, v4, c4⟩ := fwd_facts cap R σ3
    have eR3 : σ3.st R = ruler (k + 1) M := by
      simp only [hσ3, WState.sets_st, Function.update_self]; rw [R2.1, R2.2, hR, hRh, ruler_write_true]
    have S4 := o4 S hSR
    obtain ⟨τ, s5, eS, eSh, eR, eRh, oth, v5, c5⟩ := prefLoop_spec S R hSR p L M d (k + 1) σ4 (by omega)
      (by rw [S4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hSR, a2, a1]; exact hT)
      (by rw [S4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hSR, a2, a1]; exact hz)
      (by rw [S4.2]; simp only [hσ3, WState.sets_sh]; rw [a2h, a1h, hSh]; ring)
      (by rw [a4]; exact eR3)
      (by rw [a4h]; simp only [hσ3, WState.sets_sh]; rw [R2.2, hRh])
    have hw : wbit σ S = true := by
      simp only [wbit, hSh]; exact hT k (by omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) s5) (by ring_nf; omega),
      ?_, eSh, eR, eRh, ?_, ?_, ?_⟩
    · rw [eS, S4.1]; simp only [hσ3, WState.sets_st]; rw [Function.update_of_ne hSR, a2, a1]
    · intro j h1 h2
      have o3 : Same σ2 σ3 j := ⟨by simp [hσ3, Function.update_of_ne h2], rfl⟩
      exact ((((o1 j h1).trans' (o2 j h1)).trans' o3).trans' (o4 j h2)).trans' (oth j h1 h2)
    · rw [v5, v4]; simp only [hσ3, WState.sets_val]; rw [v2, v1]
    · rw [c5, c4]; simp only [hσ3, WState.sets_cell]; rw [c2, c1]

theorem ruler_max (L r : ℕ) : ruler L r = ruler L (max L r) := by
  unfold ruler; congr 2; omega

/-! ## The payload: one cell pair per ruler cell, the ruler erased back to `false` -/

/-- One skipped payload cell pair. -/
def skipBody (S R : Fin (ns + 1)) : WM ns nr := .seq (.wr R false) (.seq (.bwd R) (.seq (.fwd S) (.fwd S)))

theorem skipLoop_spec (S R : Fin (ns + 1)) (hSR : S ≠ R) (M : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), k ≤ M → σ.st R = ruler k M → σ.sh R = k - 1 →
      ∃ τ, WExec cap (.whs R (skipBody S R)) σ τ (k * 9 + 1) ∧ τ.st S = σ.st S ∧ τ.sh S = σ.sh S + 2 * k ∧
        τ.st R = ruler 0 M ∧ τ.sh R = 0 ∧ (∀ j, j ≠ S → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, σ, _, hR, hRh => by
    have hz : wbit σ R = false := by simp only [wbit, hR, hRh]; exact ruler_read_ge 0 M _ (Nat.zero_le _)
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by simp, hR, by simpa using hRh,
      fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | k + 1, σ, hkM, hR, hRh => by
    have hRS : R ≠ S := fun e => hSR e.symm
    have hw : wbit σ R = true := by simp only [wbit, hR, hRh]; exact ruler_read_lt _ M _ (by omega)
    have s1 := WExec.wr (cap := cap) R false σ
    set σ1 := σ.sets R (writeTapeBit (σ.st R) (σ.sh R) false) with hσ1
    have e1 : σ1.st R = ruler k M := by
      simp only [hσ1, WState.sets_st, Function.update_self]; rw [hR, hRh]; exact ruler_write_false k M hkM
    have s2 := WExec.bwd (cap := cap) R σ1
    set σ2 := σ1.seth R (σ1.sh R - 1) with hσ2
    obtain ⟨σ3, s3, a3, a3h, o3, v3, c3⟩ := fwd_facts cap S σ2
    obtain ⟨σ4, s4, a4, a4h, o4, v4, c4⟩ := fwd_facts cap S σ3
    have R4 := (o3 R hRS).trans' (o4 R hRS)
    obtain ⟨τ, s5, eS, eSh, eR, eRh, oth, v5, c5⟩ := skipLoop_spec S R hSR M k σ4 (by omega)
      (by rw [R4.1]; simpa [hσ2] using e1)
      (by rw [R4.2]; simp [hσ2, hσ1, hRh])
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) s5) (by ring_nf; omega),
      ?_, ?_, eR, eRh, ?_, ?_, ?_⟩
    · rw [eS, a4, a3]; simp [hσ2, hσ1, Function.update_of_ne hSR]
    · rw [eSh, a4h, a3h]; simp [hσ2, hσ1, Function.update_of_ne hSR]; ring
    · intro j h1 h2
      have o12 : Same σ σ2 j := ⟨by simp [hσ2, hσ1, Function.update_of_ne h2], by simp [hσ2, hσ1, Function.update_of_ne h2]⟩
      exact ((o12.trans' (o3 j h1)).trans' (o4 j h1)).trans' (oth j h1 h2)
    · rw [v5, v4, v3]; simp [hσ2, hσ1]
    · rw [c5, c4, c3]; simp [hσ2, hσ1]

/-- One copied payload cell pair: the marker, then the bit read on `S`. -/
def copyBody (S R O : Fin (ns + 1)) : WM ns nr :=
  .seq (.wr R false) (.seq (.bwd R) (.seq (.fwd S) (.seq (emitW O true)
    (.seq (.ifs S (emitW O true) (emitW O false)) (.fwd S)))))

theorem copyLoop_spec (S R O : Fin (ns + 1)) (hSR : S ≠ R) (hSO : S ≠ O) (hRO : R ≠ O) (M : ℕ) (w : List Bool)
    (hwM : w.length ≤ M) (q : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), k ≤ w.length →
      (∀ j < w.length, readTapeBit (σ.st S) (q + 2 * j + 1) = w.getD j false) →
      σ.sh S = q + 2 * (w.length - k) → σ.st R = ruler k M → σ.sh R = k - 1 →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (.whs R (copyBody S R O)) σ τ (k * 20 + 1) ∧ τ.st S = σ.st S ∧ τ.sh S = q + 2 * w.length ∧
        τ.st R = ruler 0 M ∧ τ.sh R = 0 ∧ τ.st O = σ.st O ++ frameP (w.drop (w.length - k)) ∧
        τ.sh O = (τ.st O).length ∧ (∀ j, j ≠ S → j ≠ R → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, σ, _, _, hSh, hR, hRh, hOh => by
    have hz : wbit σ R = false := by simp only [wbit, hR, hRh]; exact ruler_read_ge 0 M _ (Nat.zero_le _)
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by simpa using hSh, hR, by simpa using hRh, ?_, hOh,
      fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
    simp
  | k + 1, σ, hkw, hT, hSh, hR, hRh, hOh => by
    have hRS : R ≠ S := fun e => hSR e.symm
    have hOS : O ≠ S := fun e => hSO e.symm
    have hOR : O ≠ R := fun e => hRO e.symm
    have hw : wbit σ R = true := by simp only [wbit, hR, hRh]; exact ruler_read_lt _ M _ (by omega)
    have s1 := WExec.wr (cap := cap) R false σ
    set σ1 := σ.sets R (writeTapeBit (σ.st R) (σ.sh R) false) with hσ1
    have e1 : σ1.st R = ruler k M := by
      simp only [hσ1, WState.sets_st, Function.update_self]; rw [hR, hRh]; exact ruler_write_false k M (by omega)
    have s2 := WExec.bwd (cap := cap) R σ1
    set σ2 := σ1.seth R (σ1.sh R - 1) with hσ2
    obtain ⟨σ3, s3, a3, a3h, o3, v3, c3⟩ := fwd_facts cap S σ2
    have O3 := o3 O hOS
    obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap O true σ3 (by
      rw [O3.1, O3.2]; simp [hσ2, hσ1, Function.update_of_ne hOR, hOh])
    set j0 := w.length - (k + 1) with hj0
    have hj0w : j0 < w.length := by omega
    have hb : wbit σ4 S = w.getD j0 false := by
      have S4 := o4 S hSO
      simp only [wbit, S4.1, S4.2, a3, a3h]
      simp only [hσ2, hσ1, WState.seth_st, WState.sets_st, WState.seth_sh, WState.sets_sh,
        Function.update_of_ne hSR]
      rw [hSh]
      have := hT j0 hj0w
      rw [show q + 2 * (w.length - (k + 1)) + 1 = q + 2 * j0 + 1 by omega]
      exact this
    obtain ⟨σ5, s5', e5, e5h, o5, v5, c5⟩ := emit_facts cap O (w.getD j0 false) σ4 e4h
    have s5 : WExec cap (.ifs S (emitW O true) (emitW O false)) σ4 σ5 4 := by
      cases hbv : w.getD j0 false
      · rw [hbv] at hb s5'; exact WExec.ifsF hb s5'
      · rw [hbv] at hb s5'; exact WExec.ifsT hb s5'
    obtain ⟨σ6, s6, a6, a6h, o6, v6, c6⟩ := fwd_facts cap S σ5
    have R6 := ((o3 R hRS).trans' (o4 R hRO)).trans' ((o5 R hRO).trans' (o6 R hRS))
    have S5 := (o4 S hSO).trans' (o5 S hSO)
    have O6 := o6 O hOS
    obtain ⟨τ, s7, eS, eSh, eR, eRh, eO, eOh, oth, v7, c7⟩ := copyLoop_spec S R O hSR hSO hRO M w hwM q k σ6
      (by omega)
      (by rw [a6, S5.1, a3]; simp only [hσ2, hσ1, WState.seth_st, WState.sets_st, Function.update_of_ne hSR]; exact hT)
      (by rw [a6h, S5.2, a3h]; simp only [hσ2, hσ1, WState.seth_sh, WState.sets_sh, Function.update_of_ne hSR]
          rw [hSh]; omega)
      (by rw [R6.1]; simpa [hσ2] using e1)
      (by rw [R6.2]; simp [hσ2, hσ1, hRh])
      (by rw [O6.1, O6.2]; exact e5h)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4
      (WExec.seq s5 s6))))) s7) (by ring_nf; omega), ?_, eSh, eR, eRh, ?_, eOh, ?_, ?_, ?_⟩
    · rw [eS, a6, S5.1, a3]; simp [hσ2, hσ1, Function.update_of_ne hSR]
    · rw [eO, O6.1, e5, e4, O3.1]
      simp only [hσ2, hσ1, WState.seth_st, WState.sets_st, Function.update_of_ne hOR]
      have hd : w.drop (w.length - (k + 1)) = w.getD j0 false :: w.drop (w.length - k) := by
        rw [List.drop_eq_getElem_cons (by omega), List.getD_eq_getElem _ _ hj0w]
        congr 2; omega
      rw [hd, frameP_cons]; simp
    · intro j h1 h2 h3
      have o12 : Same σ σ2 j := ⟨by simp [hσ2, hσ1, Function.update_of_ne h2], by simp [hσ2, hσ1, Function.update_of_ne h2]⟩
      exact ((((o12.trans' (o3 j h1)).trans' (o4 j h3)).trans' (o5 j h3)).trans' (o6 j h1)).trans' (oth j h1 h2 h3)
    · rw [v7, v6, v5, v4, v3]; simp [hσ2, hσ1]
    · rw [c7, c6, c5, c4, c3]; simp [hσ2, hσ1]

/-! ## One field: skip it, or copy its payload -/

/-- The prefix `1^L` of the field at the head of `S`, counted onto the ruler `R`; `S` stops at the payload. -/
def prefW (S R : Fin (ns + 1)) : WM ns nr := .seq (.fwd S) (.seq (.whs S (prefBody S R)) (.fwd S))

/-- **Skip one framed field** `nf x`; the ruler returns to `false`. -/
def skipNatW (S R : Fin (ns + 1)) : WM ns nr := .seq (prefW S R) (.seq (.bwd R) (.whs R (skipBody S R)))

/-- **Copy one framed field's payload** to the end of `O` as `frame (pay x)`; the ruler returns to `false`. -/
def copyNatW (S R O : Fin (ns + 1)) : WM ns nr :=
  .seq (prefW S R) (.seq (.bwd R) (.seq (.whs R (copyBody S R O)) (emitW O false)))

/-- The facts of the prefix pass. -/
theorem prefW_spec (S R : Fin (ns + 1)) (hSR : S ≠ R) (x : ℕ) (pre rest : List Bool) (r : ℕ) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (nf x ++ rest)) (hSh : σ.sh S = pre.length) (hR : σ.st R = List.replicate r false)
    (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (prefW S R) σ τ (natBitLength x * 9 + 5) ∧ τ.st S = σ.st S ∧
      τ.sh S = pre.length + 2 * natBitLength x + 2 ∧ τ.st R = ruler (natBitLength x) (max (natBitLength x) r) ∧
      τ.sh R = natBitLength x ∧ (∀ j, j ≠ S → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hRS : R ≠ S := fun e => hSR e.symm
  unfold nf at hS
  set L := natBitLength x with hL
  obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap S σ
  have R1 := o1 R hRS
  have hlen : L < (natWord x).length := by rw [natWord_len]; omega
  obtain ⟨σ2, s2, e2, e2h, e2R, e2Rh, o2, v2, c2⟩ := prefLoop_spec cap S R hSR pre.length L r L 0 σ1 (by omega)
    (fun j hj => by
      rw [a1, hS]
      have := rd_bit pre (natWord x) rest j (by omega)
      rw [show pre.length + 1 + 2 * j = pre.length + (2 * j + 1) by ring, this]
      exact natWord_getD_one x j hj)
    (by
      rw [a1, hS]
      have := rd_bit pre (natWord x) rest L hlen
      rw [show pre.length + 1 + 2 * L = pre.length + (2 * L + 1) by ring, this]
      exact natWord_getD_zero x)
    (by rw [a1h, hSh])
    (by rw [R1.1, hR, ruler_zero])
    (by rw [R1.2, hRh])
  obtain ⟨τ, s3, a3, a3h, o3, v3, c3⟩ := fwd_facts cap S σ2
  have R3 := o3 R hRS
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a3, e2, a1]
  · rw [a3h, e2h]; omega
  · rw [R3.1, e2R, ruler_max]
  · rw [R3.2, e2Rh]
  · intro j h1 h2; exact ((o1 j h1).trans' (o2 j h1 h2)).trans' (o3 j h1)
  · rw [v3, v2, v1]
  · rw [c3, c2, c1]

theorem skipNatW_spec (S R : Fin (ns + 1)) (hSR : S ≠ R) (x : ℕ) (pre rest : List Bool) (r : ℕ) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (nf x ++ rest)) (hSh : σ.sh S = pre.length) (hR : σ.st R = List.replicate r false)
    (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (skipNatW S R) σ τ (natBitLength x * 18 + 9) ∧ τ.st S = σ.st S ∧
      τ.sh S = pre.length + (nf x).length ∧ τ.st R = List.replicate (max (natBitLength x) r) false ∧
      τ.sh R = 0 ∧ (∀ j, j ≠ S → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  set L := natBitLength x with hL
  obtain ⟨σ1, s1, e1, e1h, e1R, e1Rh, o1, v1, c1⟩ := prefW_spec cap S R hSR x pre rest r σ hS hSh hR hRh
  have s2 := WExec.bwd (cap := cap) R σ1
  set σ2 := σ1.seth R (σ1.sh R - 1) with hσ2
  obtain ⟨τ, s3, e3, e3h, e3R, e3Rh, o3, v3, c3⟩ := skipLoop_spec cap S R hSR (max L r) L σ2 (le_max_left _ _)
    (by simpa [hσ2] using e1R) (by simp [hσ2, e1Rh, hL])
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_, ?_, ?_, e3Rh, ?_, ?_, ?_⟩
  · rw [e3]; simp [hσ2, e1]
  · rw [e3h]; simp only [hσ2, WState.seth_sh]; rw [Function.update_of_ne hSR, e1h, nf_length]; omega
  · rw [e3R, ruler_zero]
  · intro j h1 h2
    exact Same.trans' (o1 j h1 h2) (Same.trans' (show Same σ1 σ2 j from ⟨rfl, by simp [hσ2, Function.update_of_ne h2]⟩)
      (o3 j h1 h2))
  · rw [v3]; simp [hσ2, v1]
  · rw [c3]; simp [hσ2, c1]

theorem copyNatW_spec (S R O : Fin (ns + 1)) (hSR : S ≠ R) (hSO : S ≠ O) (hRO : R ≠ O) (x : ℕ)
    (pre rest : List Bool) (r : ℕ) (σ : WState ns nr)
    (hS : σ.st S = pre ++ (nf x ++ rest)) (hSh : σ.sh S = pre.length) (hR : σ.st R = List.replicate r false)
    (hRh : σ.sh R = 0) (hOh : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (copyNatW S R O) σ τ (natBitLength x * 29 + 13) ∧ τ.st S = σ.st S ∧
      τ.sh S = pre.length + (nf x).length ∧ τ.st R = List.replicate (max (natBitLength x) r) false ∧
      τ.sh R = 0 ∧ τ.st O = σ.st O ++ frame (pay x) ∧ τ.sh O = (τ.st O).length ∧
      (∀ j, j ≠ S → j ≠ R → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hOS : O ≠ S := fun e => hSO e.symm
  have hOR : O ≠ R := fun e => hRO e.symm
  set L := natBitLength x with hL
  obtain ⟨σ1, s1, e1, e1h, e1R, e1Rh, o1, v1, c1⟩ := prefW_spec cap S R hSR x pre rest r σ hS hSh hR hRh
  have O1 := o1 O hOS hOR
  have s2 := WExec.bwd (cap := cap) R σ1
  set σ2 := σ1.seth R (σ1.sh R - 1) with hσ2
  have hpl : (pay x).length = L := pay_length x
  obtain ⟨σ3, s3, e3, e3h, e3R, e3Rh, e3O, e3Oh, o3, v3, c3⟩ := copyLoop_spec cap S R O hSR hSO hRO (max L r) (pay x)
    (by rw [hpl]; exact le_max_left _ _) (pre.length + 2 * L + 2) L σ2 (by omega)
    (fun j hj => by
      simp only [hσ2, WState.seth_st]; rw [e1, hS]; unfold nf
      have := rd_bit pre (natWord x) rest (L + 1 + j) (by rw [natWord_len]; omega)
      rw [show pre.length + 2 * L + 2 + 2 * j + 1 = pre.length + (2 * (L + 1 + j) + 1) by ring, this]
      exact natWord_getD_pay x j)
    (by simp only [hσ2, WState.seth_sh]; rw [Function.update_of_ne hSR, e1h, hpl]; omega)
    (by simpa [hσ2, hpl] using e1R)
    (by simp [hσ2, e1Rh, hpl, hL])
    (by simp only [hσ2, WState.seth_sh, WState.seth_st]; rw [Function.update_of_ne hOR, O1.1, O1.2, hOh])
  obtain ⟨τ, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap O false σ3 e3Oh
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_, ?_, ?_, ?_, e4h,
    ?_, ?_, ?_⟩
  · rw [(o4 S hSO).1, e3]; simp [hσ2, e1]
  · rw [(o4 S hSO).2, e3h, nf_length, hpl]; omega
  · rw [(o4 R hRO).1, e3R, ruler_zero]
  · rw [(o4 R hRO).2, e3Rh]
  · rw [e4, e3O]; simp only [hσ2, WState.seth_st, hpl, Nat.sub_self, List.drop_zero]
    rw [O1.1, frame_eq_frameP, List.append_assoc]
  · intro j h1 h2 h3
    exact Same.trans' (Same.trans' (o1 j h1 h2) (show Same σ1 σ2 j from ⟨rfl, by simp [hσ2, Function.update_of_ne h2]⟩))
      (Same.trans' (o3 j h1 h2 h3) (o4 j h3))
  · rw [v4, v3]; simp [hσ2, v1]
  · rw [c4, c3]; simp [hσ2, c1]

/-! ## The fields of the input -/

theorem frameP_append' (l l' : List Bool) : frameP (l ++ l') = frameP l ++ frameP l' := by
  simp [frameP, List.flatMap_append]

theorem frameP_flatten (ws : List (List Bool)) : frameP ws.flatten = (ws.map frameP).flatten := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [frameP_append', ih]

/-- The input `frame u` of the writer, field by field. -/
theorem frame_fields (xs : List ℕ) : frame (xs.map natWord).flatten = (xs.map nf).flatten ++ [false] := by
  rw [frame_eq_frameP, frameP_flatten, List.map_map]; rfl

theorem fields_split (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    (xs.map nf).flatten = ((xs.take k).map nf).flatten ++ (nf xs[k] ++ ((xs.drop (k + 1)).map nf).flatten) := by
  have e : xs = xs.take k ++ xs[k] :: xs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  calc (xs.map nf).flatten = ((xs.take k ++ xs[k] :: xs.drop (k + 1)).map nf).flatten := by rw [← e]
    _ = _ := by simp only [List.map_append, List.map_cons, List.flatten_append, List.flatten_cons]

theorem fields_take_succ (xs : List ℕ) (k : ℕ) (hk : k < xs.length) :
    ((xs.take (k + 1)).map nf).flatten.length = ((xs.take k).map nf).flatten.length + (nf xs[k]).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.flatten_append,
    List.length_append]
  simp

/-- **Skip `i` fields** along the counter `K` (`1^i 0 …`); the ruler stays `false`. -/
theorem skipNats_spec (S K R : Fin (ns + 1)) (hSK : S ≠ K) (hSR : S ≠ R) (hKR : K ≠ R) (xs : List ℕ) (W : ℕ)
    (hW : ∀ x ∈ xs, natBitLength x ≤ W) (tail : List Bool) (i : ℕ) (hi : i ≤ xs.length) (rest : List Bool) :
    ∀ (d k : ℕ) (σ : WState ns nr) (r : ℕ), k + d = i → σ.st S = (xs.map nf).flatten ++ tail →
      σ.sh S = ((xs.take k).map nf).flatten.length → σ.st K = List.replicate i true ++ (false :: rest) →
      σ.sh K = k → σ.st R = List.replicate r false → σ.sh R = 0 →
      ∃ τ, WExec cap (.whs K (.seq (skipNatW S R) (.fwd K))) σ τ (d * (18 * W + 16) + 1) ∧ τ.st S = σ.st S ∧
        τ.sh S = ((xs.take i).map nf).flatten.length ∧ τ.st K = σ.st K ∧ τ.sh K = i ∧
        (∃ r', τ.st R = List.replicate r' false) ∧ τ.sh R = 0 ∧ (∀ j, j ≠ S → j ≠ K → j ≠ R → Same σ τ j) ∧
        τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, r, hkd, _, hSh, hK, hKh, hR, hRh => by
    have hk : k = i := by omega
    subst hk
    have hz : wbit σ K = false := by
      simp only [wbit, hK, hKh]; have := NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at (List.replicate k true)
        (false :: rest); simpa using this
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hSh, rfl, hKh, ⟨r, hR⟩, hRh, fun _ _ _ _ => ⟨rfl, rfl⟩,
      rfl, rfl⟩
  | d + 1, k, σ, r, hkd, hS, hSh, hK, hKh, hR, hRh => by
    have hk : k < xs.length := by omega
    have hKS : K ≠ S := fun e => hSK e.symm
    have hRK : R ≠ K := fun e => hKR e.symm
    obtain ⟨σ1, s1, e1, e1h, e1R, e1Rh, o1, v1, c1⟩ := skipNatW_spec cap S R hSR xs[k]
      ((xs.take k).map nf).flatten (((xs.drop (k + 1)).map nf).flatten ++ tail) r σ
      (by rw [hS, fields_split xs k hk]; simp) hSh hR hRh
    have K1 := o1 K hKS hKR
    obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap K σ1
    have S2 := o2 S hSK
    have R2 := o2 R hRK
    have hxw : natBitLength xs[k] ≤ W := hW _ (List.getElem_mem hk)
    obtain ⟨τ, s3, eS, eSh, eK, eKh, eR, eRh, oth, v3, c3⟩ := skipNats_spec S K R hSK hSR hKR xs W hW tail i hi rest d
      (k + 1) σ2 (max (natBitLength xs[k]) r) (by omega)
      (by rw [S2.1, e1, hS]) (by rw [S2.2, e1h, fields_take_succ xs k hk])
      (by rw [a2, K1.1, hK]) (by rw [a2h, K1.2, hKh])
      (by rw [R2.1, e1R]) (by rw [R2.2, e1Rh])
    have hki : k < i := by omega
    have hw : wbit σ K = true := by
      simp only [wbit, hK, hKh]
      unfold readTapeBit; rw [List.getD_append _ _ _ _ (by simp; omega)]; simp [hki]
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, ?_, eSh, ?_, eKh, eR, eRh, ?_, ?_, ?_⟩
    · have : (d + 1) * (18 * W + 16) = d * (18 * W + 16) + (18 * W + 16) := by ring
      omega
    · rw [eS, S2.1, e1]
    · rw [eK, a2, K1.1]
    · intro j h1 h2 h3; exact ((o1 j h1 h3).trans' (o2 j h2)).trans' (oth j h1 h2 h3)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

/-! ## The field counter and the input's length -/

/-- One counted field: skip it, one more cell of the count. -/
theorem countLoop_spec (S C R : Fin (ns + 1)) (hSC : S ≠ C) (hSR : S ≠ R) (hCR : C ≠ R) (xs : List ℕ) (W : ℕ)
    (hW : ∀ x ∈ xs, natBitLength x ≤ W) :
    ∀ (d k : ℕ) (σ : WState ns nr) (r : ℕ), k + d = xs.length →
      σ.st S = (xs.map nf).flatten ++ [false] → σ.sh S = ((xs.take k).map nf).flatten.length →
      σ.st C = false :: List.replicate k true → σ.sh C = k + 1 → σ.st R = List.replicate r false → σ.sh R = 0 →
      ∃ τ, WExec cap (.whs S (.seq (skipNatW S R) (emitW C true))) σ τ (d * (18 * W + 16) + 1) ∧
        τ.st S = σ.st S ∧ τ.st C = false :: List.replicate xs.length true ∧ (∃ r', τ.st R = List.replicate r' false) ∧
        (∀ j, j ≠ S → j ≠ C → j ≠ R → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, r, hkd, hS, hSh, hC, _, hR, _ => by
    have hk : k = xs.length := by omega
    subst hk
    have hz : wbit σ S = false := by
      simp only [wbit, hS, hSh, List.take_length]
      have := NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at ((xs.map nf).flatten) [false]; simpa using this
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hC, ⟨r, hR⟩, fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | d + 1, k, σ, r, hkd, hS, hSh, hC, hCh, hR, hRh => by
    have hk : k < xs.length := by omega
    have hCS : C ≠ S := fun e => hSC e.symm
    have hRC : R ≠ C := fun e => hCR e.symm
    have hsplit := fields_split xs k hk
    obtain ⟨σ1, s1, e1, e1h, e1R, e1Rh, o1, v1, c1⟩ := skipNatW_spec cap S R hSR xs[k]
      ((xs.take k).map nf).flatten (((xs.drop (k + 1)).map nf).flatten ++ [false]) r σ
      (by rw [hS, hsplit]; simp) hSh hR hRh
    have C1 := o1 C hCS hCR
    obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := emit_facts cap C true σ1 (by rw [C1.1, C1.2, hC, hCh]; simp)
    have S2 := o2 S hSC
    have R2 := o2 R hRC
    have hxw : natBitLength xs[k] ≤ W := hW _ (List.getElem_mem hk)
    obtain ⟨τ, s3, eS, eC, eR, oth, v3, c3⟩ := countLoop_spec S C R hSC hSR hCR xs W hW d (k + 1) σ2
      (max (natBitLength xs[k]) r) (by omega)
      (by rw [S2.1, e1, hS]) (by rw [S2.2, e1h, fields_take_succ xs k hk])
      (by rw [a2, C1.1, hC, List.replicate_succ', List.cons_append]) (by rw [a2h, a2, C1.1, hC]; simp)
      (by rw [R2.1, e1R]) (by rw [R2.2, e1Rh])
    have hw : wbit σ S = true := by
      simp only [wbit, hS, hSh, hsplit, List.append_assoc]
      have := rd_mark ((xs.take k).map nf).flatten (natWord xs[k])
        (((xs.drop (k + 1)).map nf).flatten ++ [false]) 0 (by rw [natWord_len]; omega)
      simpa [nf] using this
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, ?_, eC, eR, ?_, ?_, ?_⟩
    · have : (d + 1) * (18 * W + 16) = d * (18 * W + 16) + (18 * W + 16) := by ring
      omega
    · rw [eS, S2.1, e1]
    · intro j h1 h2 h3; exact ((o1 j h1 h3).trans' (o2 j h2)).trans' (oth j h1 h2 h3)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

/-- One cell pair of `frame u`: one cell of the ruler `1^|u|`. -/
theorem lenLoop_spec (S X : Fin (ns + 1)) (hSX : S ≠ X) (u : List Bool) :
    ∀ (d k : ℕ) (σ : WState ns nr), k + d = u.length → σ.st S = frame u → σ.sh S = 2 * k →
      σ.st X = List.replicate k true → σ.sh X = k →
      ∃ τ, WExec cap (.whs S (.seq (.fwd S) (.seq (.fwd S) (emitW X true)))) σ τ (d * 9 + 1) ∧
        τ.st S = σ.st S ∧ τ.st X = List.replicate u.length true ∧ (∀ j, j ≠ S → j ≠ X → Same σ τ j) ∧
        τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, hkd, hS, hSh, hX, _ => by
    have hk : k = u.length := by omega
    subst hk
    have hz : wbit σ S = false := by
      simp only [wbit, hS, hSh, frame_eq_frameP]
      have := NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at (frameP u) [false]; simpa using this
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hX, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | d + 1, k, σ, hkd, hS, hSh, hX, hXh => by
    have hXS : X ≠ S := fun e => hSX e.symm
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap S σ
    obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap S σ1
    have X2 := (o1 X hXS).trans' (o2 X hXS)
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap X true σ2 (by rw [X2.1, X2.2, hX, hXh]; simp)
    have S3 := o3 S hSX
    obtain ⟨τ, s4, eS, eX, oth, v4, c4⟩ := lenLoop_spec S X hSX u d (k + 1) σ3 (by omega)
      (by rw [S3.1, a2, a1, hS]) (by rw [S3.2, a2h, a1h, hSh]; ring)
      (by rw [e3, X2.1, hX, List.replicate_succ']) (by rw [e3h, e3, X2.1, hX]; simp)
    have hw : wbit σ S = true := by
      simp only [wbit, hS, hSh, frame_eq_frameP]
      have := rd_mark [] u [false] k (by omega); simpa using this
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4) (by ring_nf; omega), ?_, eX, ?_, ?_, ?_⟩
    · rw [eS, S3.1, a2, a1]
    · intro j h1 h2; exact (((o1 j h1).trans' (o2 j h1)).trans' (o3 j h2)).trans' (oth j h1 h2)
    · rw [v4, v3, v2, v1]
    · rw [c4, c3, c2, c1]

/-! ## Lists of framed words -/

theorem rd_frame_head (pre w rest : List Bool) (hw : w ≠ []) : readTapeBit (pre ++ (frame w ++ rest)) pre.length = true := by
  rw [NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at]
  cases w with
  | nil => exact absurd rfl hw
  | cons b w => rfl

/-- **Skip a list of nonempty framed words** (the stream ends after them). -/
theorem skipWords_spec (X : Fin (ns + 1)) :
    ∀ (ws : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ w ∈ ws, w ≠ []) →
      σ.st X = pre ++ ws.flatMap frame → σ.sh X = pre.length →
      WExec cap (.whs X (NearCubicWires.WireExponent3_5.PrimT.skipFrameW X)) σ
        (σ.seth X (pre.length + (ws.flatMap frame).length)) (6 * (ws.flatMap frame).length + 1)
  | [], pre, σ, _, hX, hXh => by
    have hz : wbit σ X = false := by
      simp only [wbit, hX, hXh, List.flatMap_nil, List.append_nil]
      unfold readTapeBit; simp
    have e : σ.seth X (pre.length + (([] : List (List Bool)).flatMap frame).length) = σ := by
      simp only [List.flatMap_nil, List.length_nil, Nat.add_zero, ← hXh, NearCubicWires.WireExponent3_5.FinalPass.Tm.wseth_same]
    rw [e]; exact WExec.mono (WExec.whsF hz) (by omega)
  | w :: ws, pre, σ, hne, hX, hXh => by
    have hw : w ≠ [] := hne w (by simp)
    have s1 := NearCubicWires.WireExponent3_5.PrimT.skipFrame_spec cap X pre (ws.flatMap frame) w σ
      (by rw [hX, List.flatMap_cons]) hXh
    have ih := skipWords_spec X ws (pre ++ frame w) (σ.seth X (pre.length + (frame w).length))
      (fun v hv => hne v (by simp [hv])) (by simp [hX, List.flatMap_cons]) (by simp)
    rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.wseth_seth] at ih
    have hr : wbit σ X = true := by
      simp only [wbit, hX, hXh, List.flatMap_cons]; exact rd_frame_head pre w _ hw
    have hl : ((w :: ws).flatMap frame).length = (frame w).length + (ws.flatMap frame).length := by
      rw [List.flatMap_cons, List.length_append]
    rw [hl]
    rw [show (pre ++ frame w).length + (ws.flatMap frame).length = pre.length + ((frame w).length +
      (ws.flatMap frame).length) by simp; omega] at ih
    have hfl : (frame w).length = 2 * w.length + 1 := by rw [frame_eq_frameP]; simp
    exact WExec.mono (WExec.whsT hr s1 ih) (by rw [hfl] at *; omega)

/-- **Copy a list of nonempty framed words** to the end of `O`. -/
theorem copyWords_spec (N O : Fin (ns + 1)) (hNO : N ≠ O) :
    ∀ (ws : List (List Bool)) (pre : List Bool) (σ : WState ns nr), (∀ w ∈ ws, w ≠ []) →
      σ.st N = pre ++ ws.flatMap frame → σ.sh N = pre.length → σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (.whs N (.seq (NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrameW N O) (.fwd N))) σ τ
          (9 * (ws.flatMap frame).length + 1) ∧ τ.st O = σ.st O ++ ws.flatMap frame ∧ τ.sh O = (τ.st O).length ∧
        τ.st N = σ.st N ∧ (∀ j, j ≠ N → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], pre, σ, _, hN, hNh, hO => by
    have hz : wbit σ N = false := by
      simp only [wbit, hN, hNh, List.flatMap_nil, List.append_nil]
      unfold readTapeBit; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hO, rfl, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | w :: ws, pre, σ, hne, hN, hNh, hO => by
    have hw : w ≠ [] := hne w (by simp)
    have hON : O ≠ N := fun e => hNO e.symm
    obtain ⟨σ1, s1, e1, e1h, n1, n1h, o1, v1, c1⟩ := NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrame_spec cap
      N O hNO pre w (ws.flatMap frame) σ (by rw [hN, List.flatMap_cons]) hNh hO
    obtain ⟨σ2, s2, a2, a2h, o2, v2, c2⟩ := fwd_facts cap N σ1
    have O2 := o2 O hON
    have hfl : (frame w).length = 2 * w.length + 1 := by rw [frame_eq_frameP]; simp
    obtain ⟨τ, s3, e3, e3h, n3, o3, v3, c3⟩ := copyWords_spec N O hNO ws (pre ++ frame w) σ2
      (fun v hv => hne v (by simp [hv])) (by rw [a2, n1, hN, List.flatMap_cons, List.append_assoc])
      (by rw [a2h, n1h, List.length_append, hfl]; omega) (by rw [O2.1, O2.2, e1h])
    have hr : wbit σ N = true := by
      simp only [wbit, hN, hNh, List.flatMap_cons]; exact rd_frame_head pre w _ hw
    have hl : ((w :: ws).flatMap frame).length = (frame w).length + (ws.flatMap frame).length := by
      rw [List.flatMap_cons, List.length_append]
    refine ⟨τ, WExec.mono (WExec.whsT hr (WExec.seq s1 s2) s3) (by rw [hl, hfl]; omega), ?_, e3h,
      by rw [n3, a2, n1], ?_, ?_, ?_⟩
    · rw [e3, O2.1, e1, List.flatMap_cons, List.append_assoc]
    · intro j h1 h2; exact ((o1 j h1 h2).trans' (o2 j h1)).trans' (o3 j h1 h2)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

/-- Walk over `1^n` (from its first cell). -/
theorem onesSkip_spec (X : Fin (ns + 1)) (pre : List Bool) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.st X = pre ++ List.replicate n true → σ.sh X = pre.length →
      WExec cap (.whs X (.fwd X)) σ (σ.seth X (pre.length + n)) (3 * n + 1)
  | 0, σ, hX, hXh => by
    have hz : wbit σ X = false := by simp only [wbit, hX, hXh]; unfold readTapeBit; simp
    rw [show pre.length + 0 = σ.sh X by omega, NearCubicWires.WireExponent3_5.FinalPass.Tm.wseth_same]
    exact WExec.mono (WExec.whsF hz) (by omega)
  | n + 1, σ, hX, hXh => by
    have hr : wbit σ X = true := by
      simp only [wbit, hX, hXh, NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at]; simp [List.replicate_succ]
    have s1 := WExec.fwd (cap := cap) X σ
    have ih := onesSkip_spec X (pre ++ [true]) n (σ.seth X (σ.sh X + 1))
      (by simp [hX, List.replicate_succ]) (by simp [hXh])
    rw [NearCubicWires.WireExponent3_5.FinalPass.Tm.wseth_seth,
      show (pre ++ [true]).length + n = pre.length + (n + 1) by simp; omega] at ih
    exact WExec.mono (WExec.whsT hr s1 ih) (by omega)

/-- One `1` of `C` copied to the end of `O`, per cell of `1^k`. -/
theorem onesCopy_spec (C O : Fin (ns + 1)) (hCO : C ≠ O) (pre : List Bool) :
    ∀ (k : ℕ) (σ : WState ns nr), σ.st C = pre ++ List.replicate k true → σ.sh C = pre.length →
      σ.sh O = (σ.st O).length →
      ∃ τ, WExec cap (.whs C (.seq (.fwd C) (emitW O true))) σ τ (7 * k + 1) ∧ τ.st O = σ.st O ++ List.replicate k true ∧
        τ.sh O = (τ.st O).length ∧ τ.st C = σ.st C ∧ (∀ j, j ≠ C → j ≠ O → Same σ τ j) ∧ τ.val = σ.val ∧
        τ.cell = σ.cell
  | 0, σ, hC, hCh, hO => by
    have hz : wbit σ C = false := by simp only [wbit, hC, hCh]; unfold readTapeBit; simp
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), by simp, hO, rfl, fun _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | k + 1, σ, hC, hCh, hO => by
    have hOC : O ≠ C := fun e => hCO e.symm
    have hr : wbit σ C = true := by
      simp only [wbit, hC, hCh, NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at]; simp [List.replicate_succ]
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap C σ
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O true σ1 (by rw [(o1 O hOC).1, (o1 O hOC).2, hO])
    have C2 := o2 C hCO
    obtain ⟨τ, s3, e3, e3h, n3, o3, v3, c3⟩ := onesCopy_spec C O hCO (pre ++ [true]) k σ2
      (by rw [C2.1, a1, hC]; simp [List.replicate_succ]) (by rw [C2.2, a1h, hCh]; simp) e2h
    refine ⟨τ, WExec.mono (WExec.whsT hr (WExec.seq s1 s2) s3) (by omega), ?_, e3h, by rw [n3, C2.1, a1], ?_, ?_, ?_⟩
    · rw [e3, e2, (o1 O hOC).1, List.append_assoc]; simp [List.replicate_succ]
    · intro j h1 h2; exact ((o1 j h1).trans' (o2 j h2)).trans' (o3 j h1 h2)
    · rw [v3, v2, v1]
    · rw [c3, c2, c1]

end Words

/-! ## The programs -/

/-- **The loop-A crop** (streams `0` the fields, `1` the round counter, `2` the payload, `3` the ruler, `4` the
header's constant): skip `i` fields, copy field `i`'s payload, advance the counter in place, write `frame []`. -/
def cropAW : WM 4 0 :=
  .seq (.whs 1 (.seq (skipNatW 0 3) (.fwd 1))) (.seq (copyNatW 0 3 2) (.seq (.wr 1 true) (emitW 4 false)))

/-- **The circuit count** (streams `0` the input, `1` the count word, `2` the ruler). -/
def countW : WM 2 0 := .seq (emitW 1 false) (.whs 0 (.seq (skipNatW 0 2) (emitW 1 true)))

/-- **The input's length in unary** (streams `0` the input, `1` the ruler `1^|u|`). -/
def lenW : WM 1 0 := .whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (emitW 1 true)))

def cropACost (i W : ℕ) : ℕ := i * (18 * W + 16) + 29 * W + 25

theorem cropAW_spec (cap : ℕ) (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (tail : List Bool) (i : ℕ)
    (hi : i < xs.length) (rest : List Bool) (σ : WState 4 0) (h0 : ∀ j, σ.sh j = 0)
    (hS : σ.st 0 = (xs.map nf).flatten ++ tail) (hK : σ.st 1 = List.replicate i true ++ (false :: rest))
    (hO : σ.st 2 = []) (hR : σ.st 3 = []) (hZ : σ.st 4 = []) :
    ∃ τ, WExec cap cropAW σ τ (cropACost i W) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = List.replicate (i + 1) true ++ rest ∧
      τ.st 2 = frame (pay xs[i]) ∧ (∃ r, τ.st 3 = List.replicate r false) ∧ τ.st 4 = [false] ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, s1, e1, e1h, e1K, e1Kh, ⟨r1, e1R⟩, e1Rh, o1, v1, c1⟩ := skipNats_spec cap (0 : Fin 5) 1 3
    (by decide) (by decide) (by decide) xs W hW tail i hi.le rest i 0 σ 0 (by omega) hS (by simp [h0]) hK (h0 1)
    (by rw [hR]; rfl) (h0 3)
  have O1 := o1 2 (by decide) (by decide) (by decide)
  have Z1 := o1 4 (by decide) (by decide) (by decide)
  obtain ⟨τ2, s2, e2, e2h, e2R, e2Rh, e2O, e2Oh, o2, v2, c2⟩ := copyNatW_spec cap (0 : Fin 5) 3 2 (by decide)
    (by decide) (by decide) xs[i] ((xs.take i).map nf).flatten (((xs.drop (i + 1)).map nf).flatten ++ tail) r1 τ1
    (by rw [e1, hS, fields_split xs i hi]; simp) e1h e1R e1Rh (by rw [O1.1, O1.2, hO, h0]; rfl)
  have K2 := o2 1 (by decide) (by decide) (by decide)
  have Z2 := o2 4 (by decide) (by decide) (by decide)
  have s3 := WExec.wr (cap := cap) (1 : Fin 5) true τ2
  set τ3 := τ2.sets 1 (writeTapeBit (τ2.st 1) (τ2.sh 1) true) with hτ3
  obtain ⟨τ, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (4 : Fin 5) false τ3 (by
    simp only [hτ3, WState.sets_st, WState.sets_sh]; rw [Function.update_of_ne (by decide), Z2.1, Z2.2, Z1.1, Z1.2, hZ,
      h0]; rfl)
  have hxw : natBitLength xs[i] ≤ W := hW _ (List.getElem_mem hi)
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by unfold cropACost; omega), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [(o4 0 (by decide)).1]; simp only [hτ3, WState.sets_st]; rw [Function.update_of_ne (by decide), e2, e1]
  · rw [(o4 1 (by decide)).1]; simp only [hτ3, WState.sets_st, Function.update_self]
    rw [K2.1, K2.2, e1K, e1Kh, hK, NearCubicWires.WireExponent3_5.PrimT.CarWM.write_counter]
  · rw [(o4 2 (by decide)).1]; simp only [hτ3, WState.sets_st]; rw [Function.update_of_ne (by decide), e2O, O1.1, hO]
    rfl
  · refine ⟨max (natBitLength xs[i]) r1, ?_⟩
    rw [(o4 3 (by decide)).1]; simp only [hτ3, WState.sets_st]; rw [Function.update_of_ne (by decide), e2R]
  · rw [e4]; simp only [hτ3, WState.sets_st]; rw [Function.update_of_ne (by decide), Z2.1, Z1.1, hZ]; rfl
  · rw [c4]; simp only [hτ3, WState.sets_cell]; rw [c2, c1]

theorem countW_spec (cap : ℕ) (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (σ : WState 2 0)
    (h0 : ∀ j, σ.sh j = 0) (hS : σ.st 0 = frame (xs.map natWord).flatten) (hC : σ.st 1 = []) (hR : σ.st 2 = []) :
    ∃ τ, WExec cap countW σ τ (xs.length * (18 * W + 16) + 5) ∧ τ.st 0 = σ.st 0 ∧
      τ.st 1 = false :: List.replicate xs.length true ∧ (∃ r, τ.st 2 = List.replicate r false) ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (1 : Fin 3) false σ (by rw [hC, h0]; rfl)
  have S1 := o1 0 (by decide)
  have R1 := o1 2 (by decide)
  obtain ⟨τ, s2, eS, eC, eR, oth, v2, c2⟩ := countLoop_spec cap (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    xs W hW xs.length 0 τ1 0 (by omega) (by rw [S1.1, hS, frame_fields]) (by rw [S1.2, h0]; rfl)
    (by rw [e1, hC]; rfl) (by rw [e1h, e1, hC]; rfl) (by rw [R1.1, hR]; rfl) (by rw [R1.2, h0])
  exact ⟨τ, WExec.mono (WExec.seq s1 s2) (by omega), by rw [eS, S1.1], eC, eR, by rw [c2, c1]⟩

theorem lenW_spec (cap : ℕ) (u : List Bool) (σ : WState 1 0) (h0 : ∀ j, σ.sh j = 0) (hS : σ.st 0 = frame u)
    (hX : σ.st 1 = []) :
    ∃ τ, WExec cap lenW σ τ (u.length * 9 + 1) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = List.replicate u.length true ∧
      τ.cell = σ.cell := by
  obtain ⟨τ, s, eS, eX, -, -, c⟩ := lenLoop_spec cap (0 : Fin 2) 1 (by decide) u u.length 0 σ (by omega) hS
    (by rw [h0]) (by rw [hX]; rfl) (h0 1)
  exact ⟨τ, s, eS, eX, c⟩

/-! ## The programs as Steps -/

open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT (wm_step wenc_H_zero)

/-- The crop's entry state. -/
def σA (S K : List Bool) : WState 4 0 := ⟨fun _ => 0, ![S, K, [], [], []], fun r => r.elim0, false⟩

/-- The crop's entry bank: the fields, the cell, the counter, three blank streams, the log. -/
def cropAIn (S K : List Bool) : Fin 7 → List Bool :=
  Fin.addCases (m := 4 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σA S K)).A (fun _ => [])

theorem cropAIn_val (S K : List Bool) (j : Fin 7) :
    cropAIn S K j = if j.val = 0 then S else if j.val = 1 then [false] else if j.val = 2 then K else [] := by
  fin_cases j <;> rfl

/-- **The loop-A crop as a Step.** -/
theorem cropAStage (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) (tail : List Bool) (i : ℕ)
    (hi : i < xs.length) (rest : List Bool) : ∃ o : Fin 7 → List Bool,
    Step (Rewind.machine cropAW.toProg.compile) (2 * cropACost i W + 2) (fun _ => 0)
      (cropAIn ((xs.map nf).flatten ++ tail) (List.replicate i true ++ (false :: rest))) (fun _ => 0) o ∧
    o 0 = (xs.map nf).flatten ++ tail ∧ o 1 = [false] ∧ o 2 = List.replicate (i + 1) true ++ rest ∧
    o 3 = frame (pay xs[i]) ∧ (∃ r, o 4 = List.replicate r false) ∧ o 5 = [false] := by
  set σ := σA ((xs.map nf).flatten ++ tail) (List.replicate i true ++ (false :: rest)) with hσ
  obtain ⟨τ, hw, e0, e1, e2, ⟨r, e3⟩, e4, ec⟩ := cropAW_spec 0 xs W hW tail i hi rest σ (fun _ => rfl) rfl rfl rfl rfl
    rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 cropAW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ⟨r, ?_⟩, ?_⟩
  · rw [show (0 : Fin 7) = Fin.castAdd 1 (0 : Fin 6) from rfl, ho]; exact e0
  · rw [show (1 : Fin 7) = Fin.castAdd 1 (1 : Fin 6) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 7) = Fin.castAdd 1 (2 : Fin 6) from rfl, ho]; exact e1
  · rw [show (3 : Fin 7) = Fin.castAdd 1 (3 : Fin 6) from rfl, ho]; exact e2
  · rw [show (4 : Fin 7) = Fin.castAdd 1 (4 : Fin 6) from rfl, ho]; exact e3
  · rw [show (5 : Fin 7) = Fin.castAdd 1 (5 : Fin 6) from rfl, ho]; exact e4

def σC (S : List Bool) : WState 2 0 := ⟨fun _ => 0, ![S, [], []], fun r => r.elim0, false⟩

/-- The count's entry bank: the input, the cell, two blank streams, the log. -/
def countIn (S : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σC S)).A (fun _ => [])

theorem countIn_val (S : List Bool) (j : Fin 5) :
    countIn S j = if j.val = 0 then S else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

/-- **The circuit count as a Step**: `false :: 1^c` on tape `2`. -/
theorem countStage (xs : List ℕ) (W : ℕ) (hW : ∀ x ∈ xs, natBitLength x ≤ W) : ∃ o : Fin 5 → List Bool,
    Step (Rewind.machine countW.toProg.compile) (2 * (xs.length * (18 * W + 16) + 5) + 2) (fun _ => 0)
      (countIn (frame (xs.map natWord).flatten)) (fun _ => 0) o ∧
    o 0 = frame (xs.map natWord).flatten ∧ o 1 = [false] ∧ o 2 = false :: List.replicate xs.length true ∧
    (∃ r, o 3 = List.replicate r false) := by
  set σ := σC (frame (xs.map natWord).flatten) with hσ
  obtain ⟨τ, hw, e0, e1, ⟨r, e2⟩, ec⟩ := countW_spec 0 xs W hW σ (fun _ => rfl) rfl rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 countW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ⟨r, ?_⟩⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 5) = Fin.castAdd 1 (2 : Fin 4) from rfl, ho]; exact e1
  · rw [show (3 : Fin 5) = Fin.castAdd 1 (3 : Fin 4) from rfl, ho]; exact e2

def σL (S : List Bool) : WState 1 0 := ⟨fun _ => 0, ![S, []], fun r => r.elim0, false⟩

/-- The length pass's entry bank: the input, the cell, a blank stream, the log. -/
def lenIn (S : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (m := 1 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σL S)).A (fun _ => [])

theorem lenIn_val (S : List Bool) (j : Fin 4) :
    lenIn S j = if j.val = 0 then S else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

/-- **The input's length as a Step**: `1^|u|` on tape `2`. -/
theorem lenStage (u : List Bool) : ∃ o : Fin 4 → List Bool,
    Step (Rewind.machine lenW.toProg.compile) (2 * (u.length * 9 + 1) + 2) (fun _ => 0) (lenIn (frame u)) (fun _ => 0) o ∧
    o 0 = frame u ∧ o 1 = [false] ∧ o 2 = List.replicate u.length true := by
  set σ := σL (frame u) with hσ
  obtain ⟨τ, hw, e0, e1, ec⟩ := lenW_spec 0 u σ (fun _ => rfl) rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 lenW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 1 (0 : Fin 3) from rfl, ho]; exact e0
  · rw [show (1 : Fin 4) = Fin.castAdd 1 (1 : Fin 3) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 4) = Fin.castAdd 1 (2 : Fin 3) from rfl, ho]; exact e1

/-! ## Loop A's append: the circuit's bottoms and their count -/

/-- **The append** (streams `0` the traversal's atoms, `1` its count word, `2` the bottom accumulator, `3` the
count accumulator): every atom's framed word to the end of `2`, one `1` per atom to the end of `3`. -/
def appendAW : WM 3 0 :=
  .seq (.whs 2 (NearCubicWires.WireExponent3_5.PrimT.skipFrameW 2))
    (.seq (.whs 0 (.seq (NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrameW 0 2) (.fwd 0)))
      (.seq (.fwd 3) (.seq (.whs 3 (.fwd 3)) (.seq (.fwd 1) (.whs 1 (.seq (.fwd 1) (emitW 3 true)))))))

def appendACost (as bs : List (List Bool)) (k n : ℕ) : ℕ :=
  6 * (bs.flatMap frame).length + 9 * (as.flatMap frame).length + 3 * n + 7 * k + 14

theorem appendAW_spec (cap : ℕ) (as bs : List (List Bool)) (has : ∀ a ∈ as, a ≠ []) (hbs : ∀ b ∈ bs, b ≠ [])
    (k n : ℕ) (σ : WState 3 0) (h0 : ∀ j, σ.sh j = 0) (hA : σ.st 0 = as.flatMap frame)
    (hC : σ.st 1 = false :: List.replicate k true) (hB : σ.st 2 = bs.flatMap frame)
    (hN : σ.st 3 = false :: List.replicate n true) :
    ∃ τ, WExec cap appendAW σ τ (appendACost as bs k n) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = σ.st 1 ∧
      τ.st 2 = (bs ++ as).flatMap frame ∧ τ.st 3 = false :: List.replicate (n + k) true ∧ τ.cell = σ.cell := by
  have s1 := skipWords_spec cap (2 : Fin 4) bs [] σ hbs (by rw [hB]; rfl) (by rw [h0]; rfl)
  set σ1 := σ.seth 2 ([].length + (bs.flatMap frame).length) with hσ1
  obtain ⟨σ2, s2, e2, e2h, n2, o2, v2, c2⟩ := copyWords_spec cap (0 : Fin 4) 2 (by decide) as [] σ1 has
    (by simp [hσ1, hA]) (by simp [hσ1, h0]) (by simp [hσ1, hB])
  obtain ⟨σ3, s3, a3, a3h, o3, v3, c3⟩ := fwd_facts cap (3 : Fin 4) σ2
  have N2 := o2 3 (by decide) (by decide)
  have s4 := onesSkip_spec cap (3 : Fin 4) [false] n σ3 (by rw [a3, N2.1]; simp [hσ1, hN])
    (by rw [a3h, N2.2]; simp [hσ1, h0])
  set σ4 := σ3.seth 3 ([false].length + n) with hσ4
  obtain ⟨σ5, s5, a5, a5h, o5, v5, c5⟩ := fwd_facts cap (1 : Fin 4) σ4
  have C3 := o3 1 (by decide)
  have C2 := o2 1 (by decide) (by decide)
  obtain ⟨τ, s6, e6, e6h, n6, o6, v6, c6⟩ := onesCopy_spec cap (1 : Fin 4) 3 (by decide) [false] k σ5
    (by rw [a5]; simp [hσ4, C3.1, C2.1, hσ1, hC]) (by rw [a5h]; simp [hσ4, C3.2, C2.2, hσ1, h0])
    (by rw [(o5 3 (by decide)).1, (o5 3 (by decide)).2]; simp [hσ4, a3, N2.1, hσ1, hN]; omega)
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 s6))))) (by
    unfold appendACost; simp; omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [(o6 0 (by decide) (by decide)).1, (o5 0 (by decide)).1]; simp [hσ4, (o3 0 (by decide)).1, n2, hσ1]
  · rw [n6, a5]; simp [hσ4, C3.1, C2.1, hσ1]
  · rw [(o6 2 (by decide) (by decide)).1, (o5 2 (by decide)).1]; simp [hσ4, (o3 2 (by decide)).1, e2, hσ1, hB]
  · rw [e6, (o5 3 (by decide)).1]; simp only [hσ4, WState.seth_st, a3, N2.1, hσ1, hN]
    rw [List.replicate_add]; simp
  · rw [c6, c5]; simp [hσ4, c3, c2, hσ1]

def σAp (A C B N : List Bool) : WState 3 0 := ⟨fun _ => 0, ![A, C, B, N], fun r => r.elim0, false⟩

/-- The append's entry bank: the atoms, the cell, the count word, the two accumulators, the log. -/
def appendAIn (A C B N : List Bool) : Fin 6 → List Bool :=
  Fin.addCases (m := 3 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σAp A C B N)).A (fun _ => [])

theorem appendAIn_val (A C B N : List Bool) (j : Fin 6) :
    appendAIn A C B N j = if j.val = 0 then A else if j.val = 1 then [false] else if j.val = 2 then C else
      if j.val = 3 then B else if j.val = 4 then N else [] := by
  fin_cases j <;> rfl

/-- **Loop A's append as a Step.** -/
theorem appendAStage (as bs : List (List Bool)) (has : ∀ a ∈ as, a ≠ []) (hbs : ∀ b ∈ bs, b ≠ []) (k n : ℕ) :
    ∃ o : Fin 6 → List Bool,
    Step (Rewind.machine appendAW.toProg.compile) (2 * appendACost as bs k n + 2) (fun _ => 0)
      (appendAIn (as.flatMap frame) (false :: List.replicate k true) (bs.flatMap frame)
        (false :: List.replicate n true)) (fun _ => 0) o ∧
    o 0 = as.flatMap frame ∧ o 1 = [false] ∧ o 2 = false :: List.replicate k true ∧ o 3 = (bs ++ as).flatMap frame ∧
    o 4 = false :: List.replicate (n + k) true := by
  set σ := σAp (as.flatMap frame) (false :: List.replicate k true) (bs.flatMap frame) (false :: List.replicate n true)
    with hσ
  obtain ⟨τ, hw, e0, e1, e2, e3, ec⟩ := appendAW_spec 0 as bs has hbs k n σ (fun _ => rfl) rfl rfl rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 appendAW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 6) = Fin.castAdd 1 (0 : Fin 5) from rfl, ho]; exact e0
  · rw [show (1 : Fin 6) = Fin.castAdd 1 (1 : Fin 5) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 6) = Fin.castAdd 1 (2 : Fin 5) from rfl, ho]; exact e1
  · rw [show (3 : Fin 6) = Fin.castAdd 1 (3 : Fin 5) from rfl, ho]; exact e2
  · rw [show (4 : Fin 6) = Fin.castAdd 1 (4 : Fin 5) from rfl, ho]; exact e3

/-! ## Loop B: the crop of bottom `j` (widths at most `W`) and the append of its atom code -/

section LoopB
variable {ns nr : ℕ} (cap : ℕ)

/-- **Skip `i` framed words** along the counter `K`, each of width at most `W`. -/
theorem skipAtomsLe_spec (S K : Fin (ns + 1)) (hSK : S ≠ K) (W : ℕ) (ys : List (List Bool))
    (hys : ∀ y ∈ ys, y.length ≤ W) (tail : List Bool) (i : ℕ) (hi : i ≤ ys.length) (rest : List Bool) :
    ∀ (d k : ℕ) (σ : WState ns nr), k + d = i → σ.st S = ys.flatMap frame ++ tail →
      σ.sh S = ((ys.take k).flatMap frame).length → σ.st K = List.replicate i true ++ (false :: rest) →
      σ.sh K = k →
      ∃ τ, WExec cap (.whs K (.seq (NearCubicWires.WireExponent3_5.PrimT.skipFrameW S) (.fwd K))) σ τ
          (d * (5 * W + 8) + 1) ∧ τ.st = σ.st ∧ τ.sh S = ((ys.take i).flatMap frame).length ∧ τ.sh K = i ∧
        (∀ j, j ≠ S → j ≠ K → τ.sh j = σ.sh j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, hkd, hS, hSh, hK, hKh => by
    have hk : k = i := by omega
    subst hk
    have hz : wbit σ K = false := by
      simp only [wbit, hK, hKh]
      have := NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at (List.replicate k true) (false :: rest); simpa using this
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hSh, hKh, fun _ _ _ => rfl, rfl, rfl⟩
  | d + 1, k, σ, hkd, hS, hSh, hK, hKh => by
    have hk : k < ys.length := by omega
    have hKS : K ≠ S := fun e => hSK e.symm
    have s1 := NearCubicWires.WireExponent3_5.PrimT.skipFrame_spec cap S ((ys.take k).flatMap frame)
      ((ys.drop (k + 1)).flatMap frame ++ tail) ys[k] σ
      (by rw [hS, NearCubicWires.WireExponent3_5.PrimT.CarWM.flatMap_split ys k hk]; simp) hSh
    set σ1 := σ.seth S (((ys.take k).flatMap frame).length + (frame ys[k]).length) with hσ1
    have s2 := WExec.fwd (cap := cap) K σ1
    set σ2 := σ1.seth K (σ1.sh K + 1) with hσ2
    have hlen : ys[k].length ≤ W := hys _ (List.getElem_mem hk)
    obtain ⟨τ, s3, est, eS, eK, oth, ev, ec⟩ := skipAtomsLe_spec S K hSK W ys hys tail i hi rest d (k + 1) σ2
      (by omega) (by simp [hσ2, hσ1, hS])
      (by simp only [hσ2, hσ1, WState.seth_sh]; rw [Function.update_of_ne hSK, Function.update_self,
        NearCubicWires.WireExponent3_5.PrimT.CarWM.take_succ_len ys k hk])
      (by simp [hσ2, hσ1, hK])
      (by simp only [hσ2, hσ1, WState.seth_sh]; rw [Function.update_self, Function.update_of_ne hKS, hKh])
    have hki : k < i := by omega
    have hw : wbit σ K = true := by
      simp only [wbit, hK, hKh]
      unfold readTapeBit; rw [List.getD_append _ _ _ _ (by simp; omega)]; simp [hki]
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, by rw [est]; simp [hσ2, hσ1], eS, eK, ?_,
      by rw [ev]; simp [hσ2, hσ1], by rw [ec]; simp [hσ2, hσ1]⟩
    · have : (d + 1) * (5 * W + 8) = d * (5 * W + 8) + (5 * W + 8) := by ring
      omega
    · intro j h1 h2; rw [oth j h1 h2]; simp [hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]

end LoopB

/-- **The loop-B crop** (streams `0` the bottoms, `1` the round counter, `2` bottom `j`, `3` the gate header's
constant `frame []`, `4` the first pair's `frame []`, `5`, `6` two copies of `frame [true]`). -/
def cropBW : WM 6 0 :=
  .seq (.whs 1 (.seq (NearCubicWires.WireExponent3_5.PrimT.skipFrameW 0) (.fwd 1)))
    (.seq (NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrameW 0 2) (.seq (.wr 1 true)
      (.seq (emitW 3 false) (.seq (emitW 4 false)
        (.seq (emitW 5 true) (.seq (emitW 5 true) (.seq (emitW 5 false)
          (.seq (emitW 6 true) (.seq (emitW 6 true) (emitW 6 false))))))))))

def cropBCost (i W : ℕ) : ℕ := i * (5 * W + 8) + 14 * W + 50

theorem cropBW_spec (cap W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length ≤ W) (tail : List Bool) (i : ℕ)
    (hi : i < ys.length) (rest : List Bool) (σ : WState 6 0) (h0 : ∀ j, σ.sh j = 0)
    (hS : σ.st 0 = ys.flatMap frame ++ tail) (hK : σ.st 1 = List.replicate i true ++ (false :: rest))
    (hE : ∀ j : Fin 7, 2 ≤ j.val → σ.st j = []) :
    ∃ τ, WExec cap cropBW σ τ (cropBCost i W) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = List.replicate (i + 1) true ++ rest ∧
      τ.st 2 = frame ys[i] ∧ τ.st 3 = [false] ∧ τ.st 4 = [false] ∧ τ.st 5 = [true, true, false] ∧
      τ.st 6 = [true, true, false] ∧ τ.cell = σ.cell := by
  obtain ⟨τ1, s1, est, eS, eK, oth, ev, ec⟩ := skipAtomsLe_spec cap (0 : Fin 7) 1 (by decide) W ys hys tail i hi.le
    rest i 0 σ (by omega) hS (by simp [h0]) hK (h0 1)
  obtain ⟨τ2, s2, e2, e2h, n2, -, o2, v2, c2⟩ := NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrame_spec cap
    (0 : Fin 7) 2 (by decide) ((ys.take i).flatMap frame) ys[i] ((ys.drop (i + 1)).flatMap frame ++ tail) τ1
    (by rw [est, hS, NearCubicWires.WireExponent3_5.PrimT.CarWM.flatMap_split ys i hi]; simp) eS
    (by rw [est, hE 2 (by decide), oth 2 (by decide) (by decide), h0]; rfl)
  have s3 := WExec.wr (cap := cap) (1 : Fin 7) true τ2
  set τ3 := τ2.sets 1 (writeTapeBit (τ2.st 1) (τ2.sh 1) true) with hτ3
  have blank : ∀ j : Fin 7, 3 ≤ j.val → τ3.st j = [] ∧ τ3.sh j = 0 := by
    intro j hj
    have hj1 : j ≠ 1 := fun e => by subst e; simp at hj
    have hj0 : j ≠ 0 := fun e => by subst e; simp at hj
    have hj2 : j ≠ 2 := fun e => by subst e; simp at hj
    simp only [hτ3, WState.sets_st, WState.sets_sh, Function.update_of_ne hj1]
    rw [(o2 j hj0 hj2).1, (o2 j hj0 hj2).2, est, hE j (by omega), oth j hj0 hj1, h0]; exact ⟨rfl, rfl⟩
  obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (3 : Fin 7) false τ3 (by
    rw [(blank 3 (by decide)).1, (blank 3 (by decide)).2]; rfl)
  obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := emit_facts cap (4 : Fin 7) false σ4 (by
    rw [(o4 4 (by decide)).1, (o4 4 (by decide)).2, (blank 4 (by decide)).1, (blank 4 (by decide)).2]; rfl)
  obtain ⟨σ6, s6, e6, e6h, o6, v6, c6⟩ := emit_facts cap (5 : Fin 7) true σ5 (by
    rw [(o5 5 (by decide)).1, (o5 5 (by decide)).2, (o4 5 (by decide)).1, (o4 5 (by decide)).2,
      (blank 5 (by decide)).1, (blank 5 (by decide)).2]; rfl)
  obtain ⟨σ7, s7, e7, e7h, o7, v7, c7⟩ := emit_facts cap (5 : Fin 7) true σ6 e6h
  obtain ⟨σ8, s8, e8, e8h, o8, v8, c8⟩ := emit_facts cap (5 : Fin 7) false σ7 e7h
  obtain ⟨σ9, s9, e9, e9h, o9, v9, c9⟩ := emit_facts cap (6 : Fin 7) true σ8 (by
    rw [(o8 6 (by decide)).1, (o8 6 (by decide)).2, (o7 6 (by decide)).1, (o7 6 (by decide)).2,
      (o6 6 (by decide)).1, (o6 6 (by decide)).2, (o5 6 (by decide)).1, (o5 6 (by decide)).2,
      (o4 6 (by decide)).1, (o4 6 (by decide)).2, (blank 6 (by decide)).1, (blank 6 (by decide)).2]; rfl)
  obtain ⟨σ10, s10, e10, e10h, o10, v10, c10⟩ := emit_facts cap (6 : Fin 7) true σ9 e9h
  obtain ⟨τ, s11, e11, e11h, o11, v11, c11⟩ := emit_facts cap (6 : Fin 7) false σ10 e10h
  have hlen : ys[i].length ≤ W := hys _ (List.getElem_mem hi)
  -- facts carried to the end, for streams other than 6, 5, 4, 3
  have keep : ∀ j : Fin 7, j ≠ 3 → j ≠ 4 → j ≠ 5 → j ≠ 6 → τ.st j = τ3.st j := by
    intro j h3 h4 h5 h6
    rw [(o11 j h6).1, (o10 j h6).1, (o9 j h6).1, (o8 j h5).1, (o7 j h5).1, (o6 j h5).1, (o5 j h4).1, (o4 j h3).1]
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 s11)))))))))) (by unfold cropBCost; omega),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keep 0 (by decide) (by decide) (by decide) (by decide)]
    simp only [hτ3, WState.sets_st]; rw [Function.update_of_ne (by decide), n2, est]
  · rw [keep 1 (by decide) (by decide) (by decide) (by decide)]
    simp only [hτ3, WState.sets_st, Function.update_self]
    rw [(o2 1 (by decide) (by decide)).1, (o2 1 (by decide) (by decide)).2, est, eK, hK,
      NearCubicWires.WireExponent3_5.PrimT.CarWM.write_counter]
  · rw [keep 2 (by decide) (by decide) (by decide) (by decide)]
    simp only [hτ3, WState.sets_st]; rw [Function.update_of_ne (by decide), e2, est, hE 2 (by decide)]; rfl
  · rw [(o11 3 (by decide)).1, (o10 3 (by decide)).1, (o9 3 (by decide)).1, (o8 3 (by decide)).1,
      (o7 3 (by decide)).1, (o6 3 (by decide)).1, (o5 3 (by decide)).1, e4, (blank 3 (by decide)).1]; rfl
  · rw [(o11 4 (by decide)).1, (o10 4 (by decide)).1, (o9 4 (by decide)).1, (o8 4 (by decide)).1,
      (o7 4 (by decide)).1, (o6 4 (by decide)).1, e5, (o4 4 (by decide)).1, (blank 4 (by decide)).1]; rfl
  · rw [(o11 5 (by decide)).1, (o10 5 (by decide)).1, (o9 5 (by decide)).1, e8, e7, e6, (o5 5 (by decide)).1,
      (o4 5 (by decide)).1, (blank 5 (by decide)).1]; rfl
  · rw [e11, e10, e9, (o8 6 (by decide)).1, (o7 6 (by decide)).1, (o6 6 (by decide)).1, (o5 6 (by decide)).1,
      (o4 6 (by decide)).1, (blank 6 (by decide)).1]; rfl
  · rw [c11, c10, c9, c8, c7, c6, c5, c4]; simp only [hτ3, WState.sets_cell]; rw [c2, ec]

/-- **The loop-B append** (streams `0` the pair's framed output, `1` the atom-code accumulator). -/
def appendBW : WM 1 0 :=
  .seq (.whs 1 (NearCubicWires.WireExponent3_5.PrimT.skipFrameW 1))
    (NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrameW 0 1)

def appendBCost (gs : List (List Bool)) (y : List Bool) : ℕ := 6 * (gs.flatMap frame).length + 14 * y.length + 7

theorem appendBW_spec (cap : ℕ) (gs : List (List Bool)) (hgs : ∀ g ∈ gs, g ≠ []) (y rest : List Bool)
    (σ : WState 1 0) (h0 : ∀ j, σ.sh j = 0) (hN : σ.st 0 = frame y ++ rest) (hG : σ.st 1 = gs.flatMap frame) :
    ∃ τ, WExec cap appendBW σ τ (appendBCost gs y) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = (gs ++ [y]).flatMap frame ∧
      τ.cell = σ.cell := by
  have s1 := skipWords_spec cap (1 : Fin 2) gs [] σ hgs (by rw [hG]; rfl) (by rw [h0]; rfl)
  set σ1 := σ.seth 1 ([].length + (gs.flatMap frame).length) with hσ1
  obtain ⟨τ, s2, e2, -, n2, -, -, -, c2⟩ := NearCubicWires.WireExponent3_5.PrimT.CarWM.copyFrame_spec cap
    (0 : Fin 2) 1 (by decide) [] y rest σ1 (by simp [hσ1, hN]) (by simp [hσ1, h0]) (by simp [hσ1, hG])
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by unfold appendBCost; omega), by rw [n2]; simp [hσ1], ?_, by
    rw [c2]; simp [hσ1]⟩
  rw [e2]; simp [hσ1, hG, List.flatMap_append]

/-! ## Loop B's word passes as Steps -/

def σB (S K : List Bool) : WState 6 0 := ⟨fun _ => 0, ![S, K, [], [], [], [], []], fun r => r.elim0, false⟩

/-- The loop-B crop's entry bank: the bottoms, the cell, the counter, five blank streams, the log. -/
def cropBIn (S K : List Bool) : Fin 9 → List Bool :=
  Fin.addCases (m := 6 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σB S K)).A (fun _ => [])

theorem cropBIn_val (S K : List Bool) (j : Fin 9) :
    cropBIn S K j = if j.val = 0 then S else if j.val = 1 then [false] else if j.val = 2 then K else [] := by
  fin_cases j <;> rfl

theorem cropBStage (W : ℕ) (ys : List (List Bool)) (hys : ∀ y ∈ ys, y.length ≤ W) (tail : List Bool) (i : ℕ)
    (hi : i < ys.length) (rest : List Bool) : ∃ o : Fin 9 → List Bool,
    Step (Rewind.machine cropBW.toProg.compile) (2 * cropBCost i W + 2) (fun _ => 0)
      (cropBIn (ys.flatMap frame ++ tail) (List.replicate i true ++ (false :: rest))) (fun _ => 0) o ∧
    o 0 = ys.flatMap frame ++ tail ∧ o 1 = [false] ∧ o 2 = List.replicate (i + 1) true ++ rest ∧
    o 3 = frame ys[i] ∧ o 4 = [false] ∧ o 5 = [false] ∧ o 6 = [true, true, false] ∧ o 7 = [true, true, false] := by
  set σ := σB (ys.flatMap frame ++ tail) (List.replicate i true ++ (false :: rest)) with hσ
  obtain ⟨τ, hw, e0, e1, e2, e3, e4, e5, e6, ec⟩ := cropBW_spec 0 W ys hys tail i hi rest σ (fun _ => rfl) rfl rfl
    (by intro j hj; fin_cases j <;> simp at hj <;> rfl)
  obtain ⟨o, st, ho⟩ := wm_step 0 cropBW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 9) = Fin.castAdd 1 (0 : Fin 8) from rfl, ho]; exact e0
  · rw [show (1 : Fin 9) = Fin.castAdd 1 (1 : Fin 8) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 9) = Fin.castAdd 1 (2 : Fin 8) from rfl, ho]; exact e1
  · rw [show (3 : Fin 9) = Fin.castAdd 1 (3 : Fin 8) from rfl, ho]; exact e2
  · rw [show (4 : Fin 9) = Fin.castAdd 1 (4 : Fin 8) from rfl, ho]; exact e3
  · rw [show (5 : Fin 9) = Fin.castAdd 1 (5 : Fin 8) from rfl, ho]; exact e4
  · rw [show (6 : Fin 9) = Fin.castAdd 1 (6 : Fin 8) from rfl, ho]; exact e5
  · rw [show (7 : Fin 9) = Fin.castAdd 1 (7 : Fin 8) from rfl, ho]; exact e6

def σBa (N G : List Bool) : WState 1 0 := ⟨fun _ => 0, ![N, G], fun r => r.elim0, false⟩

/-- The loop-B append's entry bank: the pair's output, the cell, the accumulator, the log. -/
def appendBIn (N G : List Bool) : Fin 4 → List Bool :=
  Fin.addCases (m := 1 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σBa N G)).A (fun _ => [])

theorem appendBIn_val (N G : List Bool) (j : Fin 4) :
    appendBIn N G j = if j.val = 0 then N else if j.val = 1 then [false] else if j.val = 2 then G else [] := by
  fin_cases j <;> rfl

theorem appendBStage (gs : List (List Bool)) (hgs : ∀ g ∈ gs, g ≠ []) (y rest : List Bool) : ∃ o : Fin 4 → List Bool,
    Step (Rewind.machine appendBW.toProg.compile) (2 * appendBCost gs y + 2) (fun _ => 0)
      (appendBIn (frame y ++ rest) (gs.flatMap frame)) (fun _ => 0) o ∧
    o 0 = frame y ++ rest ∧ o 1 = [false] ∧ o 2 = (gs ++ [y]).flatMap frame := by
  set σ := σBa (frame y ++ rest) (gs.flatMap frame) with hσ
  obtain ⟨τ, hw, e0, e1, ec⟩ := appendBW_spec 0 gs hgs y rest σ (fun _ => rfl) rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 appendBW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 1 (0 : Fin 3) from rfl, ho]; exact e0
  · rw [show (1 : Fin 4) = Fin.castAdd 1 (1 : Fin 3) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 4) = Fin.castAdd 1 (2 : Fin 3) from rfl, ho]; exact e1

/-! ## The carrier code's field: canonical binary to `natWord` -/

/-- `natWord` of a positive number: `1^|x.bits| 0 x.bits`. -/
theorem natWord_bits (x : ℕ) (hx : 0 < x) : natWord x = List.replicate x.bits.length true ++ false :: x.bits := by
  have hs : x.bits.length = natBitLength x := by
    rw [Nat.size_eq_bits_len]
    unfold natBitLength
    apply le_antisymm
    · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) x)
    · exact Nat.lt_size.mpr (Nat.pow_log_le_self 2 (by omega))
  rw [natWord_pay, hs]
  congr 2
  unfold pay
  rw [NearCubicWires.WireExponent3_5.UnionMachine.Round.testBit_eq_binary,
    CanonicalPositiveOutput.binary_padding _ _ (NearCubicWires.WireExponent3_5.UnionMachine.Round.natBitLength_lt x), hs]
  simp

theorem rd_sent_lt (L k : ℕ) (hk : k < L) : readTapeBit (false :: List.replicate L true) (k + 1) = true := by
  unfold readTapeBit; rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; omega)]; simp

theorem rd_sent_ge (L k : ℕ) (hk : L ≤ k) : readTapeBit (false :: List.replicate L true) (k + 1) = false := by
  unfold readTapeBit; rw [List.getD_cons_succ, List.getD_eq_default _ _ (by simp; omega)]

theorem frameP_rep_succ (k : ℕ) : frameP (List.replicate (k + 1) true) = frameP (List.replicate k true) ++ [true, true] := by
  rw [List.replicate_succ', frameP_append']; rfl

section NatW
variable {ns nr : ℕ} (cap : ℕ)

/-- Pass 1: one prefix `1` (two cells) per framed bit of `F`, one ruler cell per bit. -/
theorem pass1_spec (F O T : Fin (ns + 1)) (hFO : F ≠ O) (hFT : F ≠ T) (hOT : O ≠ T) (b rest : List Bool) :
    ∀ (d k : ℕ) (σ : WState ns nr), k + d = b.length → σ.st F = frame b ++ rest → σ.sh F = 2 * k →
      σ.st O = frameP (List.replicate k true) → σ.sh O = (σ.st O).length →
      σ.st T = false :: List.replicate k true → σ.sh T = (σ.st T).length →
      ∃ τ, WExec cap (.whs F (.seq (.fwd F) (.seq (emitW O true) (.seq (emitW O true) (.seq (.fwd F)
          (emitW T true)))))) σ τ (d * 18 + 1) ∧
        τ.st F = σ.st F ∧ τ.sh F = 2 * b.length ∧ τ.st O = frameP (List.replicate b.length true) ∧
        τ.sh O = (τ.st O).length ∧ τ.st T = false :: List.replicate b.length true ∧ τ.sh T = (τ.st T).length ∧
        (∀ j, j ≠ F → j ≠ O → j ≠ T → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, hkd, hF, hFh, hO, hOh, hT, hTh => by
    have hk : k = b.length := by omega
    subst hk
    have hz : wbit σ F = false := by
      simp only [wbit, hF, hFh, frame_eq_frameP, List.append_assoc]
      have := NearCubicWires.WireExponent3_5.PrimT.CarWM.rd_at (frameP b) ([false] ++ rest)
      simpa using this
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hFh, hO, hOh, hT, hTh, fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | d + 1, k, σ, hkd, hF, hFh, hO, hOh, hT, hTh => by
    have hOF : O ≠ F := fun e => hFO e.symm
    have hTF : T ≠ F := fun e => hFT e.symm
    have hTO : T ≠ O := fun e => hOT e.symm
    have hkb : k < b.length := by omega
    have hw : wbit σ F = true := by
      simp only [wbit, hF, hFh, frame_eq_frameP, List.append_assoc]
      have := rd_mark [] b ([false] ++ rest) k hkb; simpa using this
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap F σ
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O true σ1 (by rw [(o1 O hOF).1, (o1 O hOF).2, hOh])
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap O true σ2 e2h
    obtain ⟨σ4, s4, a4, a4h, o4, v4, c4⟩ := fwd_facts cap F σ3
    have T4 := (((o1 T hTF).trans' (o2 T hTO)).trans' (o3 T hTO)).trans' (o4 T hTF)
    obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := emit_facts cap T true σ4 (by rw [T4.1, T4.2, hTh])
    have O5 := (o4 O hOF).trans' (o5 O hOT)
    obtain ⟨τ, s6, eF, eFh, eO, eOh, eT, eTh, oth, v6, c6⟩ := pass1_spec F O T hFO hFT hOT b rest d (k + 1) σ5
      (by omega) (by rw [(o5 F hFT).1, a4, (o3 F hFO).1, (o2 F hFO).1, a1, hF])
      (by rw [(o5 F hFT).2, a4h, (o3 F hFO).2, (o2 F hFO).2, a1h, hFh]; ring)
      (by rw [O5.1, e3, e2, (o1 O hOF).1, hO, frameP_rep_succ]; simp)
      (by rw [O5.1, O5.2, e3h])
      (by rw [e5, T4.1, hT, List.replicate_succ']; simp)
      e5h
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) s6)
      (by ring_nf; omega), ?_, eFh, eO, eOh, eT, eTh, ?_, ?_, ?_⟩
    · rw [eF, (o5 F hFT).1, a4, (o3 F hFO).1, (o2 F hFO).1, a1]
    · intro j h1 h2 h3
      exact (((((o1 j h1).trans' (o2 j h2)).trans' (o3 j h2)).trans' (o4 j h1)).trans' (o5 j h3)).trans' (oth j h1 h2 h3)
    · rw [v6, v5, v4, v3, v2, v1]
    · rw [c6, c5, c4, c3, c2, c1]

/-- The rewind: both heads back along the ruler, two cells of `F` per ruler cell. -/
theorem rewind_spec (F T : Fin (ns + 1)) (hFT : F ≠ T) (L : ℕ) :
    ∀ (k : ℕ) (σ : WState ns nr), k ≤ L → σ.st T = false :: List.replicate L true → σ.sh T = k →
      σ.sh F = 2 * k →
      ∃ τ, WExec cap (.whs T (.seq (.bwd T) (.seq (.bwd F) (.bwd F)))) σ τ (k * 7 + 1) ∧ τ.st = σ.st ∧
        τ.sh T = 0 ∧ τ.sh F = 0 ∧ (∀ j, j ≠ F → j ≠ T → τ.sh j = σ.sh j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, σ, _, hT, hTh, hFh => by
    have hz : wbit σ T = false := by simp only [wbit, hT, hTh]; rfl
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, hTh, by omega, fun _ _ _ => rfl, rfl, rfl⟩
  | k + 1, σ, hkL, hT, hTh, hFh => by
    have hTF : T ≠ F := fun e => hFT e.symm
    have hw : wbit σ T = true := by simp only [wbit, hT, hTh]; exact rd_sent_lt L k (by omega)
    have s1 := WExec.bwd (cap := cap) T σ
    set σ1 := σ.seth T (σ.sh T - 1) with hσ1
    have s2 := WExec.bwd (cap := cap) F σ1
    set σ2 := σ1.seth F (σ1.sh F - 1) with hσ2
    have s3 := WExec.bwd (cap := cap) F σ2
    set σ3 := σ2.seth F (σ2.sh F - 1) with hσ3
    obtain ⟨τ, s4, e4, e4T, e4F, oth, v4, c4⟩ := rewind_spec F T hFT L k σ3 (by omega)
      (by simp [hσ3, hσ2, hσ1, hT]) (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hTF, hTh])
      (by simp [hσ3, hσ2, hσ1, Function.update_of_ne hFT, hFh]; omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) s4) (by ring_nf; omega),
      by rw [e4]; simp [hσ3, hσ2, hσ1], e4T, e4F, ?_, by rw [v4]; simp [hσ3, hσ2, hσ1],
      by rw [c4]; simp [hσ3, hσ2, hσ1]⟩
    intro j h1 h2
    rw [oth j h1 h2]; simp [hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]

/-- Pass 3: one payload bit per ruler cell, framed. -/
theorem pass3_spec (F O T : Fin (ns + 1)) (hFO : F ≠ O) (hFT : F ≠ T) (hOT : O ≠ T) (b rest : List Bool) :
    ∀ (d k : ℕ) (σ : WState ns nr) (o0 : List Bool), k + d = b.length → σ.st F = frame b ++ rest →
      σ.sh F = 2 * k → σ.st O = o0 ++ frameP (b.take k) → σ.sh O = (σ.st O).length →
      σ.st T = false :: List.replicate b.length true → σ.sh T = k + 1 →
      ∃ τ, WExec cap (.whs T (.seq (.fwd F) (.seq (emitW O true) (.seq (.ifs F (emitW O true) (emitW O false))
          (.seq (.fwd F) (.fwd T)))))) σ τ (d * 17 + 1) ∧
        τ.st F = σ.st F ∧ τ.st O = o0 ++ frameP b ∧ τ.sh O = (τ.st O).length ∧ τ.st T = σ.st T ∧
        (∀ j, j ≠ F → j ≠ O → j ≠ T → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | 0, k, σ, o0, hkd, _, _, hO, hOh, hT, hTh => by
    have hk : k = b.length := by omega
    subst hk
    have hz : wbit σ T = false := by
      simp only [wbit, hT, hTh]; exact rd_sent_ge _ _ (le_refl _)
    exact ⟨σ, WExec.mono (WExec.whsF hz) (by omega), rfl, by rw [hO, List.take_length], hOh, rfl,
      fun _ _ _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | d + 1, k, σ, o0, hkd, hF, hFh, hO, hOh, hT, hTh => by
    have hOF : O ≠ F := fun e => hFO e.symm
    have hTF : T ≠ F := fun e => hFT e.symm
    have hTO : T ≠ O := fun e => hOT e.symm
    have hkb : k < b.length := by omega
    have hw : wbit σ T = true := by
      simp only [wbit, hT, hTh]; exact rd_sent_lt _ _ hkb
    obtain ⟨σ1, s1, a1, a1h, o1, v1, c1⟩ := fwd_facts cap F σ
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap O true σ1 (by rw [(o1 O hOF).1, (o1 O hOF).2, hOh])
    have hb : wbit σ2 F = b.getD k false := by
      simp only [wbit, (o2 F hFO).1, (o2 F hFO).2, a1, a1h, hF, hFh, frame_eq_frameP, List.append_assoc]
      have := rd_bit [] b ([false] ++ rest) k hkb; simpa using this
    obtain ⟨σ3, s3', e3, e3h, o3, v3, c3⟩ := emit_facts cap O (b.getD k false) σ2 e2h
    have s3 : WExec cap (.ifs F (emitW O true) (emitW O false)) σ2 σ3 4 := by
      cases hbv : b.getD k false
      · rw [hbv] at hb s3'; exact WExec.ifsF hb s3'
      · rw [hbv] at hb s3'; exact WExec.ifsT hb s3'
    obtain ⟨σ4, s4, a4, a4h, o4, v4, c4⟩ := fwd_facts cap F σ3
    obtain ⟨σ5, s5, a5, a5h, o5, v5, c5⟩ := fwd_facts cap T σ4
    have T4 := (((o1 T hTF).trans' (o2 T hTO)).trans' (o3 T hTO)).trans' (o4 T hTF)
    have F3 := (o2 F hFO).trans' (o3 F hFO)
    have O5 := (o4 O hOF).trans' (o5 O hOT)
    obtain ⟨τ, s6, eF, eO, eOh, eT, oth, v6, c6⟩ := pass3_spec F O T hFO hFT hOT b rest d (k + 1) σ5 o0 (by omega)
      (by rw [(o5 F hFT).1, a4, F3.1, a1, hF])
      (by rw [(o5 F hFT).2, a4h, F3.2, a1h, hFh]; ring)
      (by rw [O5.1, e3, e2, (o1 O hOF).1, hO, List.take_add_one, List.getElem?_eq_getElem hkb, Option.toList_some,
          frameP_append', List.getD_eq_getElem _ _ hkb]; simp)
      (by rw [O5.1, O5.2, e3h])
      (by rw [a5, T4.1, hT]) (by rw [a5h, T4.2, hTh])
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) s6)
      (by ring_nf; omega), ?_, eO, eOh, ?_, ?_, ?_, ?_⟩
    · rw [eF, (o5 F hFT).1, a4, F3.1, a1]
    · rw [eT, a5, T4.1]
    · intro j h1 h2 h3
      exact (((((o1 j h1).trans' (o2 j h2)).trans' (o3 j h2)).trans' (o4 j h1)).trans' (o5 j h3)).trans' (oth j h1 h2 h3)
    · rw [v6, v5, v4, v3, v2, v1]
    · rw [c6, c5, c4, c3, c2, c1]

end NatW

/-- **The `natWord` writer** (streams `0` the framed canonical binary `frame x.bits ++ …`, `1` the output, `2` a
ruler): `frame (natWord x)`, the special word for `x = 0` included. -/
def natW : WM 2 0 :=
  .ifs 0
    (.seq (emitW 2 false) (.seq (.whs 0 (.seq (.fwd 0) (.seq (emitW 1 true) (.seq (emitW 1 true) (.seq (.fwd 0)
      (emitW 2 true)))))) (.seq (emitW 1 true) (.seq (emitW 1 false) (.seq (.seq (.bwd 2)
        (.whs 2 (.seq (.bwd 2) (.seq (.bwd 0) (.bwd 0))))) (.seq (.fwd 2) (.seq (.whs 2 (.seq (.fwd 0)
          (.seq (emitW 1 true) (.seq (.ifs 0 (emitW 1 true) (emitW 1 false)) (.seq (.fwd 0) (.fwd 2))))))
            (emitW 1 false))))))))
    (.seq (emitW 1 true) (.seq (emitW 1 true) (.seq (emitW 1 true) (.seq (emitW 1 false) (.seq (emitW 1 true)
      (.seq (emitW 1 false) (emitW 1 false)))))))

def natCost (x : ℕ) : ℕ := 42 * x.bits.length + 40

theorem frame_natWord_split (L : ℕ) (b : List Bool) :
    frame (List.replicate L true ++ false :: b) = frameP (List.replicate L true) ++ [true, false] ++ frameP b ++ [false] := by
  rw [frame_eq_frameP, frameP_append']; simp

theorem natW_spec (cap x : ℕ) (rest : List Bool) (σ : WState 2 0) (h0 : ∀ j, σ.sh j = 0)
    (hF : σ.st 0 = frame x.bits ++ rest) (hO : σ.st 1 = []) (hT : σ.st 2 = []) :
    ∃ τ, WExec cap natW σ τ (natCost x) ∧ τ.st 0 = σ.st 0 ∧ τ.st 1 = frame (natWord x) ∧ τ.cell = σ.cell := by
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx
    have hz : wbit σ 0 = false := by simp only [wbit, hF, h0]; rfl
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (1 : Fin 3) true σ (by rw [hO, h0]; rfl)
    obtain ⟨σ2, s2, e2, e2h, o2, v2, c2⟩ := emit_facts cap (1 : Fin 3) true σ1 e1h
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap (1 : Fin 3) true σ2 e2h
    obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (1 : Fin 3) false σ3 e3h
    obtain ⟨σ5, s5, e5, e5h, o5, v5, c5⟩ := emit_facts cap (1 : Fin 3) true σ4 e4h
    obtain ⟨σ6, s6, e6, e6h, o6, v6, c6⟩ := emit_facts cap (1 : Fin 3) false σ5 e5h
    obtain ⟨τ, s7, e7, e7h, o7, v7, c7⟩ := emit_facts cap (1 : Fin 3) false σ6 e6h
    refine ⟨τ, WExec.mono (WExec.ifsF hz (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5
      (WExec.seq s6 s7))))))) (by unfold natCost; simp), ?_, ?_, ?_⟩
    · rw [(o7 0 (by decide)).1, (o6 0 (by decide)).1, (o5 0 (by decide)).1, (o4 0 (by decide)).1,
        (o3 0 (by decide)).1, (o2 0 (by decide)).1, (o1 0 (by decide)).1]
    · rw [e7, e6, e5, e4, e3, e2, e1, hO]; decide
    · rw [c7, c6, c5, c4, c3, c2, c1]
  · set b := x.bits with hb
    have hbne : b ≠ [] := by
      intro h
      have := CanonicalPositiveOutput.nat_bits_value x
      rw [← hb, h] at this; simp [RadixSemantics.value] at this; omega
    have hw : wbit σ 0 = true := by
      simp only [wbit, hF, h0]
      cases hbc : b with
      | nil => exact absurd hbc hbne
      | cons c cs => rfl
    -- the ruler's sentinel
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap (2 : Fin 3) false σ (by rw [hT, h0]; rfl)
    -- pass 1
    obtain ⟨σ2, s2, a2, a2h, e2O, e2Oh, e2T, e2Th, o2, v2, c2⟩ := pass1_spec cap (0 : Fin 3) 1 2 (by decide)
      (by decide) (by decide) b rest b.length 0 σ1 (by omega) (by rw [(o1 0 (by decide)).1, hF])
      (by rw [(o1 0 (by decide)).2, h0]) (by rw [(o1 1 (by decide)).1, hO]; rfl)
      (by rw [(o1 1 (by decide)).1, (o1 1 (by decide)).2, hO, h0]; rfl) (by rw [e1, hT]; rfl) e1h
    -- the separator `1 0`
    obtain ⟨σ3, s3, e3, e3h, o3, v3, c3⟩ := emit_facts cap (1 : Fin 3) true σ2 e2Oh
    obtain ⟨σ4, s4, e4, e4h, o4, v4, c4⟩ := emit_facts cap (1 : Fin 3) false σ3 e3h
    -- the rewind
    have T4 := (o3 2 (by decide)).trans' (o4 2 (by decide))
    have F4 := (o3 0 (by decide)).trans' (o4 0 (by decide))
    have s5a := WExec.bwd (cap := cap) (2 : Fin 3) σ4
    set σ5 := σ4.seth 2 (σ4.sh 2 - 1) with hσ5
    obtain ⟨σ6, s6, e6, e6T, e6F, o6, v6, c6⟩ := rewind_spec cap (0 : Fin 3) 2 (by decide) b.length b.length σ5
      (le_refl _) (by simp [hσ5, T4.1, e2T]) (by simp [hσ5, T4.2, e2Th, T4.1, e2T])
      (by simp [hσ5, F4.2, a2h])
    -- pass 3
    obtain ⟨σ7, s7, a7, a7h, o7, v7, c7⟩ := fwd_facts cap (2 : Fin 3) σ6
    obtain ⟨σ8, s8, e8F, e8O, e8Oh, e8T, o8, v8, c8⟩ := pass3_spec cap (0 : Fin 3) 1 2 (by decide) (by decide)
      (by decide) b rest b.length 0 σ7 (frameP (List.replicate b.length true) ++ [true, false]) (by omega)
      (by rw [(o7 0 (by decide)).1, e6]; simp [hσ5, F4.1, a2, (o1 0 (by decide)).1, hF])
      (by rw [(o7 0 (by decide)).2, e6F])
      (by rw [(o7 1 (by decide)).1, e6]; simp [hσ5, e4, e3, e2O])
      (by rw [(o7 1 (by decide)).1, (o7 1 (by decide)).2, e6, o6 1 (by decide) (by decide)]; simp [hσ5, e4h])
      (by rw [a7, e6]; simp [hσ5, T4.1, e2T]) (by rw [a7h, e6T])
    -- the end mark
    obtain ⟨τ, s9, e9, e9h, o9, v9, c9⟩ := emit_facts cap (1 : Fin 3) false σ8 e8Oh
    refine ⟨τ, WExec.mono (WExec.ifsT hw (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq
      (WExec.seq s5a s6) (WExec.seq s7 (WExec.seq s8 s9)))))))) (by unfold natCost; rw [← hb]; omega), ?_, ?_, ?_⟩
    · rw [(o9 0 (by decide)).1, e8F, (o7 0 (by decide)).1, e6]; simp [hσ5, F4.1, a2, (o1 0 (by decide)).1]
    · rw [e9, e8O, natWord_bits x hx, ← hb, frame_natWord_split]
    · rw [c9, c8, c7, c6]; simp [hσ5, c4, c3, c2, c1]

def σN (F : List Bool) : WState 2 0 := ⟨fun _ => 0, ![F, [], []], fun r => r.elim0, false⟩

/-- The `natWord` writer's entry bank: the framed binary, the cell, two blank streams, the log. -/
def natIn (F : List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m := 2 + 2 + 0) (n := 1) (motive := fun _ => List Bool) (wenc 0 (σN F)).A (fun _ => [])

theorem natIn_val (F : List Bool) (j : Fin 5) :
    natIn F j = if j.val = 0 then F else if j.val = 1 then [false] else [] := by
  fin_cases j <;> rfl

/-- **The `natWord` writer as a Step**: `frame (natWord x)` on tape `2`. -/
theorem natStage (x : ℕ) (rest : List Bool) : ∃ o : Fin 5 → List Bool,
    Step (Rewind.machine natW.toProg.compile) (2 * natCost x + 2) (fun _ => 0) (natIn (frame x.bits ++ rest))
      (fun _ => 0) o ∧ o 0 = frame x.bits ++ rest ∧ o 1 = [false] ∧ o 2 = frame (natWord x) := by
  set σ := σN (frame x.bits ++ rest) with hσ
  obtain ⟨τ, hw, e0, e1, ec⟩ := natW_spec 0 x rest σ (fun _ => rfl) rfl rfl rfl
  obtain ⟨o, st, ho⟩ := wm_step 0 natW σ τ _ hw (wenc_H_zero 0 _ (fun _ => rfl) (fun r => r.elim0))
  refine ⟨o, st, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 5) = Fin.castAdd 1 (0 : Fin 4) from rfl, ho]; exact e0
  · rw [show (1 : Fin 5) = Fin.castAdd 1 (1 : Fin 4) from rfl, ho]; show [τ.cell] = [false]; rw [ec]; rfl
  · rw [show (2 : Fin 5) = Fin.castAdd 1 (2 : Fin 4) from rfl, ho]; exact e1

end NearCubicWires.WireExponent3_5.UnionMachine.CWWords
