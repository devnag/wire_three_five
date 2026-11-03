import Setup.PhaseP
import Setup.Positions

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

/-! ## The readers do not see trailing blanks -/

theorem rd_tail {a b : List Bool} {x y : Bool} (h : RdEq (x :: a) (y :: b)) : RdEq a b := fun p => by
  have := h (p + 1); simpa [readTapeBit] using this

theorem rd_nil_tail {a : List Bool} {x : Bool} (h : RdEq [] (x :: a)) : RdEq [] a := fun p => by
  have := h (p + 1); simpa [readTapeBit] using this

theorem rd_head {a b : List Bool} {x y : Bool} (h : RdEq (x :: a) (y :: b)) : x = y := by
  have := h 0; simpa [readTapeBit] using this

theorem rd_nil_head {a : List Bool} {x : Bool} (h : RdEq [] (x :: a)) : x = false := by
  have := h 0; simpa [readTapeBit] using this.symm

theorem rc_rd : ∀ (a b : List Bool), RdEq a b →
    (readCount a).1 = (readCount b).1 ∧ RdEq (readCount a).2 (readCount b).2
  | [], [], _ => ⟨rfl, RdEq.refl _⟩
  | [], x :: r, h => by
    have hx := rd_nil_head h
    subst hx
    exact ⟨rfl, rd_nil_tail h⟩
  | x :: r, [], h => by
    have hx := rd_nil_head (RdEq.symm h)
    subst hx
    exact ⟨rfl, RdEq.symm (rd_nil_tail (RdEq.symm h))⟩
  | x :: a, y :: b, h => by
    have hxy := rd_head h
    subst hxy
    cases x with
    | false => exact ⟨rfl, rd_tail h⟩
    | true =>
      have ih := rc_rd a b (rd_tail h)
      simp only [readCount]
      exact ⟨by rw [ih.1], ih.2⟩

theorem drop_rd (n : ℕ) {a b : List Bool} (h : RdEq a b) : RdEq (a.drop n) (b.drop n) := fun p => by
  have := h (n + p)
  simpa [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_drop] using this

theorem rb_rd (ℓ : ℕ) {a b : List Bool} (h : RdEq a b) :
    (readBits ℓ a).1 = (readBits ℓ b).1 ∧ RdEq (readBits ℓ a).2 (readBits ℓ b).2 := by
  refine ⟨?_, drop_rd ℓ h⟩
  unfold readBits
  simp only
  congr 1
  funext i
  exact h i.val

theorem rf_rd {a b : List Bool} (h : RdEq a b) :
    (readField a).1 = (readField b).1 ∧ RdEq (readField a).2 (readField b).2 := by
  obtain ⟨h1, h2⟩ := rc_rd a b h
  unfold readField
  rw [h1]
  exact rb_rd _ h2

/-! ## The ideal guess word of phase B -/

/-- The padding of the ideal guess word of phase B. -/
def padB (N pad : ℕ) : ℕ := pad + 2 * (N / 16) + 4

theorem guessWord_length (N : ℕ) (bits : List Bool) (pad : ℕ) : (guessWord N bits pad).length = N / 16 + pad := by
  simp [guessWord, prefixBits_length]

/-- A field at the start of `r` is physical when `r` contains a blank and is long enough. -/
theorem field_split (r : List Bool) (hf : false ∈ r) (hl : 2 * (readCount r).1 + 1 ≤ r.length) :
    r = countWord (readField r).1.length ++ (readField r).1 ++ (readField r).2 ∧
      (readField r).1.length = (readCount r).1 ∧ (readField r).2 = r.drop (2 * (readCount r).1 + 1) := by
  set l := (readCount r).1 with hl'
  set t := (readCount r).2 with ht
  have hsplit : r = countWord l ++ t := readCount_split r hf
  have htl : l ≤ t.length := by
    have := congrArg List.length hsplit
    simp [countWord] at this
    omega
  have hrf : readField r = (t.take l, t.drop l) := by
    unfold readField readBits
    rw [← hl', ← ht, ofFn_getD_take t l htl]
  have hlen : (t.take l).length = l := by simp; omega
  refine ⟨?_, by rw [hrf, hlen], Worker.Format.readField_snd r⟩
  rw [hrf, hlen]
  simp only
  rw [List.append_assoc, List.take_append_drop]
  exact hsplit

/-- **The first field of the ideal guess word is physical.** -/
theorem field1_split (N : ℕ) (bits : List Bool) (pad : ℕ) :
    guessWord N bits (padB N pad) = countWord (readField (guessWord N bits (padB N pad))).1.length ++
        (readField (guessWord N bits (padB N pad))).1 ++ (readField (guessWord N bits (padB N pad))).2 ∧
      (readField (guessWord N bits (padB N pad))).1.length ≤ N / 16 ∧
      (readField (guessWord N bits (padB N pad))).2 =
        (guessWord N bits (padB N pad)).drop (oracleEnd (guessWord N bits (padB N pad))) := by
  obtain ⟨h1, h2, h3, h4⟩ := guessWord_split N bits (padB N pad) (by unfold padB; omega)
  exact ⟨h1, by omega, h4⟩

theorem drop_guessWord (N : ℕ) (bits : List Bool) (pad p : ℕ) :
    ∃ l m, (guessWord N bits pad).drop p = l ++ List.replicate m false ∧ l.length ≤ N / 16 ∧
      m + p ≥ pad := by
  unfold guessWord
  refine ⟨(Codec.prefixBits bits (N / 16)).drop p, pad - (p - (Codec.prefixBits bits (N / 16)).length), ?_, ?_, ?_⟩
  · rw [List.drop_append, List.drop_replicate]
  · simp [prefixBits_length]
  · rw [prefixBits_length]; omega

/-- **The second field of the ideal guess word is physical.** -/
theorem field2_split (N : ℕ) (bits : List Bool) (pad : ℕ) (hpad : N / 16 + 1 ≤ pad) :
    let r := (readField (guessWord N bits (padB N pad))).2
    r = countWord (readField r).1.length ++ (readField r).1 ++ (readField r).2 ∧ (readField r).1.length ≤ N / 16 ∧
      oracleEnd r = 2 * (readField r).1.length + 1 := by
  intro r
  obtain ⟨-, hl1, hr1⟩ := field1_split N bits pad
  have hp1 : oracleEnd (guessWord N bits (padB N pad)) ≤ 2 * (N / 16) + 1 := by
    have := (guessWord_split N bits (padB N pad) (by unfold padB; omega)).2.2.1
    unfold oracleEnd; omega
  obtain ⟨l, m, hlm, hll, hm⟩ := drop_guessWord N bits (padB N pad) (oracleEnd (guessWord N bits (padB N pad)))
  have hr : r = l ++ List.replicate m false := by rw [← hlm]; exact hr1
  have hc : (readCount r).1 ≤ N / 16 := by rw [hr]; exact (readCount_pad l m).trans hll
  have hpB : padB N pad = pad + 2 * (N / 16) + 4 := rfl
  have hm4 : 1 ≤ m := by omega
  have hf : false ∈ r := by
    rw [hr]; apply List.mem_append_right; apply List.mem_replicate.2; exact ⟨by omega, rfl⟩
  have hrl : r.length = (guessWord N bits (padB N pad)).length - oracleEnd (guessWord N bits (padB N pad)) := by
    have hr1' : r = List.drop (oracleEnd (guessWord N bits (padB N pad))) (guessWord N bits (padB N pad)) := hr1
    rw [hr1', List.length_drop]
  have hlen : 2 * (readCount r).1 + 1 ≤ r.length := by
    rw [hrl, guessWord_length]; omega
  obtain ⟨hs, hl2, -⟩ := field_split r hf hlen
  exact ⟨hs, by omega, by unfold oracleEnd; omega⟩

/-! ## `updS` frames -/

theorem updS_sh_zero {ns nr t : ℕ} (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (tout : Fin t → List Bool) (i : Fin (ns + 1)) :
    (updS tmap σ (fun _ => 0) tout).sh i = if ∃ j, tmap j = i then 0 else σ.sh i := by
  classical
  by_cases h : ∃ j, tmap j = i
  · obtain ⟨j, rfl⟩ := h
    rw [updS_sh_slot tmap σ _ tout hinj j, if_pos ⟨j, rfl⟩]
  · rw [if_neg h, updS_sh_other tmap σ _ tout i (fun j hj => h ⟨j, hj⟩)]

/-! ## The program -/

section Prog

end Prog

/-! ## The states before and after phase B -/

/-! ## The flag step -/

/-! ## Phase B on the ideal state -/

end

end NearCubicGates.Close.Setup
