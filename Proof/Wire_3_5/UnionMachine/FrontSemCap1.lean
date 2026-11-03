import Lean
import Proof.Wire_3_5.UnionMachine.FrontSemGate
import Proof.Wire_3_5.UnionMachine.FrontSemPathBase
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontSemTW
import Proof.Wire_3_5.UnionMachine.FrontSemCap1Base


noncomputable section


/-! # C6 front, the semantic core (12): a guess's size envelope and its call table (P3:3485-3491, 3669-3691)

**`GEnv g Λ K`**: every size of the guess `g` the front's capacities read is at most `K` (the width, the variable
count, `2^{cb}`, the grid, the mass, the PCPP size bound, the atoms' and the carriers' codes, the translation).
From it: every scheduled call's request word (**`word_le`**, PA's `word_length`), every entry word, and the call
table's words (**`twWords_le`**: the schedule's length, the `length_schedule_le`, times an entry's length).

Paper quantity of the main types: the guess's call table (its requests and coefficients) against the width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairRepresentation (natWord natListWord)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTW (nvG twWords)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontFoldSem (foldOf)

section Env
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N}

/-- **A guess's size envelope** at bound `K` (mass `Λ`). -/
structure GEnv (g : UnionGuess S z) (Λ K : ℕ) : Prop where
  q2 : 2 ≤ g.q
  q : g.q ≤ K
  nv : nvG g ≤ K
  cb : 2 ^ g.pcpp.clauseBits ≤ K
  s1 : 1 ≤ g.s
  s : g.s ≤ K
  lam1 : 1 ≤ Λ
  lam : Λ ≤ K
  mass : (g.checkData g.translation).mass = Λ
  kp : S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree ≤ K
  circ : ∀ a : g.AtomIx, (natWord (g.mode.code (g.circ a))).length ≤ K
  cw : ∀ X, X < nvG g → (CodeWriters.codesWord g.mode ((foldOf (g.checkData g.translation)).atoms X)).length ≤ K
  car : ∀ X : PcppVar g.pcpp, natBitLength (Stars.Carrier.code (g.carrier X)) ≤ K
  tr : (natListWord g.translation).length ≤ K
  trl : g.translation.length ≤ K
  cst : (natWord (CWConst.constCode g.mode)).length ≤ K

variable {g : UnionGuess S z} {Λ K : ℕ}

/-- **Every scheduled call's word.** -/
theorem call_word_le (hG : GEnv g Λ K) (t : ℚ × PrimRequest)
    (ht : t ∈ (g.checkData g.translation).termsV ∨ t ∈ (g.checkData g.translation).termsQ ∨
      t ∈ (g.checkData g.translation).termsMu) :
    t.2.word.length ≤ 11 * K + 24 := by
  have hq := hG.q
  have key : ∀ (cs : List (Stars.Carrier (g.checkData g.translation).q)) (u : Fin 4 → g.AtomIx), cs.length ≤ 2 →
      (∀ X ∈ cs, natBitLength (Stars.Carrier.code X) ≤ K) →
      (tupleRequest (g.checkData g.translation).mode (g.checkData g.translation).q (g.checkData g.translation).circ u cs
        (g.checkData g.translation).translation).word.length ≤ 11 * K + 24 := by
    intro cs u hcs hcar
    have := word_le g.mode g.q (g.checkData g.translation).circ u cs g.translation K
      (fun k => by rw [UnionGuess.checkData_circ]; exact hG.circ (u k)) hcs hcar hG.tr
    exact le_trans this (by omega)
  rcases ht with ht | ht | ht
  · obtain ⟨pos, j, u, -, rfl⟩ := ((g.checkData g.translation).mem_termsV t).1 ht
    exact key _ u (le_of_eq_of_le rfl (by norm_num)) (fun X hX => by
      have e := List.mem_singleton.1 hX; subst e; exact hG.car _)
  · obtain ⟨pos, j, u, -, rfl⟩ := ((g.checkData g.translation).mem_termsQ t).1 ht
    exact key _ u (le_of_eq_of_le rfl (by norm_num)) (fun X hX => by
      have e := List.mem_singleton.1 hX; subst e; exact hG.car _)
  · obtain ⟨i, j, u, -, rfl⟩ := ((g.checkData g.translation).mem_termsMu t).1 ht
    exact key _ u (le_of_eq_of_le rfl (by norm_num)) (fun X hX => by
      rcases List.mem_cons.1 hX with e | hX'
      · subst e; exact hG.car _
      · have e := List.mem_singleton.1 hX'; subst e; exact hG.car _)

theorem entry_le (hG : GEnv g Λ K) (hsg : (g.checkData g.translation).signsOk = true) (k : Fin 3)
    (t : ℚ × PrimRequest)
    (ht : t ∈ (g.checkData g.translation).termsV ∨ t ∈ (g.checkData g.translation).termsQ ∨
      t ∈ (g.checkData g.translation).termsMu) :
    (Entry.entryWord (Bridge.entryOf k (g.checkData g.translation).s t)).length ≤ EW K := by
  have hw := call_word_le hG t ht
  have hm := FrontCaps.CheckB.terms_mag (g.checkData g.translation) Λ hG.mass hG.s1 hsg t ht
  have hΛs : (Λ + (g.checkData g.translation).s) ^ 4 ≤ (K + K) ^ 4 :=
    Nat.pow_le_pow_left (Nat.add_le_add hG.lam hG.s) 4
  unfold Entry.entryWord Bridge.entryOf
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate,
    frame_len]
  unfold EW
  omega

/-- **The call table's words.** -/
theorem twWords_le (hG : GEnv g Λ K) (hsg : (g.checkData g.translation).signsOk = true) :
    (twWords (g.checkData g.translation)).length ≤ CN K * EW K := by
  set D := g.checkData g.translation with hD
  have hm : D.mass ≠ 0 := by rw [hG.mass]; exact_mod_cast (show Λ ≠ 0 by have := hG.lam1; omega)
  have hs : D.s ≠ 0 := by have := hG.s1; show g.s ≠ 0; omega
  have pV := FrontTableRef.termsV_perm D hm hs
  have pQ := FrontTableRef.termsQ_perm D hm hs
  have pM := FrontTableRef.termsMu_perm D hm hs
  have hlen : (FrontTableRef.myV D).length + (FrontTableRef.myQ D).length + (FrontTableRef.myMu D).length ≤ CN K := by
    have hsch := length_schedule_le g g.translation
    have e : D.schedule.length = D.termsV.length + D.termsQ.length + D.termsMu.length := by
      unfold UnionCheckData.schedule; simp [List.length_append]; omega
    rw [← pV.length_eq, ← pQ.length_eq, ← pM.length_eq, ← e]
    refine hsch.trans ?_
    unfold CN
    have h1 := hG.kp
    have h2 : g.s ≤ K := hG.s
    have h3 : 1 + 2 * (S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree) *
        (g.s + 1) ≤ 1 + 2 * K * (K + 1) := by
      have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1) (show g.s + 1 ≤ K + 1 by omega)
      omega
    calc 24 * (S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree) *
          (1 + 2 * (S.pcppAlg.coefficient * ((S.request z g.pair).circuit.size + 1) ^ S.pcppAlg.degree) *
            (g.s + 1)) ^ 4 ≤ 24 * K * (1 + 2 * K * (K + 1)) ^ 4 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 24 h1) (Nat.pow_le_pow_left h3 4)
      _ = 24 * K * (1 + 2 * K * (K + 1)) ^ 4 := rfl
  have b0 := flatMap_le (FrontTableRef.myV D) (fun t => Entry.entryWord (Bridge.entryOf 0 D.s t)) (EW K)
    (fun t ht => entry_le hG hsg 0 t (Or.inl (pV.mem_iff.2 ht)))
  have b1 := flatMap_le (FrontTableRef.myQ D) (fun t => Entry.entryWord (Bridge.entryOf 1 D.s t)) (EW K)
    (fun t ht => entry_le hG hsg 1 t (Or.inr (Or.inl (pQ.mem_iff.2 ht))))
  have b2 := flatMap_le (FrontTableRef.myMu D) (fun t => Entry.entryWord (Bridge.entryOf 2 D.s t)) (EW K)
    (fun t ht => entry_le hG hsg 2 t (Or.inr (Or.inr (pM.mem_iff.2 ht))))
  unfold twWords
  simp only [List.length_append]
  have := Nat.mul_le_mul_right (EW K) hlen
  rw [Nat.add_mul, Nat.add_mul] at this
  omega

end Env

end NearCubicWires.WireExponent3_5.UnionMachine.FrontSemCap1

end
