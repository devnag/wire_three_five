import Lean
import Proof.Wire_3_5.UnionMachine.FrontOutRefBase
import Proof.Wire_3_5.UnionMachine.FrontTWBridge5
import Proof.Wire_3_5.Transfer.TransferUnionComplete
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Proof.Wire_3_5.UnionMachine.FrontCallOkBase


noncomputable section
set_option maxRecDepth 4096


/-! # C6 front, the callOk bridge: a call's admissibility is its circuits' and carriers' envelope bits

The table writer conjoins, per emitted call, the envelope bits of its four circuits and its named carriers
(`FrontTW.okT fD fE`, M17); its semantics (`FrontTW.twSem`) takes `hokV`/`hokM`: for every tuple of the factors'
supports, `callOkI` (`[I.Call r]`, M41) is that conjunction. Past the onset (`I.StarAt q`, `B.FitsAt q`, two names)
the other conjuncts of `PrimitiveInputs.Call` hold (P3:3083-3094: every tuple's gates lie in the named carriers, the
translation is well formed): **`callOk_V`**, **`callOk_Mu`** at `fD C = [descriptionBits C ≤ (q+1)^descDeg]`,
`fE X = [X.WithinEnvelope carrierDeg]`.

Paper quantity: the per-call hypothesis `PrimitiveInputs.Call` (P3:3083-3094). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCallOk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTW NearCubicWires.WireExponent3_5.UnionMachine.FrontOutRef

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} {S : UnionSetup I} {N : ℕ}
  {z : BitInput N}

/-- A factor's support lies in `X`'s carrier (`sx`, `one`, `par`) or `Y`'s (`sy`). -/
theorem cand_gates (g : UnionGuess S z) (hpar : ∀ (m : Mode) (n : ℕ), m.gates (S.parityAtom m n ∅) = [])
    (X Y : PcppVar g.pcpp) (f : FK) (a : g.AtomIx) (ha : a ∈ cand (g.checkData g.translation) X Y f) :
    (g.mode.gates (g.circ a)).Sublist (g.carrier X) ∨ (g.mode.gates (g.circ a)).Sublist (g.carrier Y) := by
  cases f with
  | one =>
    have ha' : a = Sum.inl () := List.mem_singleton.mp ha
    rw [ha']
    left; rw [g.gates_const]; exact List.nil_sublist _
  | par =>
    have ha' : a = Sum.inr (Sum.inr X) := List.mem_singleton.mp ha
    rw [ha']
    left
    by_cases hs : g.sysBit X = true
    · exact g.gates_parity_sublist X hs
    · have hsup : g.support X = ∅ := by
        unfold UnionGuess.support
        rw [dif_neg]
        simpa [UnionGuess.sysBit] using hs
      show (g.mode.gates (g.parity X)).Sublist _
      unfold UnionGuess.parity
      rw [hsup, hpar]
      exact List.nil_sublist _
  | sx =>
    obtain ⟨b, -, hb⟩ := List.mem_filterMap.mp ha
    by_cases hs : (g.checkData g.translation).sign X b = 0
    · simp [hs] at hb
    · rw [if_neg hs] at hb
      rw [← Option.some.inj hb]
      left; exact g.gates_atom_sublist X b
  | sy =>
    obtain ⟨b, -, hb⟩ := List.mem_filterMap.mp ha
    by_cases hs : (g.checkData g.translation).sign Y b = 0
    · simp [hs] at hb
    · rw [if_neg hs] at hb
      rw [← Option.some.inj hb]
      right; exact g.gates_atom_sublist Y b

/-- **A `V`/`Q` call's admissibility is its envelope bits** (past the onset). -/
theorem callOk_V (g : UnionGuess S z) (hpar : ∀ (m : Mode) (n : ℕ), m.gates (S.parityAtom m n ∅) = [])
    (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount)
    (pos : Fin (2 ^ g.pcpp.clauseBits) × Fin 2) (pat : Fin 4 → FK) (t : Fin 4 → g.AtomIx)
    (ht : ∀ k, t k ∈ cand (g.checkData g.translation) (posVar g.pcpp pos.1 pos.2) (posVar g.pcpp pos.1 pos.2) (pat k)) :
    callOkI (I := I) ((g.checkData g.translation).vCall pos t) =
      okT (g.checkData g.translation) (fDI (I := I) g.mode g.q) (fEI (I := I)) (posVar g.pcpp pos.1 pos.2)
        (posVar g.pcpp pos.1 pos.2) false t := by
  rw [g.checkData_vCall]
  unfold callOkI okT
  rw [g.checkData_circ]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_false, Bool.true_or, and_true, fDI, fEI]
  set X := posVar g.pcpp pos.1 pos.2
  constructor
  · intro h
    obtain ⟨-, henv, hdesc, -⟩ := h
    have hd : ∀ k : Fin 4, g.mode.descriptionBits (g.circ (t k)) ≤ (g.q + 1) ^ I.descDeg := fun k => hdesc k
    exact ⟨⟨⟨⟨hd 0, hd 1⟩, hd 2⟩, hd 3⟩, henv _ (List.mem_singleton_self _)⟩
  · rintro ⟨⟨⟨⟨d0, d1⟩, d2⟩, d3⟩, hX⟩
    have hsub : ∀ k, (g.mode.gates (g.circ (t k))).Sublist (g.carrier X) := fun k => by
      rcases cand_gates g hpar X X (pat k) (t k) (ht k) with h | h <;> exact h
    refine ⟨fun k => ((hsub k).subperm).trans ?_, ?_, ?_, ?_, g.translationOk hStar _ rfl rfl, hStar, hFit⟩
    · simp only [UnionGuess.vCall, tupleRequest, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact List.Subperm.refl _
    · intro Y hY
      rw [List.mem_singleton.mp hY]; exact hX
    · intro k
      rcases k with ⟨_ | _ | _ | _ | k, hk⟩
      · exact d0
      · exact d1
      · exact d2
      · exact d3
      · exact absurd (show k + 1 + 1 + 1 + 1 < 4 from hk) (by omega)
    · show 1 ≤ I.nameCount
      omega

/-- **A `μ` call's admissibility is its envelope bits** (past the onset). -/
theorem callOk_Mu (g : UnionGuess S z) (hpar : ∀ (m : Mode) (n : ℕ), m.gates (S.parityAtom m n ∅) = [])
    (hStar : I.StarAt g.q) (hFit : B.FitsAt g.q) (hname : 2 ≤ I.nameCount)
    (i : Fin (2 ^ g.pcpp.clauseBits)) (pat : Fin 4 → FK) (t : Fin 4 → g.AtomIx)
    (ht : ∀ k, t k ∈ cand (g.checkData g.translation) (posVar g.pcpp i 0) (posVar g.pcpp i 1) (pat k)) :
    callOkI (I := I) ((g.checkData g.translation).muCall i t) =
      okT (g.checkData g.translation) (fDI (I := I) g.mode g.q) (fEI (I := I)) (posVar g.pcpp i 0)
        (posVar g.pcpp i 1) true t := by
  rw [g.checkData_muCall]
  unfold callOkI okT
  rw [g.checkData_circ]
  apply Bool.eq_iff_iff.2
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_true, Bool.false_or, fDI, fEI]
  set X := posVar g.pcpp i 0
  set Y := posVar g.pcpp i 1
  constructor
  · intro h
    obtain ⟨-, henv, hdesc, -⟩ := h
    have hd : ∀ k : Fin 4, g.mode.descriptionBits (g.circ (t k)) ≤ (g.q + 1) ^ I.descDeg := fun k => hdesc k
    exact ⟨⟨⟨⟨⟨hd 0, hd 1⟩, hd 2⟩, hd 3⟩, henv _ (List.mem_cons_self ..)⟩,
      henv _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · rintro ⟨⟨⟨⟨⟨d0, d1⟩, d2⟩, d3⟩, hX⟩, hY⟩
    refine ⟨fun k => ?_, ?_, ?_, ?_, g.translationOk hStar _ rfl rfl, hStar, hFit⟩
    · simp only [UnionGuess.muCall, tupleRequest, List.flatten_cons, List.flatten_nil, List.append_nil]
      rcases cand_gates g hpar X Y (pat k) (t k) (ht k) with h | h
      · exact (h.trans (List.sublist_append_left _ _)).subperm
      · exact (h.trans (List.sublist_append_right _ _)).subperm
    · intro Z hZ
      have hZ0 : Z ∈ [g.carrier X, g.carrier Y] := hZ
      rcases List.mem_cons.mp hZ0 with h | h
      · rw [h]; exact hX
      · rw [List.mem_singleton.mp h]; exact hY
    · intro k
      rcases k with ⟨_ | _ | _ | _ | k, hk⟩
      · exact d0
      · exact d1
      · exact d2
      · exact d3
      · exact absurd (show k + 1 + 1 + 1 + 1 < 4 from hk) (by omega)
    · show 2 ≤ I.nameCount
      exact hname

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCallOk

end
