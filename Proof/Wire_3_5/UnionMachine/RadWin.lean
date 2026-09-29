import Proof.Wire_3_5.UnionMachine.RadDigs
import Proof.Wire_3_5.UnionMachine.RadFieldsP

/-! # RADIX, stage 5a (1): the fixed hash's window word (P3:2604)

The table builder (`Hash4.build_spec`) reads `winWord M L J W = unary M ++ unary L ++ unary J ++ winRecs ++ [false]`
on its window stream. The setup builds the table ONCE, at `L = Lmax = G`, from the level records `winRecs`
(W6's word on stream `131`, of length `S2`) and the numbers `M`, `G`, `J`, `S2` in registers.

* `copyP` / **`copyP_spec`**: the next `K` bits of a stream, appended to another (position register `OP`);
* `winP` / **`winP_spec`**: on a blank stream, `winWord M G J W` with its head back at `0`; the source rewound.

Paper quantity of the main type: the fixed hash's level windows `W_j` (the table builder's input word). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadWin
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.UnionMachine.RadFields

variable {ns nr : ℕ} (cap : ℕ)

/-- The next `K` bits of stream `S`, appended to `O`, consuming `K`. -/
def copyP (O S : Fin (ns + 1)) (OP SP K : Fin nr) : WM ns nr :=
  .whr K (.seq (.dec K) (.seq (.ifs S (emitW O OP [true]) (emitW O OP [false])) (WM.fwdC S SP)))

theorem copyP_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K : Fin nr) (hKO : K ≠ OP) (hKS : K ≠ SP)
    (hOSP : OP ≠ SP) (w : List Bool) (σ : WState ns nr) (hKn : σ.val K = w.length)
    (hw : ∀ i < w.length, readTapeBit (σ.st S) (σ.sh S + i) = w.getD i false)
    (ho : σ.sh O = (σ.st O).length) (hc : σ.val OP + w.length ≤ cap) (hsp : σ.val SP + w.length ≤ cap)
    (hn : w.length ≤ cap) :
    WExec cap (copyP O S OP SP K) σ
      ((((appendO σ O OP w).seth S (σ.sh S + w.length)).setv SP (σ.val SP + w.length)).setv K 0)
      (w.length * (8 + 1 + 1 + 5 + 4) + 1) := by
  let S' : ℕ → WState ns nr := fun k =>
    (((appendO σ O OP (w.take k)).seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K (w.length - k)
  have hS0 : S' 0 = σ := by
    simp only [S', List.take_zero, appendO_nil, Nat.add_zero, Nat.sub_zero, ← hKn]
    apply WState.eq <;> simp [Function.update_eq_self]
  have hloop := UnionMachine.Round.wloop cap K
    (.seq (.ifs S (emitW O OP [true]) (emitW O OP [false])) (WM.fwdC S SP)) (8 + 1 + 1 + 5) w.length S'
    (fun k _ => by simp [S'])
    hn
    (fun k hk => by
      set τ := ((((appendO σ O OP (w.take k)).seth S (σ.sh S + k)).setv SP (σ.val SP + k)).setv K
        (w.length - k - 1)) with hτ
      have hτS : (S' k).setv K (w.length - k - 1) = τ := by simp only [S', hτ, wsetv_setv]
      rw [hτS]
      have hlen : (w.take k).length = k := by rw [List.length_take, min_eq_left (by omega)]
      have hbit : wbit τ S = w.getD k false := by
        simp only [hτ, wbit]
        simp [hOS.symm, Function.update_apply, hw k hk]
      have hoτ : τ.sh O = (τ.st O).length := by simp [hτ, hOS, ho]
      have hcτ : τ.val OP + [w.getD k false].length ≤ cap := by
        simp only [hτ]
        simp [Function.update_apply, Ne.symm hKO, hOSP, hlen]
        omega
      have hE : WExec cap (.ifs S (emitW O OP [true]) (emitW O OP [false])) τ
          (appendO τ O OP [w.getD k false]) (8 + 1) := by
        cases hb : w.getD k false
        · rw [hb] at hbit hcτ
          exact WExec.ifsF hbit (emitW_spec cap O OP [false] τ hoτ hcτ)
        · rw [hb] at hbit hcτ
          exact WExec.ifsT hbit (emitW_spec cap O OP [true] τ hoτ hcτ)
      have hF := wfwdC_spec cap S SP (appendO τ O OP [w.getD k false])
        (by simp [hτ, Function.update_apply, Ne.symm hKS, Ne.symm hOSP]; omega)
      refine WExec.cast cap (WExec.seq hE hF) ?_ (by omega)
      have htake : w.take (k + 1) = w.take k ++ [w.getD k false] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.getD_eq_getElem _ _ hk]
      simp only [S', hτ, htake]
      apply WState.eq
      · funext j
        by_cases hjS : j = S
        · subst hjS; simp [Function.update_apply, Ne.symm hOS]; try omega
        · by_cases hj : j = O
          · subst hj; simp [Function.update_apply, hjS]; try omega
          · simp [Function.update_apply, hj, hjS]
      · funext j; by_cases hj : j = O
        · subst hj; simp [hOS]
        · simp [Function.update_apply, hj]
      · funext j; by_cases hj : j = K
        · subst hj; simp [Function.update_apply, hKS, hKO]; omega
        · by_cases hjS : j = SP
          · subst hjS; simp [Function.update_apply, hj, Ne.symm hOSP]; omega
          · by_cases hjO : j = OP
            · subst hjO; simp [Function.update_apply, hj, hjS]; omega
            · simp [Function.update_apply, hj, hjS, hjO]
      · simp)
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp only [S', List.take_length, Nat.sub_self]

theorem ao_seth (σ : WState ns nr) (i o : Fin (ns + 1)) (hio : i ≠ o) (OP : Fin nr) (x : ℕ) (u : List Bool) :
    appendO (σ.seth i x) o OP u = (appendO σ o OP u).seth i x := by
  apply WState.eq
  · funext j
    by_cases hj : j = i
    · subst hj; simp [Function.update_apply, hio]
    · simp [Function.update_apply, hj, Ne.symm hio]
  · simp
  · simp
  · simp

theorem reps_true (n : ℕ) : reps n [true] = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [reps_succ, ih, List.replicate_succ']

/-- The unary field `1^A 0` from register `A` (kept). -/
def unaryE (O : Fin (ns + 1)) (OP A K T : Fin nr) : WM ns nr :=
  .seq (repRegW O OP A K T [true]) (emitW O OP [false])

theorem unaryE_spec (O : Fin (ns + 1)) (OP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T)
    (hKO : K ≠ OP) (σ : WState ns nr) (hK : σ.val K = 0) (hT : σ.val T = 0) (ho : σ.sh O = (σ.st O).length)
    (hA : σ.val A ≤ cap) (hc : σ.val OP + σ.val A + 1 ≤ cap) :
    WExec cap (unaryE O OP A K T) σ (appendO σ O OP (FinalPass.ListEval.unary (σ.val A))) (30 * σ.val A + 20) := by
  have h1 := repRegW_spec cap O OP A K T hAK hAT hKT hKO [true] σ hK hT ho hA (by simp; omega)
  rw [reps_true] at h1
  have h2 := emitW_spec cap O OP [false] (appendO σ O OP (List.replicate (σ.val A) true)) (ao_ho O OP σ _ ho)
    (by rw [ao_val_op]; simp; omega)
  rw [appendO_append] at h2
  have e : FinalPass.ListEval.unary (σ.val A) = List.replicate (σ.val A) true ++ [false] := rfl
  rw [e]
  exact WExec.mono (WExec.seq h1 h2) (by simp; omega)

/-- **The window word's writer**: `unary M ++ unary G ++ unary J`, then the next `S2` bits of `S`, then `0`; `S` and
`O` rewound (by `SP`, `OP`). -/
def winP (O S : Fin (ns + 1)) (OP SP K T A1 A2 A3 A4 : Fin nr) : WM ns nr :=
  .seq (unaryE O OP A1 K T) (.seq (unaryE O OP A2 K T) (.seq (unaryE O OP A3 K T) (.seq (FinalPass.Hash4.wcopyR A4 K T)
    (.seq (copyP O S OP SP K) (.seq (emitW O OP [false]) (.seq (WM.rewind S SP) (WM.rewind O OP)))))))

/-- The window word's writer's cost. -/
def winCost (M G J w : ℕ) : ℕ :=
  (30 * M + 20) + 1 + ((30 * G + 20) + 1 + ((30 * J + 20) + 1 + ((18 * w + 3) + 1 + ((w * 19 + 1) + 1 +
    (8 + 1 + ((5 * w + 1) + 1 + (5 * (M + G + J + w + 4) + 1)))))))

/-- **The window word, written**: on a blank `O` (head `0`, `OP = 0`) from `S` holding `w ++ rest` at head `0`
(`SP = 0`) and `M, G, J, |w|` in `A1 … A4`, `O` becomes `unary M ++ unary G ++ unary J ++ w ++ [false]`, head `0`;
everything else is back. -/
theorem winP_spec (O S : Fin (ns + 1)) (hOS : O ≠ S) (OP SP K T A1 A2 A3 A4 : Fin nr)
    (hd : [OP, SP, K, T, A1, A2, A3, A4].Nodup) (σ : WState ns nr) (w rest : List Bool) (M G J : ℕ)
    (hO : σ.st O = []) (hOh : σ.sh O = 0) (hS : σ.st S = w ++ rest) (hSh : σ.sh S = 0)
    (hOP : σ.val OP = 0) (hSP : σ.val SP = 0) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (h1 : σ.val A1 = M) (h2 : σ.val A2 = G) (h3 : σ.val A3 = J) (h4 : σ.val A4 = w.length)
    (hc : M + G + J + w.length + 4 ≤ cap) :
    WExec cap (winP O S OP SP K T A1 A2 A3 A4) σ
      (σ.sets O (FinalPass.ListEval.unary M ++ FinalPass.ListEval.unary G ++ FinalPass.ListEval.unary J ++ w ++ [false]))
      (winCost M G J w.length) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, ⟨b1, b2, b3, b4, b5, b6⟩, ⟨c1, c2, c3, c4, c5⟩, ⟨d1, d2, d3, d4⟩,
    ⟨e1, e2, e3⟩, ⟨f1, f2⟩, g1, -⟩ := hd
  have hO0 : σ.sh O = (σ.st O).length := by rw [hO, hOh]; rfl
  -- the three unary fields
  have s1 := unaryE_spec cap O OP A1 K T (Ne.symm c2) (Ne.symm d1) c1 (Ne.symm a2) σ hK hT hO0
    (by rw [h1]; omega) (by rw [hOP, h1]; omega)
  rw [h1] at s1
  have l1 : (FinalPass.ListEval.unary M).length = M + 1 := by simp [FinalPass.ListEval.unary]
  have s2 := unaryE_spec cap O OP A2 K T (Ne.symm c3) (Ne.symm d2) c1 (Ne.symm a2)
    (appendO σ O OP (FinalPass.ListEval.unary M)) (by rw [ao_val_ne O OP _ _ (Ne.symm a2)]; exact hK)
    (by rw [ao_val_ne O OP _ _ (Ne.symm a3)]; exact hT) (ao_ho O OP σ _ hO0)
    (by rw [ao_val_ne O OP _ _ (Ne.symm a5), h2]; omega)
    (by rw [ao_val_op, ao_val_ne O OP _ _ (Ne.symm a5), hOP, h2, l1]; omega)
  rw [ao_val_ne O OP _ _ (Ne.symm a5), h2, appendO_append] at s2
  have l2 : (FinalPass.ListEval.unary M ++ FinalPass.ListEval.unary G).length = M + G + 2 := by
    simp [FinalPass.ListEval.unary]; omega
  have s3 := unaryE_spec cap O OP A3 K T (Ne.symm c4) (Ne.symm d3) c1 (Ne.symm a2)
    (appendO σ O OP (FinalPass.ListEval.unary M ++ FinalPass.ListEval.unary G))
    (by rw [ao_val_ne O OP _ _ (Ne.symm a2)]; exact hK) (by rw [ao_val_ne O OP _ _ (Ne.symm a3)]; exact hT)
    (ao_ho O OP σ _ hO0) (by rw [ao_val_ne O OP _ _ (Ne.symm a6), h3]; omega)
    (by rw [ao_val_op, ao_val_ne O OP _ _ (Ne.symm a6), hOP, h3, l2]; omega)
  rw [ao_val_ne O OP _ _ (Ne.symm a6), h3, appendO_append] at s3
  obtain ⟨U, hUdef⟩ : ∃ U, U = FinalPass.ListEval.unary M ++ FinalPass.ListEval.unary G ++ FinalPass.ListEval.unary J :=
    ⟨_, rfl⟩
  rw [← hUdef] at s3
  have lU : U.length = M + G + J + 3 := by rw [hUdef]; simp [FinalPass.ListEval.unary]; omega
  -- the count and the copy
  have s4 := FinalPass.Hash4.wcopyR_spec cap A4 K T (Ne.symm c5) (Ne.symm d4) c1 (appendO σ O OP U)
    (by rw [ao_val_ne O OP _ _ (Ne.symm a2)]; exact hK) (by rw [ao_val_ne O OP _ _ (Ne.symm a3)]; exact hT)
    (by rw [ao_val_ne O OP _ _ (Ne.symm a7), h4]; omega)
  rw [ao_val_ne O OP _ _ (Ne.symm a7), h4] at s4
  have s5 := copyP_spec cap O S hOS OP SP K (Ne.symm a2) (Ne.symm b1) a1 w ((appendO σ O OP U).setv K w.length)
    (by simp)
    (fun i hi => by
      have e1 : ((appendO σ O OP U).setv K w.length).st S = w ++ rest := by simp [hOS.symm, hS]
      have e2 : ((appendO σ O OP U).setv K w.length).sh S = 0 := by simp [hOS.symm, hSh]
      rw [e1, e2, Nat.zero_add]
      unfold readTapeBit
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD])
    (by simp [hO, hOh, lU])
    (by rw [WState.setv_val, Function.update_of_ne a2, ao_val_op, hOP, lU]; omega)
    (by rw [WState.setv_val, Function.update_of_ne b1, ao_val_ne O OP _ _ (Ne.symm a1), hSP]; omega)
    (by omega)
  have e5 : ((((appendO ((appendO σ O OP U).setv K w.length) O OP w).seth S
      (((appendO σ O OP U).setv K w.length).sh S + w.length)).setv SP
      (((appendO σ O OP U).setv K w.length).val SP + w.length)).setv K 0) =
      ((appendO σ O OP (U ++ w)).seth S w.length).setv SP w.length := by
    rw [appendO_setv _ O OP K (Ne.symm a2), appendO_append]
    apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [Function.update_apply, hOS.symm, hSh]
      · simp [Function.update_apply, hj]
    · simp
    · funext j; by_cases hj : j = K
      · subst hj; simp [Function.update_apply, b1, Ne.symm b1, a2, Ne.symm a2, hK]
      · by_cases hj2 : j = SP
        · subst hj2; simp [Function.update_apply, hj, a1, Ne.symm a1, hSP]
        · simp [Function.update_apply, hj, hj2]
    · simp
  rw [e5] at s5
  have s6 := emitW_spec cap O OP [false] (((appendO σ O OP (U ++ w)).seth S w.length).setv SP w.length)
    (by simp [hOS, hO, hOh]) (by simp [Function.update_apply, a1, hOP, lU]; omega)
  have e6 : appendO (((appendO σ O OP (U ++ w)).seth S w.length).setv SP w.length) O OP [false] =
      ((appendO σ O OP (U ++ w ++ [false])).seth S w.length).setv SP w.length := by
    rw [appendO_setv _ O OP SP (Ne.symm a1), ao_seth _ S O hOS.symm, appendO_append]
  rw [e6] at s6
  have s7 := wrewind_spec cap S SP w.length (((appendO σ O OP (U ++ w ++ [false])).seth S w.length).setv SP w.length)
    (by simp) (by simp; omega)
  have e7 : ((((appendO σ O OP (U ++ w ++ [false])).seth S w.length).setv SP w.length).setv SP 0).seth S
      ((((appendO σ O OP (U ++ w ++ [false])).seth S w.length).setv SP w.length).sh S - w.length) =
      appendO σ O OP (U ++ w ++ [false]) := by
    apply WState.eq
    · funext j; by_cases hj : j = S
      · subst hj; simp [Function.update_apply, hOS.symm, hSh]
      · simp [Function.update_apply, hj]
    · simp
    · funext j; by_cases hj : j = SP
      · subst hj; simp [Function.update_apply, Ne.symm a1, hSP]
      · simp [Function.update_apply, hj]
    · simp
  rw [e7] at s7
  have lW : (U ++ w ++ [false]).length = M + G + J + w.length + 4 := by simp [lU]; omega
  have s8 := wrewind_spec cap O OP (M + G + J + w.length + 4) (appendO σ O OP (U ++ w ++ [false]))
    (by rw [ao_val_op, hOP, lW]; omega) (by rw [ao_val_op, hOP, lW]; omega)
  have e8 : ((appendO σ O OP (U ++ w ++ [false])).setv OP 0).seth O
      ((appendO σ O OP (U ++ w ++ [false])).sh O - (M + G + J + w.length + 4)) = σ.sets O (U ++ w ++ [false]) := by
    apply WState.eq
    · funext j; by_cases hj : j = O
      · subst hj; simp [hOh, lU]; omega
      · simp [Function.update_apply, hj]
    · funext j; by_cases hj : j = O
      · subst hj; simp [hO]
      · simp [Function.update_apply, hj]
    · funext j; by_cases hj : j = OP
      · subst hj; simp [hOP]
      · simp [Function.update_apply, hj]
    · simp
  rw [e8] at s8
  rw [← hUdef]
  refine WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) ?_
  unfold winCost
  simp only [List.length_cons, List.length_nil]
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.RadWin
