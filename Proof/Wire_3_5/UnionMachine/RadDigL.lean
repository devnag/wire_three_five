import Proof.Wire_3_5.UnionMachine.RadDig

/-! # RADIX, stage 5a (9): the digit loop (P3:2596-2604)

The row's `τ₀` digits, in order: the digit populations `ls = [gis_0, …, gis_{τ₀−1}]` are read in place from `DigsW`'s
word `ls.flatMap gisWord` (`Digs.digsWord`) on `GS`; each digit appends its `2(M+1)` factor blocks to the record `O`
and its table word to `T` (`RadDig.digBody_spec`).

* `post` (the streams after some digits), `post_nil`, **`digOut_post`**;
* `digIn_post`, `digIn_setv`: the digit's entry survives;
* `digLoop` / **`digLoop_spec`**: the record gets `ls.flatMap (digBlocks D · G row)`, `T` gets
  `ls.flatMap (tdW D ·.length)` (head at its end), `GS` passes the digit word; every register as at the entry but the
  loop counter (`0`).

Paper quantity of the main type: the RADIX row's factor blocks (the store `radBlocksC`, row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadDigL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec NearCubicWires.WireExponent3_5.UnionMachine.RadDig

variable {ns nr : ℕ} (cap : ℕ)

theorem flatMap_take_succ {α β : Type} (f : α → List β) (ls : List α) (k : ℕ) (hk : k < ls.length) :
    (ls.take (k + 1)).flatMap f = (ls.take k).flatMap f ++ f ls[k] := by
  rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
  simp

theorem flatMap_split {α β : Type} (f : α → List β) (ls : List α) (k : ℕ) :
    ls.flatMap f = (ls.take k).flatMap f ++ (ls.drop k).flatMap f := by
  rw [← List.flatMap_append, List.take_append_drop]

theorem flatMap_take_len_le {α β : Type} (f : α → List β) (ls : List α) {k m : ℕ} (h : k ≤ m) :
    ((ls.take k).flatMap f).length ≤ ((ls.take m).flatMap f).length := by
  have e : ls.take k = (ls.take m).take k := by rw [List.take_take, min_eq_left h]
  rw [e, flatMap_split f (ls.take m) k, List.length_append]
  omega

section Loop
variable (O T GS : Fin (ns + 1)) (OP : Fin nr)

/-- The streams after some digits: `uO` appended to the record, `uT` to `T` (head at its end), `GS` `g` cells on. -/
def post (σ : WState ns nr) (uO uT : List Bool) (g : ℕ) : WState ns nr :=
  (((appendO σ O OP uO).sets T (σ.st T ++ uT)).seth T (σ.sh T + uT.length)).seth GS (σ.sh GS + g)

theorem post_nil (σ : WState ns nr) : post O T GS OP σ [] [] 0 = σ := by
  unfold post
  rw [appendO_nil]
  apply WState.eq
  · funext j
    by_cases hG : j = GS
    · subst hG; simp
    · by_cases hT : j = T
      · subst hT; simp [Function.update_apply, hG]
      · simp [Function.update_apply, hG, hT]
  · funext j; by_cases hT : j = T
    · subst hT; simp
    · simp [Function.update_apply, hT]
  · simp
  · simp

theorem digOut_post (hOT : O ≠ T) (hOG : O ≠ GS) (hTG : T ≠ GS) (σ : WState ns nr) (uO uT : List Bool) (g : ℕ)
    (Dl : ListData) (gis : List ℕ) (G row : ℕ) :
    digOut O T GS OP (post O T GS OP σ uO uT g) Dl gis G row =
      post O T GS OP σ (uO ++ RadBlk.digBlocks Dl gis G row) (uT ++ tdW Dl gis.length) (g + (gisWord gis).length) := by
  unfold digOut post
  apply WState.eq
  · funext j
    by_cases hG : j = GS
    · subst hG; simp [Function.update_apply, Ne.symm hTG, Ne.symm hOG]; omega
    · by_cases hT : j = T
      · subst hT; simp [Function.update_apply, hG, Ne.symm hOT]; omega
      · by_cases hO : j = O
        · subst hO; simp [Function.update_apply, hG, hT]; omega
        · simp [Function.update_apply, hG, hT, hO]
  · funext j
    by_cases hT : j = T
    · subst hT; simp [Function.update_apply, Ne.symm hOT]
    · by_cases hO : j = O
      · subst hO; simp [Function.update_apply, hT, hOT]
      · simp [Function.update_apply, hT, hO]
  · funext q
    by_cases hq : q = OP
    · subst hq; simp; omega
    · simp [Function.update_apply, hq]
  · simp

end Loop

section Loop2
variable (Z : Fin 11 ↪ Fin nr) (Rg : Fin radBlkK ↪ Fin nr)

theorem digIn_post {O T TS GS : Fin (ns + 1)} {Sc : Fin 2 → Fin (ns + 1)} {OP : Fin nr} {Dl : ListData} {G row : ℕ}
    {σ : WState ns nr} (h : DigIn Z Rg O T TS GS Sc OP Dl G row σ) (hOS : O ≠ TS) (hGS : GS ≠ TS)
    (uO uT : List Bool) (g : ℕ) : DigIn Z Rg O T TS GS Sc OP Dl G row (post O T GS OP σ uO uT g) := by
  obtain ⟨hOT, hOG, hTG, hTTS, hSI, hSN, hRO, hZO, hZR, ⟨qS, hS⟩, ho, hT, hSc, h1, h2, h5, hz, h9, hzz⟩ := h
  refine ⟨hOT, hOG, hTG, hTTS, hSI, hSN, hRO, hZO, hZR, ⟨qS, ?_⟩, ?_, ?_, fun i => ?_, ?_, ?_, ?_, fun j a b c => ?_, ?_,
    fun i hi => ?_⟩
  · simp [post, Function.update_apply, Ne.symm hGS, Ne.symm hTTS, Ne.symm hOS, hS]
  · simp [post, Function.update_apply, Ne.symm hOG, hOG, hOT, ho]
  · simp [post, Function.update_apply, Ne.symm hTG, hTG, hT]
  · simp [post, Function.update_apply, (hSN i).1, (hSN i).2.1, (hSN i).2.2, hSc i]
  · simp [post, Function.update_apply, hRO 1, h1]
  · simp [post, Function.update_apply, hRO 2, h2]
  · simp [post, Function.update_apply, hRO 5, h5]
  · simp [post, Function.update_apply, hRO j, hz j a b c]
  · simp [post, Function.update_apply, hZO 9, h9]
  · simp [post, Function.update_apply, hZO i, hzz i hi]

theorem digIn_setv {O T TS GS : Fin (ns + 1)} {Sc : Fin 2 → Fin (ns + 1)} {OP : Fin nr} {Dl : ListData} {G row : ℕ}
    {σ : WState ns nr} (h : DigIn Z Rg O T TS GS Sc OP Dl G row σ) (r : Fin nr) (hZ : ∀ i, Z i ≠ r)
    (hR : ∀ j, Rg j ≠ r) (x : ℕ) : DigIn Z Rg O T TS GS Sc OP Dl G row (σ.setv r x) := by
  obtain ⟨hOT, hOG, hTG, hTTS, hSI, hSN, hRO, hZO, hZR, hS, ho, hT, hSc, h1, h2, h5, hz, h9, hzz⟩ := h
  refine ⟨hOT, hOG, hTG, hTTS, hSI, hSN, hRO, hZO, hZR, hS, ho, hT, hSc, ?_, ?_, ?_, fun j a b c => ?_, ?_,
    fun i hi => ?_⟩
  · simp [Function.update_apply, hR 1, h1]
  · simp [Function.update_apply, hR 2, h2]
  · simp [Function.update_apply, hR 5, h5]
  · simp [Function.update_apply, hR j, hz j a b c]
  · simp [Function.update_apply, hZ 9, h9]
  · simp [Function.update_apply, hZ i, hzz i hi]

/-- **The digit loop** (counter `Dc`). -/
def digLoop (Wb : RadSpec3.RadBlockW3) (O T TS GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (OP Dc : Fin nr) :
    WM ns nr :=
  .whr Dc (.seq (.dec Dc) (digBody Z Rg Wb O T TS GS Sc OP))

theorem digLoop_spec (Wb : RadSpec3.RadBlockW3) (O T TS GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1))
    (OP Dc : Fin nr) (Dl : ListData) (G row : ℕ) (ls : List (List ℕ)) (σ : WState ns nr)
    (hin : DigIn Z Rg O T TS GS Sc OP Dl G row σ) (hOS : O ≠ TS) (hGS : GS ≠ TS)
    (hZD : ∀ i, Z i ≠ Dc) (hRD : ∀ j, Rg j ≠ Dc) (hDO : Dc ≠ OP) (hDc : σ.val Dc = ls.length)
    (restG : List Bool) (hG : (σ.st GS).drop (σ.sh GS) = ls.flatMap gisWord ++ restG)
    (hLG : ∀ gis ∈ ls, gis.length ≤ G) (hc1 : ∀ gis ∈ ls, (gis.flatMap RadCnt.itemW).length ≤ cap) (hc2 : G < cap)
    (hc3 : (levelWord Dl.M Dl.J Dl.W (rowsOf Dl G)).length ≤ cap) (hc4 : ∀ gis ∈ ls, capC Dl gis.length ≤ cap)
    (hcM : Dl.M + 1 ≤ cap) (hcn : ls.length ≤ cap)
    (hneed : ∀ gis ∈ ls, ∀ t ≤ Dl.M, ∀ sgn : Bool,
      ∀ olen ≤ (σ.st O).length + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length,
        Wb.need (blkSize Dl gis G row t sgn olen) ≤ cap)
    (hop : σ.val OP + (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length ≤ cap)
    (c : ℕ) (hcost : ∀ gis ∈ ls, digCost cap Wb Dl gis G ≤ c) :
    WExec cap (digLoop Z Rg Wb O T TS GS Sc OP Dc) σ
      ((post O T GS OP σ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)
        (ls.flatMap fun gis => tdW Dl gis.length) (ls.flatMap gisWord).length).setv Dc 0)
      (ls.length * (c + 4) + 1) := by
  let Sf : ℕ → WState ns nr := fun k =>
    (post O T GS OP σ ((ls.take k).flatMap fun gis => RadBlk.digBlocks Dl gis G row)
      ((ls.take k).flatMap fun gis => tdW Dl gis.length) ((ls.take k).flatMap gisWord).length).setv Dc (ls.length - k)
  have hS0 : Sf 0 = σ := by
    simp only [Sf, List.take_zero, List.flatMap_nil, List.length_nil, Nat.sub_zero]
    rw [post_nil, ← hDc, wsetv_same]
  have hSn : Sf ls.length = (post O T GS OP σ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row)
      (ls.flatMap fun gis => tdW Dl gis.length) (ls.flatMap gisWord).length).setv Dc 0 := by
    simp only [Sf, List.take_length, Nat.sub_self]
  have hK : ∀ k ≤ ls.length, (Sf k).val Dc = ls.length - k := fun k _ => by simp [Sf]
  have hbody : ∀ k < ls.length, WExec cap (digBody Z Rg Wb O T TS GS Sc OP)
      ((Sf k).setv Dc (ls.length - k - 1)) (Sf (k + 1)) c := by
    intro k hk
    have hmem : ls[k] ∈ ls := List.getElem_mem hk
    set τ := (post O T GS OP σ ((ls.take k).flatMap fun gis => RadBlk.digBlocks Dl gis G row)
      ((ls.take k).flatMap fun gis => tdW Dl gis.length) ((ls.take k).flatMap gisWord).length).setv Dc
        (ls.length - k - 1) with hτ
    have e1 : (Sf k).setv Dc (ls.length - k - 1) = τ := by simp only [Sf, hτ, wsetv_setv]
    rw [e1]
    have hinτ : DigIn Z Rg O T TS GS Sc OP Dl G row τ := digIn_setv Z Rg (digIn_post Z Rg hin hOS hGS _ _ _) Dc hZD hRD _
    have hGτ : (τ.st GS).drop (τ.sh GS) = gisWord ls[k] ++ ((ls.drop (k + 1)).flatMap gisWord ++ restG) := by
      have e : τ.sh GS = σ.sh GS + ((ls.take k).flatMap gisWord).length := by simp [τ, post]
      have e2 : τ.st GS = σ.st GS := by
        simp [τ, post, Function.update_apply, Ne.symm hin.TG, Ne.symm hin.OG]
      have hd : (σ.st GS).drop (σ.sh GS + ((ls.take k).flatMap gisWord).length) =
          (ls.drop k).flatMap gisWord ++ restG :=
        dropAppend (by rw [hG, flatMap_split gisWord ls k, List.append_assoc])
      rw [e, e2, hd, List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
    have hlenB := flatMap_take_len_le (fun gis => RadBlk.digBlocks Dl gis G row) ls (Nat.succ_le_of_lt hk)
    have hlenB' := flatMap_take_len_le (fun gis => RadBlk.digBlocks Dl gis G row) ls (le_refl ls.length)
    rw [flatMap_take_succ _ ls k hk, List.length_append] at hlenB
    rw [List.take_length] at hlenB'
    have hlenN : ((ls.take ls.length).flatMap fun gis => RadBlk.digBlocks Dl gis G row).length =
        (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length := by rw [List.take_length]
    have hlenK := flatMap_take_len_le (fun gis => RadBlk.digBlocks Dl gis G row) ls (le_of_lt hk)
    have hlenA := flatMap_take_len_le (fun gis => RadBlk.digBlocks Dl gis G row) ls (Nat.succ_le_of_lt hk)
    rw [hlenN] at hlenA
    have hstO : (τ.st O).length = (σ.st O).length + ((ls.take k).flatMap fun gis => RadBlk.digBlocks Dl gis G row).length := by
      simp [τ, post, Function.update_apply, hin.OT]
    have hvOP : τ.val OP = σ.val OP + ((ls.take k).flatMap fun gis => RadBlk.digBlocks Dl gis G row).length := by
      simp [τ, post, Function.update_apply, Ne.symm hDO]
    have hA : ((ls.take k).flatMap fun gis => RadBlk.digBlocks Dl gis G row).length +
        (RadBlk.digBlocks Dl ls[k] G row).length ≤ (ls.flatMap fun gis => RadBlk.digBlocks Dl gis G row).length := by
      have h' := hlenA
      rw [flatMap_take_succ _ ls k hk, List.length_append] at h'
      exact h'
    have hstep := digBody_spec cap Z Rg Wb O T TS GS Sc OP Dl ls[k] G row τ hinτ _ hGτ (hLG _ hmem) (hc1 _ hmem) hc2 hc3
      (hc4 _ hmem) hcM
      (fun t ht sgn olen hol => hneed _ hmem t ht sgn olen (by rw [hstO] at hol; omega))
      (by rw [hvOP]; omega)
    refine WExec.cast cap hstep ?_ (hcost _ hmem)
    have ecomm : digOut O T GS OP τ Dl ls[k] G row = (digOut O T GS OP (post O T GS OP σ
        ((ls.take k).flatMap fun gis => RadBlk.digBlocks Dl gis G row)
        ((ls.take k).flatMap fun gis => tdW Dl gis.length) ((ls.take k).flatMap gisWord).length) Dl ls[k] G row).setv
          Dc (ls.length - k - 1) := by
      simp only [τ, digOut]
      apply WState.eq
      · simp
      · simp
      · funext q
        by_cases hq : q = Dc
        · subst hq; simp [Function.update_apply, hDO]
        · by_cases hq2 : q = OP
          · subst hq2; simp [Function.update_apply, Ne.symm hDO]
          · simp [Function.update_apply, hq, hq2]
      · simp
    rw [ecomm, digOut_post O T GS OP hin.OT hin.OG hin.TG]
    simp only [Sf, flatMap_take_succ _ ls k hk, List.length_append]
    congr 1
  have hloop := UnionMachine.Round.wloop cap Dc (digBody Z Rg Wb O T TS GS Sc OP) c ls.length Sf hK hcn hbody
  rw [hS0, hSn] at hloop
  exact hloop

end Loop2

end NearCubicWires.WireExponent3_5.UnionMachine.RadDigL
