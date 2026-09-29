import Proof.Wire_3_5.UnionMachine.RadTrunc2
import Proof.Wire_3_5.UnionMachine.RadSpec3

/-! # RADIX, stage 5a (7): one digit's factor blocks, both signs (P3:2585-2623)

Digit `d` of row `(g, p)` contributes, per sign (`+` then `−`) and per `t = 0, …, M`, the factor block
`marks (true :: blockC D L_d t sgn false labs_d)` to the record (`ListMachine.Row.radBlocksC`, store order). The block
writer is a parameter `Wb : RadSpec3.RadBlockW3` (`FinalPass.RadB.radBlockW3`): it appends one block and changes
nothing else, so its seven input registers survive the calls.

* `bw` (one block's word), `bws` (one sign's blocks), `digBlocks` (the digit's blocks);
* `tLoop` / **`tLoop_spec`**: `N := M + 1`, `N` block calls with `t = 0, 1, …` (`Rg 3`), `t` cleared;
* `sgnP` / **`sgnP_spec`**: `Rg 4 := 1`, the `+` blocks, `Rg 4 := 0`, the `−` blocks.

Paper quantity of the main type: the RADIX row's factor blocks of one digit (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadBlk
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

/-- One factor block's word. -/
def bw (Dl : ListData) (gis : List ℕ) (G row : ℕ) (sgn : Bool) (t : ℕ) : List Bool :=
  Streaming.marks (true :: blockC Dl gis.length t sgn false (CompilerMachine.Pool.labsOf G row gis))

/-- The first `k` blocks of one sign. -/
def bws (Dl : ListData) (gis : List ℕ) (G row : ℕ) (sgn : Bool) (k : ℕ) : List Bool :=
  (List.range k).flatMap (bw Dl gis G row sgn)

/-- **A digit's blocks**: the `M + 1` blocks of sign `+`, then those of sign `−`. -/
def digBlocks (Dl : ListData) (gis : List ℕ) (G row : ℕ) : List Bool :=
  bws Dl gis G row true (Dl.M + 1) ++ bws Dl gis G row false (Dl.M + 1)

theorem bws_succ (Dl : ListData) (gis : List ℕ) (G row : ℕ) (sgn : Bool) (k : ℕ) :
    bws Dl gis G row sgn (k + 1) = bws Dl gis G row sgn k ++ bw Dl gis G row sgn k := by
  simp [bws, List.range_succ, List.flatMap_append]

theorem bws_len_le (Dl : ListData) (gis : List ℕ) (G row : ℕ) (sgn : Bool) {k m : ℕ} (h : k ≤ m) :
    (bws Dl gis G row sgn k).length ≤ (bws Dl gis G row sgn m).length := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hk | hk
    · rw [bws_succ, List.length_append]; have := ih (by omega); omega
    · rw [show k = m + 1 by omega]

variable {ns nr : ℕ} (cap : ℕ) (Wb : RadSpec3.RadBlockW3)

/-- One sign's blocks: `N := M + 1` (from `Mr`; scratch `tmp`), `N` block calls with `t` in `Rg 3` counting up, then
`t` cleared. -/
def tLoop (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr) (OP Mr N tmp : Fin nr) :
    WM ns nr :=
  .seq (wcopyR Mr N tmp) (.seq (.inc N) (.seq (.whr N (.seq (.dec N) (.seq (Wb.prog O T GS Sc Rg OP) (.inc (Rg 3)))))
    (WM.clear (Rg 3))))

/-- The cost of one sign's blocks. -/
def tCost (M c : ℕ) : ℕ := (18 * M + 3) + 1 + (3 + 1 + (((M + 1) * (c + 1 + 3 + 4) + 1) + 1 + (3 * (M + 1) + 1)))

/-- The block writer's entry conditions that the calls keep (streams, the fixed registers). -/
structure BlkIn (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr) (OP : Fin nr)
    (Dl : ListData) (gis : List ℕ) (G row : ℕ) (σ : WState ns nr) : Prop where
  OT : O ≠ T
  OG : O ≠ GS
  TG : T ≠ GS
  ScI : Function.Injective Sc
  ScN : ∀ i, Sc i ≠ O ∧ Sc i ≠ T ∧ Sc i ≠ GS
  RgOP : ∀ j, Rg j ≠ OP
  Td : ∃ restT, (σ.st T).drop (σ.sh T) =
    FinalPass.ListEval.levelWord Dl.M Dl.J Dl.W (FinalPass.ListEval.rowsOf Dl gis.length) ++ restT
  Gd : ∃ restG, (σ.st GS).drop (σ.sh GS) = gisWord gis ++ restG
  ho : σ.sh O = (σ.st O).length
  Sc0 : ∀ i, σ.st (Sc i) = [] ∧ σ.sh (Sc i) = 0
  r0 : σ.val (Rg 0) = gis.length
  r1 : σ.val (Rg 1) = G
  r2 : σ.val (Rg 2) = row
  r5 : σ.val (Rg 5) = 3 * ListMachine.listBound Dl
  r6 : σ.val (Rg 6) = capC Dl gis.length
  rz : ∀ j : Fin radBlkK, 7 ≤ j.val → σ.val (Rg j) = 0

theorem BlkIn.ao {O T GS : Fin (ns + 1)} {Sc : Fin 2 → Fin (ns + 1)} {Rg : Fin radBlkK ↪ Fin nr} {OP : Fin nr}
    {Dl : ListData} {gis : List ℕ} {G row : ℕ} {σ : WState ns nr} (h : BlkIn O T GS Sc Rg OP Dl gis G row σ)
    (u : List Bool) : BlkIn O T GS Sc Rg OP Dl gis G row (appendO σ O OP u) := by
  obtain ⟨hOT, hOG, hTG, hSI, hSN, hRg, ⟨qT, hT⟩, ⟨qG, hG⟩, ho, hS, h0, h1, h2, h5, h6, hz⟩ := h
  refine ⟨hOT, hOG, hTG, hSI, hSN, hRg, ⟨qT, ?_⟩, ⟨qG, ?_⟩, ?_, fun i => ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp [Function.update_apply, Ne.symm hOT, hT]
  · simp [Function.update_apply, Ne.symm hOG, hG]
  · simp [ho]
  · simp [Function.update_apply, (hSN i).1, hS i]
  · simp [Function.update_apply, hRg 0, h0]
  · simp [Function.update_apply, hRg 1, h1]
  · simp [Function.update_apply, hRg 2, h2]
  · simp [Function.update_apply, hRg 5, h5]
  · simp [Function.update_apply, hRg 6, h6]
  · simp [Function.update_apply, hRg j, hz j hj]

theorem BlkIn.setv {O T GS : Fin (ns + 1)} {Sc : Fin 2 → Fin (ns + 1)} {Rg : Fin radBlkK ↪ Fin nr} {OP : Fin nr}
    {Dl : ListData} {gis : List ℕ} {G row : ℕ} {σ : WState ns nr} (h : BlkIn O T GS Sc Rg OP Dl gis G row σ)
    (r : Fin nr) (hr : ∀ j, Rg j = r → j = 3 ∨ j = 4) (x : ℕ) : BlkIn O T GS Sc Rg OP Dl gis G row (σ.setv r x) := by
  obtain ⟨hOT, hOG, hTG, hSI, hSN, hRg, hT, hG, ho, hS, h0, h1, h2, h5, h6, hz⟩ := h
  have hn : ∀ j : Fin radBlkK, j ≠ 3 → j ≠ 4 → Rg j ≠ r := fun j h3 h4 e => by
    rcases hr j e with e' | e'
    · exact h3 e'
    · exact h4 e'
  refine ⟨hOT, hOG, hTG, hSI, hSN, hRg, hT, hG, ho, hS, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_⟩
  · simp [Function.update_apply, hn 0 (by decide) (by decide), h0]
  · simp [Function.update_apply, hn 1 (by decide) (by decide), h1]
  · simp [Function.update_apply, hn 2 (by decide) (by decide), h2]
  · simp [Function.update_apply, hn 5 (by decide) (by decide), h5]
  · simp [Function.update_apply, hn 6 (by decide) (by decide), h6]
  · have h3 : j ≠ 3 := fun e => by subst e; exact absurd hj (by decide)
    have h4 : j ≠ 4 := fun e => by subst e; exact absurd hj (by decide)
    simp [Function.update_apply, hn j h3 h4, hz j hj]

theorem tLoop_spec (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr)
    (OP Mr N tmp : Fin nr) (hMN : Mr ≠ N) (hMt : Mr ≠ tmp) (hNt : N ≠ tmp) (hNOP : N ≠ OP)
    (hRN : ∀ j, Rg j ≠ N) (hRt : ∀ j, Rg j ≠ tmp) (hRM : ∀ j, Rg j ≠ Mr)
    (Dl : ListData) (gis : List ℕ) (G row : ℕ) (sgn : Bool) (σ : WState ns nr)
    (hin : BlkIn O T GS Sc Rg OP Dl gis G row σ) (hM : σ.val Mr = Dl.M) (hN0 : σ.val N = 0) (ht0 : σ.val tmp = 0)
    (h3 : σ.val (Rg 3) = 0) (h4 : σ.val (Rg 4) = (if sgn then 1 else 0))
    (hneed : ∀ t ≤ Dl.M, ∀ olen ≤ (σ.st O).length + (bws Dl gis G row sgn (Dl.M + 1)).length,
      Wb.need (blkSize Dl gis G row t sgn olen) ≤ cap)
    (hop : σ.val OP + (bws Dl gis G row sgn (Dl.M + 1)).length ≤ cap) (hcM : Dl.M + 1 ≤ cap) :
    WExec cap (tLoop Wb O T GS Sc Rg OP Mr N tmp) σ (appendO σ O OP (bws Dl gis G row sgn (Dl.M + 1)))
      (tCost Dl.M (Wb.bound cap)) := by
  have n3 : Rg 3 ≠ N := hRN 3
  have n3t : Rg 3 ≠ tmp := hRt 3
  have n3O : Rg 3 ≠ OP := hin.RgOP 3
  have n3M : Rg 3 ≠ Mr := hRM 3
  -- N := M + 1
  have s1 := wcopyR_spec cap Mr N tmp hMN hMt hNt σ hN0 ht0 (by omega)
  rw [hM] at s1
  have s2 := WExec.inc (cap := cap) N (σ.setv N Dl.M) (by simp; omega)
  rw [WState.setv_val, Function.update_self, wsetv_setv] at s2
  -- the loop
  let Sf : ℕ → WState ns nr := fun k =>
    ((appendO σ O OP (bws Dl gis G row sgn k)).setv (Rg 3) k).setv N (Dl.M + 1 - k)
  have hS0 : Sf 0 = σ.setv N (Dl.M + 1) := by
    simp only [Sf, bws, List.range_zero, List.flatMap_nil, appendO_nil, Nat.sub_zero]
    rw [← h3, wsetv_same]
  have hK : ∀ k ≤ Dl.M + 1, (Sf k).val N = Dl.M + 1 - k := fun k _ => by simp [Sf]
  have hbody : ∀ k < Dl.M + 1, WExec cap (.seq (Wb.prog O T GS Sc Rg OP) (.inc (Rg 3)))
      ((Sf k).setv N (Dl.M + 1 - k - 1)) (Sf (k + 1)) (Wb.bound cap + 1 + 3) := by
    intro k hk
    set τ := ((appendO σ O OP (bws Dl gis G row sgn k)).setv (Rg 3) k).setv N (Dl.M + 1 - k - 1) with hτ
    have e1 : (Sf k).setv N (Dl.M + 1 - k - 1) = τ := by simp only [Sf, hτ, wsetv_setv]
    rw [e1]
    have hinτ : BlkIn O T GS Sc Rg OP Dl gis G row τ := by
      refine ((hin.ao _).setv (Rg 3) (fun j e => Or.inl (Rg.injective e)) k).setv N
        (fun j e => absurd e (hRN j)) _
    have hlen : (bws Dl gis G row sgn (k + 1)).length ≤ (bws Dl gis G row sgn (Dl.M + 1)).length :=
      bws_len_le Dl gis G row sgn (by omega)
    rw [bws_succ, List.length_append] at hlen
    have hstO : τ.st O = σ.st O ++ bws Dl gis G row sgn k := by simp [τ]
    have hv3 : τ.val (Rg 3) = k := by simp [τ, Function.update_apply, n3]
    have hv4 : τ.val (Rg 4) = (if sgn then 1 else 0) := by
      have n4N : Rg 4 ≠ N := hRN 4
      have n43 : Rg 4 ≠ Rg 3 := Rg.injective.ne (by decide)
      simp [τ, Function.update_apply, n4N, n43, hin.RgOP 4, h4]
    have hvOP : τ.val OP = σ.val OP + (bws Dl gis G row sgn k).length := by
      simp [τ, Function.update_apply, Ne.symm hNOP, Ne.symm n3O]
    obtain ⟨qT, hT⟩ := hinτ.Td
    obtain ⟨qG, hG⟩ := hinτ.Gd
    have hcall := Wb.run O T GS Sc Rg OP hinτ.OT hinτ.OG hinτ.TG hinτ.ScI hinτ.ScN hinτ.RgOP Dl gis G row k sgn cap
      qT qG τ hT hG hinτ.ho hinτ.Sc0 hinτ.r0 hinτ.r1 hinτ.r2 hv3 hv4 hinτ.r5 hinτ.r6 hinτ.rz
      (hneed k (by omega) _ (by rw [hstO, List.length_append]; omega))
      (by rw [hvOP]; unfold bw at hlen; omega)
    have hinc := WExec.inc (cap := cap) (Rg 3) (appendO τ O OP (bw Dl gis G row sgn k))
      (by simp [Function.update_apply, n3O, hv3]; omega)
    refine WExec.cast cap (WExec.seq hcall hinc) ?_ le_rfl
    simp only [Sf, τ]
    rw [bws_succ]
    apply WState.eq
    · simp [Nat.add_assoc]
    · simp [List.append_assoc]
    · funext q
      by_cases hqN : q = N
      · subst hqN; simp [Function.update_apply, Ne.symm n3, hNOP]; omega
      · by_cases hq3 : q = Rg 3
        · subst hq3; simp [Function.update_apply, n3, n3O]
        · by_cases hqO : q = OP
          · subst hqO; simp [Function.update_apply, hqN, hq3, List.length_append]; omega
          · simp [Function.update_apply, hqN, hq3, hqO]
    · simp
  have s3 := UnionMachine.Round.wloop cap N (.seq (Wb.prog O T GS Sc Rg OP) (.inc (Rg 3))) (Wb.bound cap + 1 + 3)
    (Dl.M + 1) Sf hK hcM hbody
  rw [hS0] at s3
  have s4 := wclear_spec cap (Rg 3) (Dl.M + 1) (Sf (Dl.M + 1)) (by simp [Sf, Function.update_apply, n3])
    (by simp [Sf, Function.update_apply, n3]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · simp only [Sf, Nat.sub_self]
    apply WState.eq
    · simp
    · simp
    · funext q
      by_cases hq3 : q = Rg 3
      · subst hq3; simp [Function.update_apply, n3, n3O, h3]
      · by_cases hqN : q = N
        · subst hqN; simp [Function.update_apply, hq3, hNOP, hN0]
        · simp [Function.update_apply, hq3, hqN]
    · simp
  · unfold tCost; omega

/-- **Both signs**: `Rg 4 := 1`, the `+` blocks, `Rg 4 := 0`, the `−` blocks. -/
def sgnP (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr) (OP Mr N tmp : Fin nr) :
    WM ns nr :=
  .seq (.inc (Rg 4)) (.seq (tLoop Wb O T GS Sc Rg OP Mr N tmp) (.seq (.dec (Rg 4)) (tLoop Wb O T GS Sc Rg OP Mr N tmp)))

theorem sgnP_spec (O T GS : Fin (ns + 1)) (Sc : Fin 2 → Fin (ns + 1)) (Rg : Fin radBlkK ↪ Fin nr)
    (OP Mr N tmp : Fin nr) (hMN : Mr ≠ N) (hMt : Mr ≠ tmp) (hNt : N ≠ tmp) (hNOP : N ≠ OP) (hMOP : Mr ≠ OP)
    (htOP : tmp ≠ OP) (hRN : ∀ j, Rg j ≠ N) (hRt : ∀ j, Rg j ≠ tmp) (hRM : ∀ j, Rg j ≠ Mr)
    (Dl : ListData) (gis : List ℕ) (G row : ℕ) (σ : WState ns nr)
    (hin : BlkIn O T GS Sc Rg OP Dl gis G row σ) (hM : σ.val Mr = Dl.M) (hN0 : σ.val N = 0) (ht0 : σ.val tmp = 0)
    (h3 : σ.val (Rg 3) = 0) (h4 : σ.val (Rg 4) = 0)
    (hneed : ∀ t ≤ Dl.M, ∀ sgn : Bool, ∀ olen ≤ (σ.st O).length + (digBlocks Dl gis G row).length,
      Wb.need (blkSize Dl gis G row t sgn olen) ≤ cap)
    (hop : σ.val OP + (digBlocks Dl gis G row).length ≤ cap) (hcM : Dl.M + 1 ≤ cap) :
    WExec cap (sgnP Wb O T GS Sc Rg OP Mr N tmp) σ (appendO σ O OP (digBlocks Dl gis G row))
      (3 + 1 + (tCost Dl.M (Wb.bound cap) + 1 + (1 + 1 + tCost Dl.M (Wb.bound cap)))) := by
  have n4 : ∀ j, Rg j = Rg 4 → j = 3 ∨ j = 4 := fun j e => Or.inr (Rg.injective e)
  have n43 : Rg 4 ≠ Rg 3 := Rg.injective.ne (by decide)
  have n4O : Rg 4 ≠ OP := hin.RgOP 4
  have n3O : Rg 3 ≠ OP := hin.RgOP 3
  have hlen : (digBlocks Dl gis G row).length =
      (bws Dl gis G row true (Dl.M + 1)).length + (bws Dl gis G row false (Dl.M + 1)).length := by
    simp [digBlocks]
  have i1 := WExec.inc (cap := cap) (Rg 4) σ (by rw [h4]; omega)
  rw [h4, Nat.zero_add] at i1
  have t1 := tLoop_spec cap Wb O T GS Sc Rg OP Mr N tmp hMN hMt hNt hNOP hRN hRt hRM Dl gis G row true
    (σ.setv (Rg 4) 1) (hin.setv (Rg 4) n4 1) (by simp [Function.update_apply, Ne.symm (hRM 4), hM])
    (by simp [Function.update_apply, Ne.symm (hRN 4), hN0]) (by simp [Function.update_apply, Ne.symm (hRt 4), ht0])
    (by simp [Function.update_apply, Ne.symm n43, h3]) (by simp)
    (fun t ht olen hol => hneed t ht true olen (by simp at hol; rw [hlen]; omega))
    (by simp [Function.update_apply, Ne.symm n4O]; rw [hlen] at hop; omega) hcM
  have v4 : (appendO (σ.setv (Rg 4) 1) O OP (bws Dl gis G row true (Dl.M + 1))).val (Rg 4) = 1 := by
    simp [Function.update_apply, n4O]
  have d1 := WExec.dec (cap := cap) (Rg 4) (appendO (σ.setv (Rg 4) 1) O OP (bws Dl gis G row true (Dl.M + 1)))
    (by rw [v4]; omega)
  have e2 : (appendO (σ.setv (Rg 4) 1) O OP (bws Dl gis G row true (Dl.M + 1))).setv (Rg 4)
      ((appendO (σ.setv (Rg 4) 1) O OP (bws Dl gis G row true (Dl.M + 1))).val (Rg 4) - 1) =
      appendO σ O OP (bws Dl gis G row true (Dl.M + 1)) := by
    rw [v4, appendO_setv _ O OP (Rg 4) n4O, wsetv_setv]
    have hz : (appendO σ O OP (bws Dl gis G row true (Dl.M + 1))).val (Rg 4) = 0 := by
      simp [Function.update_apply, n4O, h4]
    calc (appendO σ O OP (bws Dl gis G row true (Dl.M + 1))).setv (Rg 4) (1 - 1)
        = (appendO σ O OP (bws Dl gis G row true (Dl.M + 1))).setv (Rg 4)
            ((appendO σ O OP (bws Dl gis G row true (Dl.M + 1))).val (Rg 4)) := by rw [hz]
      _ = _ := wsetv_same _ _
  rw [e2] at d1
  have hlen1 : ((appendO σ O OP (bws Dl gis G row true (Dl.M + 1))).st O).length =
      (σ.st O).length + (bws Dl gis G row true (Dl.M + 1)).length := by simp
  have t2 := tLoop_spec cap Wb O T GS Sc Rg OP Mr N tmp hMN hMt hNt hNOP hRN hRt hRM Dl gis G row false
    (appendO σ O OP (bws Dl gis G row true (Dl.M + 1))) (hin.ao _)
    (by simp [Function.update_apply, hMOP, hM]) (by simp [Function.update_apply, hNOP, hN0])
    (by simp [Function.update_apply, htOP, ht0]) (by simp [Function.update_apply, n3O, h3])
    (by simp [Function.update_apply, n4O, h4])
    (fun t ht olen hol => hneed t ht false olen (by rw [hlen1] at hol; rw [hlen]; omega))
    (by simp; rw [hlen] at hop; omega) hcM
  rw [appendO_append] at t2
  exact WExec.seq i1 (WExec.seq t1 (WExec.seq d1 t2))

end NearCubicWires.WireExponent3_5.UnionMachine.RadBlk
