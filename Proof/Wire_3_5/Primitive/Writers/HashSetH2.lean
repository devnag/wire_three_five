import Proof.Wire_3_5.Primitive.SeedFix.C4H2
import Proof.Wire_3_5.Primitive.Writers.HashSetH1

/-! # HASH setup (C), P3 part 2: the HASH setup's run to `HBank2` (**`setupH_run`**)

P3:3011-3016 (the HASH stage's setup before the loop), P3:2253-2290 (the Hb printer's static words), P3:2291-2296 (the
compiler request's `1^{Q'}`): at a THR call, from the stage's entry `stageIn XH w v` (the request `w = thrReq.word`, the
HASH tape `v`), the HASH setup `M0H` (the THR setup chain, two front copies, the data-stage rerun, the HASH cell,
the kept words writer and `1^{Q'}` copy) leaves `HBank2` at the call's words: the SymBank part (`hash_setup_run`), the 94 kept words `hb0 (hbX (hashDataOf …) (capsOf (fr 1)) 0 0)` framed on `oK + j` (T-b fed by the
HASH cell's `kwIns`), `1^{Q'}` on `oQ` (T-c from `gW 34`), the bank blank from `hOff` up. The three stage contracts
(`DataRerun`, `KwDock`, `QCopy`, PrimTC4KWT, with this dock) are hypotheses.

* `stageIn_val`, `hashTape_htWord` (the HASH tape is the kept words writer's input `htWord Fs`), `hLxH`,
  `kInH_inj`, `kInH_lt`, `extC_cases`, `extC_none`; **`setupH_run`**.

Paper quantity of the main type: `HBank2` at the call: the HASH stage's setup exit bank (the Hb printer's static
words `KW`, the compiler request's fixed fields and `1^{Q'}`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

theorem stageIn_val (x : ℕ) (w v : List Bool) (i : Fin (3 + x)) :
    PrimT.SeedFixTypes.stageIn x w v i = if i.val = 0 then frame w else if i.val = 1 then v else [] := by
  unfold PrimT.SeedFixTypes.stageIn
  refine Fin.addCases (fun j => ?_) (fun k => ?_) i
  · rw [Fin.addCases_left]
    fin_cases j <;> simp
  · rw [Fin.addCases_right]
    have h0 : (Fin.natAdd 3 k : Fin (3 + x)).val ≠ 0 := by simp
    have h1 : (Fin.natAdd 3 k : Fin (3 + x)).val ≠ 1 := by simp; omega
    rw [if_neg h0, if_neg h1]

section Tape
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
  (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The HASH tape is the kept words writer's input `htWord Fs`** (every HASH row is a FILTER row with the single
term `1·filtPolyC …`). -/
theorem hashTape_htWord : WriterIface.hashTape alg I hs Cs carriers =
    PrimT.HbM.htWord (PrimT.C4H.hashFsOf alg I hs Cs carriers) := by
  unfold WriterIface.hashTape PrimT.HbM.htWord
  refine congrArg SeedFix.blockWord ?_
  unfold WriterIface.hashExprs PrimT.C4H.hashFsOf
  rw [List.map_map, List.map_map]
  refine List.map_congr_left (fun r hr => ?_)
  unfold Batch.hashBatch at hr
  obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
  simp only [Function.comp, Records.hashRow, WriterIface.refOf, PrimT.C4H.rowPoly, ListMachine.Row.filtRefC]

end Tape

section Lay
variable (L : Lay) {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ} {capT : ℕ → ℕ}
  (S4 : ThrData.ThrDataStage4 alg Dexp capT) (T : PrimThrW.PortsE.TopFrontPort3 alg)
  (N : PrimThrW.Nums4.NumsPort4 alg Dexp) (Wk : PrimT.C4KW.KWW) (fT : ℕ)

theorem hLxH : L.N ≤ 3 + XH L S4 T N Wk fT := le_trans (LN_le L S4) (hxX L S4 T N Wk fT)

theorem kS_ge : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 10 → 138 ≤ (kS i).val := by decide

theorem kS_inj : ∀ i j : Fin 12, i.val ≠ 0 → i.val ≠ 10 → j.val ≠ 0 → j.val ≠ 10 → (kS i).val = (kS j).val → i = j := by
  decide

theorem gW3_ge : 9925 ≤ (L.gW 3).val := by simp only [Lay.gW]; omega

theorem kInH_val (i : Fin 12) : (kInH L S4 T N Wk fT i).val =
    if i.val = 0 then 1 else if i.val = 10 then (L.gW 3).val else oC L S4 + (kS i).val + 1 := by
  unfold kInH
  split_ifs <;> rfl

theorem kInH_inj : Function.Injective (kInH L S4 T N Wk fT) := by
  intro a b h
  have e := congrArg Fin.val h
  have hW3 := (L.gW 3).isLt
  have hLN := LN_le L S4
  have g3 := gW3_ge L
  have hbase : (L.gW 3).val < oC L S4 := by simp only [oC, oD, oF2, oF1]; omega
  have key : ∀ i : Fin 12, (i.val = 0 ∧ (kInH L S4 T N Wk fT i).val = 1) ∨
      (i.val = 10 ∧ (kInH L S4 T N Wk fT i).val = (L.gW 3).val) ∨
      (i.val ≠ 0 ∧ i.val ≠ 10 ∧ (kInH L S4 T N Wk fT i).val = oC L S4 + (kS i).val + 1) := by
    intro i
    rw [kInH_val]
    by_cases h0 : i.val = 0
    · exact Or.inl ⟨h0, by rw [if_pos h0]⟩
    · by_cases h10 : i.val = 10
      · exact Or.inr (Or.inl ⟨h10, by rw [if_neg h0, if_pos h10]⟩)
      · exact Or.inr (Or.inr ⟨h0, h10, by rw [if_neg h0, if_neg h10]⟩)
  rcases key a with ⟨a0, ea⟩ | ⟨a10, ea⟩ | ⟨a0, a10, ea⟩ <;>
    rcases key b with ⟨b0, eb⟩ | ⟨b10, eb⟩ | ⟨b0, b10, eb⟩ <;> rw [ea, eb] at e
  · exact Fin.ext (by omega)
  · omega
  · omega
  · omega
  · exact Fin.ext (by omega)
  · omega
  · omega
  · omega
  · exact kS_inj a b a0 a10 b0 b10 (by omega)

theorem kInH_lt (i : Fin 12) : (kInH L S4 T N Wk fT i).val < oK L S4 T N := by
  have hW3 := (L.gW 3).isLt
  have hLN := LN_le L S4
  have hk := (kS i).isLt
  have hB : BX (cX T N) = LNS (cX T N) + 2 + LNR + 2 := rfl
  unfold LNS at hB
  rw [kInH_val]
  split_ifs <;> simp only [oK, oC, oD, oF2, oF1] <;> omega

theorem extC_cases (j : Fin (BX (cX T N) + 1)) (g : Fin (3 + XH L S4 T N Wk fT))
    (h : extC L S4 T N Wk fT j = some g) :
    (j = Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) 0))) ∧ g = g0 L S4 T N Wk fT) ∨
    (j = Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) 113))) ∧ g = uT L S4 T N Wk fT) ∨
    (j = Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) 2))) ∧ g = vT L S4 T N Wk fT) ∨
    (j = Fin.castAdd 1 (bCnt (cX T N)) ∧ g = wT L S4 T N Wk fT) := by
  unfold extC at h
  split_ifs at h with h1 h2 h3 h4
  · exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
  · exact Or.inr (Or.inl ⟨h2, (Option.some.inj h).symm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h3, (Option.some.inj h).symm⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h4, (Option.some.inj h).symm⟩))

theorem val_g0 : (g0 L S4 T N Wk fT).val = 0 := rfl
theorem val_uT : (uT L S4 T N Wk fT).val = oD L S4 + PrimT.C4KW.drTU S4 := rfl
theorem val_vT : (vT L S4 T N Wk fT).val = oF2 L S4 + (18 + L.U + (UnaryCalc.outputTape L.D).val) := rfl
theorem val_wT : (wT L S4 T N Wk fT).val = oF2 L S4 + (18 + 2 * L.U + (UnaryCalc.outputTape L.D).val) := rfl
theorem val_tN : (tNt L S4 T N Wk fT).val = oF1 L S4 + 14 := rfl
theorem val_tL : (tLt L S4 T N Wk fT).val = oF1 L S4 + (18 + (UnaryCalc.outputTape L.D).val) := rfl
theorem val_tD : (tDt L S4 T N Wk fT).val = oF1 L S4 + (18 + L.U + (UnaryCalc.outputTape L.D).val) := rfl

theorem c_ne (a b : Fin 161) (h : a.val ≠ b.val) :
    (Fin.castAdd 1 (bIn (cX T N) (sTape (nr := LNR) (sk (cX T N) a))) : Fin (BX (cX T N) + 1)) ≠
      Fin.castAdd 1 (bIn (cX T N) (sTape (sk (cX T N) b))) := fun e => by
  have := congrArg Fin.val e
  simp only [Fin.val_castAdd, HashCell.bIn_val, DockW.sTape_val, sk_val] at this
  split_ifs at this <;> omega

theorem c_ne_cnt (a : Fin 161) :
    (Fin.castAdd 1 (bIn (cX T N) (sTape (nr := LNR) (sk (cX T N) a))) : Fin (BX (cX T N) + 1)) ≠
      Fin.castAdd 1 (bCnt (cX T N)) := fun e => by
  have := congrArg Fin.val e
  have hs := sTsk_le (cX T N) a
  simp only [Fin.val_castAdd, HashCell.bIn_val, HashCell.bCnt_val] at this
  unfold HashCell.BT at this
  omega

theorem lay_facts : L.N ≤ 3 + ThrSet.thrXb L S4.x3 ∧ 0 < L.U ∧ (UnaryCalc.outputTape L.D).val < L.U ∧
    18 + 3 * L.U ≤ L.N := by
  refine ⟨LN_le L S4, L.U_pos, L.out_lt, ?_⟩
  rw [L.N_eq]; omega

theorem extC_inj : ∀ i j g, extC L S4 T N Wk fT i = some g → extC L S4 T N Wk fT j = some g → i = j := by
  obtain ⟨h1, h2, h3, h4⟩ := lay_facts L S4
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  have vg0 := val_g0 L S4 T N Wk fT
  have vuT := val_uT L S4 T N Wk fT
  have vvT := val_vT L S4 T N Wk fT
  have vwT := val_wT L S4 T N Wk fT
  intro i j g hi hj
  rcases extC_cases L S4 T N Wk fT i g hi with ⟨ei, eg⟩ | ⟨ei, eg⟩ | ⟨ei, eg⟩ | ⟨ei, eg⟩ <;>
    rcases extC_cases L S4 T N Wk fT j g hj with ⟨ej, eg'⟩ | ⟨ej, eg'⟩ | ⟨ej, eg'⟩ | ⟨ej, eg'⟩ <;>
    first
    | (exfalso; have := congrArg Fin.val (eg.symm.trans eg'); simp only [vg0, vuT, vvT, vwT] at this; omega)
    | (rw [ei, ej])

theorem extC_lt : ∀ i g, extC L S4 T N Wk fT i = some g → g.val < oC L S4 := by
  obtain ⟨h1, h2, h3, h4⟩ := lay_facts L S4
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  have hoC : oC L S4 = oD L S4 + PrimT.C4KW.drN S4 := rfl
  have hdN : PrimT.C4KW.drN S4 = PrimT.C4KW.drM3 S4 + 3 := rfl
  have hdU : PrimT.C4KW.drTU S4 = PrimT.C4KW.drM3 S4 + 1 := rfl
  intro i g hi
  rcases extC_cases L S4 T N Wk fT i g hi with ⟨-, eg⟩ | ⟨-, eg⟩ | ⟨-, eg⟩ | ⟨-, eg⟩ <;> rw [eg] <;>
    simp only [val_g0, val_uT, val_vT, val_wT] <;> omega

theorem extC_low (i : Fin (3 + XH L S4 T N Wk fT)) (hi : i.val < oF1 L S4) (hig : i ≠ g0 L S4 T N Wk fT) :
    ∀ j, extC L S4 T N Wk fT j ≠ some i := by
  obtain ⟨h1, h2, h3, h4⟩ := lay_facts L S4
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  intro j e
  rcases extC_cases L S4 T N Wk fT j i e with ⟨-, eg⟩ | ⟨-, eg⟩ | ⟨-, eg⟩ | ⟨-, eg⟩
  · exact hig eg
  · have := congrArg Fin.val eg; rw [val_uT] at this; omega
  · have := congrArg Fin.val eg; rw [val_vT] at this; omega
  · have := congrArg Fin.val eg; rw [val_wT] at this; omega

theorem t_facts : (tNt L S4 T N Wk fT) ≠ g0 L S4 T N Wk fT ∧ (tLt L S4 T N Wk fT) ≠ g0 L S4 T N Wk fT ∧
    (tDt L S4 T N Wk fT) ≠ g0 L S4 T N Wk fT ∧ (tNt L S4 T N Wk fT) ≠ tLt L S4 T N Wk fT ∧
    (tNt L S4 T N Wk fT) ≠ tDt L S4 T N Wk fT ∧ (tLt L S4 T N Wk fT) ≠ tDt L S4 T N Wk fT ∧
    oF1 L S4 ≤ (tNt L S4 T N Wk fT).val ∧ oF1 L S4 ≤ (tLt L S4 T N Wk fT).val ∧ oF1 L S4 ≤ (tDt L S4 T N Wk fT).val ∧
    (tNt L S4 T N Wk fT).val < oF2 L S4 ∧ (tLt L S4 T N Wk fT).val < oF2 L S4 ∧ (tDt L S4 T N Wk fT).val < oF2 L S4 ∧
    (g0 L S4 T N Wk fT).val < oF1 L S4 ∧ oF2 L S4 ≤ (vT L S4 T N Wk fT).val ∧ (vT L S4 T N Wk fT).val < oD L S4 ∧
    oF2 L S4 ≤ (wT L S4 T N Wk fT).val ∧ (wT L S4 T N Wk fT).val < oD L S4 ∧ oD L S4 ≤ oC L S4 := by
  obtain ⟨h1, h2, h3, h4⟩ := lay_facts L S4
  have hoF1 : oF1 L S4 = 3 + ThrSet.thrXb L S4.x3 := rfl
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  have hoC : oC L S4 = oD L S4 + PrimT.C4KW.drN S4 := rfl
  have vg0 := val_g0 L S4 T N Wk fT
  have vtN := val_tN L S4 T N Wk fT
  have vtL := val_tL L S4 T N Wk fT
  have vtD := val_tD L S4 T N Wk fT
  have vvT := val_vT L S4 T N Wk fT
  have vwT := val_wT L S4 T N Wk fT
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩ <;> (try have := congrArg Fin.val e) <;> omega

section Chain
variable (B1 B2 B3 B4 B5 B6 B7 : Fin (3 + XH L S4 T N Wk fT) → List Bool)

/-- Above T-a's region the bank is blank after T-a. -/
theorem up_blank
    (e4u : ∀ i : Fin (3 + XH L S4 T N Wk fT), i ≠ g0 L S4 T N Wk fT → i ≠ tNt L S4 T N Wk fT → i ≠ tLt L S4 T N Wk fT →
      i ≠ tDt L S4 T N Wk fT → (i.val < oD L S4 ∨ oD L S4 + PrimT.C4KW.drN S4 ≤ i.val) → B4 i = B3 i)
    (e3bl : ∀ i : Fin (3 + XH L S4 T N Wk fT), oF2 L S4 + L.N ≤ i.val → B3 i = []) :
    ∀ i : Fin (3 + XH L S4 T N Wk fT), oC L S4 ≤ i.val → B4 i = [] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, a1, a2, a3, a4, -, -, -, -, a5⟩ := t_facts L S4 T N Wk fT
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  have hoC : oC L S4 = oD L S4 + PrimT.C4KW.drN S4 := rfl
  intro i hi
  rw [e4u i (fun e => by rw [e] at hi; omega) (fun e => by rw [e] at hi; omega) (fun e => by rw [e] at hi; omega)
    (fun e => by rw [e] at hi; omega) (Or.inr (by omega))]
  exact e3bl i (by omega)

/-- T-a keeps the second copy's `1^V` and `1^W`. -/
theorem keep_vw
    (e4u : ∀ i : Fin (3 + XH L S4 T N Wk fT), i ≠ g0 L S4 T N Wk fT → i ≠ tNt L S4 T N Wk fT → i ≠ tLt L S4 T N Wk fT →
      i ≠ tDt L S4 T N Wk fT → (i.val < oD L S4 ∨ oD L S4 + PrimT.C4KW.drN S4 ≤ i.val) → B4 i = B3 i) :
    B4 (vT L S4 T N Wk fT) = B3 (vT L S4 T N Wk fT) ∧ B4 (wT L S4 T N Wk fT) = B3 (wT L S4 T N Wk fT) := by
  obtain ⟨-, -, -, -, -, -, b1, b2, b3, a1, a2, a3, a4, c1, c2, c3, c4, -⟩ := t_facts L S4 T N Wk fT
  refine ⟨e4u _ ?_ ?_ ?_ ?_ (Or.inl c2), e4u _ ?_ ?_ ?_ ?_ (Or.inl c4)⟩ <;> intro e <;>
    have := congrArg Fin.val e <;> omega

/-- Below the first copy, the bank after the cell is the setup's. -/
theorem low_chain (e2u : ∀ i : Fin (3 + XH L S4 T N Wk fT), i.val < oF1 L S4 → i ≠ g0 L S4 T N Wk fT → B2 i = B1 i)
    (e3u : ∀ i : Fin (3 + XH L S4 T N Wk fT), i.val < oF2 L S4 → i ≠ g0 L S4 T N Wk fT → B3 i = B2 i)
    (e4u : ∀ i : Fin (3 + XH L S4 T N Wk fT), i ≠ g0 L S4 T N Wk fT → i ≠ tNt L S4 T N Wk fT → i ≠ tLt L S4 T N Wk fT →
      i ≠ tDt L S4 T N Wk fT → (i.val < oD L S4 ∨ oD L S4 + PrimT.C4KW.drN S4 ≤ i.val) → B4 i = B3 i)
    (un5 : ∀ i : Fin (3 + XH L S4 T N Wk fT), i.val < oC L S4 → (∀ j, extC L S4 T N Wk fT j ≠ some i) → B5 i = B4 i)
    (hg : B5 (g0 L S4 T N Wk fT) = B1 (g0 L S4 T N Wk fT)) :
    ∀ i : Fin (3 + XH L S4 T N Wk fT), i.val < oF1 L S4 → B5 i = B1 i := by
  obtain ⟨-, -, -, -, -, -, b1, b2, b3, a1, a2, a3, a4, c1, c2, c3, c4, c5⟩ := t_facts L S4 T N Wk fT
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  intro i hi
  by_cases hig : i = g0 L S4 T N Wk fT
  · rw [hig]; exact hg
  · rw [un5 i (by omega) (extC_low L S4 T N Wk fT i hi hig)]
    rw [e4u i hig (fun e => by rw [e] at hi; omega) (fun e => by rw [e] at hi; omega) (fun e => by rw [e] at hi; omega)
      (Or.inl (by omega))]
    rw [e3u i (by omega) hig, e2u i hi hig]

/-- After T-b and T-c: the low part and the kept words kept, the bank blank from `hOff` up. -/
theorem tail_chain
    (e6u : ∀ i : Fin (3 + XH L S4 T N Wk fT), (i.val < oK L S4 T N ∨ oK L S4 T N + 94 + Wk.x ≤ i.val) → B6 i = B5 i)
    (e7u : ∀ i : Fin (3 + XH L S4 T N Wk fT), (i.val < oQ L S4 T N Wk ∨ oQ L S4 T N Wk + 3 ≤ i.val) → B7 i = B6 i)
    (bl5 : ∀ i : Fin (3 + XH L S4 T N Wk fT), oC L S4 + (BX (cX T N) + 1) ≤ i.val → B5 i = []) :
    (∀ i : Fin (3 + XH L S4 T N Wk fT), i.val < oC L S4 → B7 i = B5 i) ∧
    (∀ i : Fin (3 + XH L S4 T N Wk fT), hOff L S4 T N Wk ≤ i.val → B7 i = []) ∧
    (∀ j : Fin 94, B7 (hkTH L S4 T N Wk fT j) = B6 (hkTH L S4 T N Wk fT j)) ∧
    (∀ i : Fin (3 + XH L S4 T N Wk fT), oK L S4 T N ≤ i.val → i.val < oK L S4 T N + 94 + Wk.x → B5 i = []) ∧
    (∀ i : Fin (3 + XH L S4 T N Wk fT), oQ L S4 T N Wk ≤ i.val → i.val < oQ L S4 T N Wk + 3 → B6 i = []) := by
  have hoK : oK L S4 T N = oC L S4 + (BX (cX T N) + 1) := rfl
  have hoQ : oQ L S4 T N Wk = oK L S4 T N + 94 + Wk.x := rfl
  have hOf : hOff L S4 T N Wk = oQ L S4 T N Wk + 3 := rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun j => ?_, fun i h1 h2 => bl5 i (by omega), fun i h1 h2 => ?_⟩
  · rw [e7u i (Or.inl (by omega)), e6u i (Or.inl (by omega))]
  · rw [e7u i (Or.inr (by omega)), e6u i (Or.inr (by omega))]
    exact bl5 i (by omega)
  · have hj := j.isLt
    exact e7u _ (Or.inl (by show oK L S4 T N + j.val < _; omega))
  · rw [e6u i (Or.inr (by omega))]
    exact bl5 i (by omega)

end Chain

/-- The kept words' and `1^{Q'}`'s tapes: distinct, above `L.N`, below `hOff`. -/
theorem bank_arith : (∀ j, L.N ≤ (hkTH L S4 T N Wk fT j).val ∧ (hkTH L S4 T N Wk fT j).val < hOff L S4 T N Wk) ∧
    (L.N ≤ (hqTH L S4 T N Wk fT).val ∧ (hqTH L S4 T N Wk fT).val < hOff L S4 T N Wk ∧
      ∀ j, hkTH L S4 T N Wk fT j ≠ hqTH L S4 T N Wk fT) ∧ Function.Injective (hkTH L S4 T N Wk fT) := by
  obtain ⟨h1, -, -, -⟩ := lay_facts L S4
  have hoF1 : oF1 L S4 = 3 + ThrSet.thrXb L S4.x3 := rfl
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  have hoC : oC L S4 = oD L S4 + PrimT.C4KW.drN S4 := rfl
  have hoK : oK L S4 T N = oC L S4 + (BX (cX T N) + 1) := rfl
  have hoQ : oQ L S4 T N Wk = oK L S4 T N + 94 + Wk.x := rfl
  have hOf : hOff L S4 T N Wk = oQ L S4 T N Wk + 3 := rfl
  refine ⟨fun j => ?_, ⟨?_, ?_, fun j e => ?_⟩, fun a b h => ?_⟩
  · have hj := j.isLt
    exact ⟨by show L.N ≤ oK L S4 T N + j.val; omega, by show oK L S4 T N + j.val < hOff L S4 T N Wk; omega⟩
  · show L.N ≤ oQ L S4 T N Wk; omega
  · show oQ L S4 T N Wk < hOff L S4 T N Wk; omega
  · have := congrArg Fin.val e
    have hj := j.isLt
    simp only [hkTH, hqTH] at this
    omega
  · exact Fin.ext (by have := congrArg Fin.val h; simp only [hkTH] at this; omega)

theorem small_lt : 1 < oF1 L S4 ∧ (∀ j, (L.gW j).val < oF1 L S4) ∧ (srcQ L S4 T N Wk fT).val < oF1 L S4 ∧
    oF1 L S4 ≤ oK L S4 T N ∧ oF1 L S4 ≤ oQ L S4 T N Wk ∧ oF1 L S4 ≤ oC L S4 := by
  obtain ⟨h1, -, -, -⟩ := lay_facts L S4
  have hoF1 : oF1 L S4 = 3 + ThrSet.thrXb L S4.x3 := rfl
  have hoF2 : oF2 L S4 = oF1 L S4 + L.N := rfl
  have hoD : oD L S4 = oF2 L S4 + L.N := rfl
  have hoC : oC L S4 = oD L S4 + PrimT.C4KW.drN S4 := rfl
  have hoK : oK L S4 T N = oC L S4 + (BX (cX T N) + 1) := rfl
  have hoQ : oQ L S4 T N Wk = oK L S4 T N + 94 + Wk.x := rfl
  have hs : (srcQ L S4 T N Wk fT).val = (L.gW 34).val := rfl
  have h34 := (L.gW 34).isLt
  refine ⟨by omega, fun j => by have := (L.gW j).isLt; omega, by omega, by omega, by omega, by omega⟩

/-- `setupT3Cost` is monotone in the numbers machine's steps. -/
theorem cost_mono (w : List Bool) (n CL Cd Cc n3 W ch : ℕ) (u : List Bool) (c c' ell d2 ρ B3 : ℕ) (h : c ≤ c') :
    ThrSet.setupT3Cost L w n CL Cd Cc n3 W ch u c ell d2 ρ B3 ≤ ThrSet.setupT3Cost L w n CL Cd Cc n3 W ch u c' ell d2 ρ B3 := by
  unfold ThrSet.setupT3Cost ThrSet.cbCost C4Set.bigCost
  omega

end Lay

section Run

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
