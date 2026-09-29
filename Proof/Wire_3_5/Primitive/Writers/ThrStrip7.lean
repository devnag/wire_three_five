import Proof.Wire_3_5.Primitive.SeedFix.C4SL
import Proof.Wire_3_5.Primitive.Writers.C3WDock
import Proof.Wire_3_5.Primitive.Writers.ThrStrip6

/-! # c4 THR block, the THR compiler writer's run: **`thrC3_run`**

From the writer `C`'s run on `frame req.word` (`C3Run C.M B … req.word …`, what `C3ReqAt3.thr_run` gives) and the
strip's run at capacity `2·pr + 2` on the THR input `w = req.word ++ hbF`, the wrapper `thrC3 C` runs on `frame w`
with the same outputs `frame PRE`, `frame POST`, within `thrB`.

Paper quantity of the main type: the THR call's compiler request fields from the THR input word. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimT.C3ReqIface (C3Stage C3Run c3In c3Out)

variable (C : C3Stage)

/-- The wrapper's budget. -/
def thrB (B cs pr wl h Q m : ℕ) : ℕ := (bigCost pr cs + 1 + B) + 1 + (2 * wl + 1) + h + Q + m + pr

theorem castAdd_val (x : Fin C.t) : (Fin.castAdd (BX + 1) x : Fin (C.t + (BX + 1))).val = x.val := rfl

theorem c3In_cast (w : List Bool) (h Q m pr : ℕ) (X : Fin C.t) :
    c3In (Fin.castAdd (BX + 1) C.inS) (Fin.castAdd (BX + 1) C.hS) (Fin.castAdd (BX + 1) C.qS)
      (Fin.castAdd (BX + 1) C.mS) (Fin.castAdd (BX + 1) C.pS) w h Q m pr (Fin.castAdd (BX + 1) X) =
    c3In C.inS C.hS C.qS C.mS C.pS w h Q m pr X := by
  unfold c3In
  simp only [(Fin.castAdd_injective C.t (BX + 1)).eq_iff]

theorem c3In_high (w : List Bool) (h Q m pr : ℕ) (i : Fin (C.t + (BX + 1))) (hi : C.t ≤ i.val) :
    c3In (Fin.castAdd (BX + 1) C.inS) (Fin.castAdd (BX + 1) C.hS) (Fin.castAdd (BX + 1) C.qS)
      (Fin.castAdd (BX + 1) C.mS) (Fin.castAdd (BX + 1) C.pS) w h Q m pr i = [] := by
  have ne : ∀ x : Fin C.t, i ≠ Fin.castAdd (BX + 1) x := fun x e => by
    have := congrArg Fin.val e; rw [castAdd_val] at this; have := x.isLt; omega
  unfold c3In
  simp [ne]

theorem c3In_word (w w' : List Bool) (h Q m pr : ℕ) (X : Fin C.t) (hX : X ≠ C.inS) :
    c3In C.inS C.hS C.qS C.mS C.pS w h Q m pr X = c3In C.inS C.hS C.qS C.mS C.pS w' h Q m pr X := by
  unfold c3In; simp [hX]

theorem c3Sl_ne_in (j : Fin C.t) : c3Sl C j ≠ Fin.castAdd (BX + 1) C.inS := by
  unfold c3Sl
  split_ifs with h
  · intro e; have := congrArg Fin.val e; simp [yT] at this; have := C.inS.isLt; omega
  · intro e; exact h (Fin.castAdd_injective _ _ e)

theorem c3Sl_cast (j : Fin C.t) (hj : j ≠ C.inS) : c3Sl C j = Fin.castAdd (BX + 1) j := by
  unfold c3Sl; rw [if_neg hj]

/-- **The THR compiler writer's run** on the THR input. -/
theorem thrC3_run (w pfx : List Bool) (h Q m pr B cs : ℕ) (pre post : List Bool)
    (hC : C3Run C.M B C.inS C.hS C.qS C.mS C.pS C.preS C.postS pfx h Q m pr pre post)
    (τ : WState (LNS 0) LNR) (c : ℕ) (hx : WExec (2 * pr + 2) stripW (CellLoopD.blankCellD 0 w [] 0 []) τ c)
    (hc : c ≤ cs) (hY : τ.st sY = frame pfx) (h0 : τ.st (sk 0 0) = frame w) :
    C3Run (thrC3 C).M (thrB B cs pr w.length h Q m) (thrC3 C).inS (thrC3 C).hS (thrC3 C).qS (thrC3 C).mS
      (thrC3 C).pS (thrC3 C).preS (thrC3 C).postS w h Q m pr pre post := by
  have eBX : BX = 676 := rfl
  have eBT : BT = 674 := rfl
  have nd := C.distinct
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨niH, niQ, niM, niP, niPre, niPost⟩, ⟨nhQ, nhM, nhP, nhPre, nhPost⟩, ⟨nqM, nqP, nqPre, nqPost⟩,
    ⟨nmP, nmPre, nmPost⟩, ⟨npPre, npPost⟩, nPP⟩ := nd
  -- 1: the strip
  obtain ⟨m8, h8⟩ := big_step stripW w [] pr τ c hx
  set In' := c3In (Fin.castAdd (BX + 1) C.inS) (Fin.castAdd (BX + 1) C.hS) (Fin.castAdd (BX + 1) C.qS)
      (Fin.castAdd (BX + 1) C.mS) (Fin.castAdd (BX + 1) C.pS) w h Q m pr with hIn'
  have nIP : (Fin.castAdd (BX + 1) C.inS : Fin (C.t + (BX + 1))) ≠ Fin.castAdd (BX + 1) C.pS :=
    fun e => niP (Fin.castAdd_injective _ _ e)
  obtain ⟨st1, bl1, un1, pv1, ex1⟩ := stageP h8 C.t (hoffS C) (stripExt C)
    (fun i j g hi hj => by
      unfold stripExt at hi hj
      split_ifs at hi hj with a0 a1 b0 b1 <;> simp only [Option.some.injEq] at hi hj <;> subst_vars <;>
        first
        | exact Fin.ext (by omega)
        | exact absurd hj nIP
        | exact absurd hj (Ne.symm nIP))
    (fun i g hi => by
      unfold stripExt at hi
      split_ifs at hi <;> simp only [Option.some.injEq] at hi <;> subst hi <;> first | exact C.inS.isLt | exact C.pS.isLt)
    In'
    (fun j g hj => by
      unfold stripExt at hj
      split_ifs at hj with a0 a1 <;> simp only [Option.some.injEq] at hj <;> subst hj <;>
        rw [ac_lt _ _ j (by omega)]
      · rw [hIn', c3In_cast]; unfold c3In; simp [rawB, Fin.ext_iff, C4Set.vb0, a0]
      · rw [hIn', c3In_cast]; unfold c3In
        simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, C4Set.vcnt, a1, Ne.symm niP, Ne.symm nhP, Ne.symm nqP,
          Ne.symm nmP])
    (fun i hi => c3In_high C w h Q m pr i hi)
    (fun j hj => by
      unfold stripExt at hj
      split_ifs at hj with a0 a1
      by_cases hlt : j.val < BX
      · rw [ac_lt _ _ j hlt]
        simp [rawB, Fin.ext_iff, C4Set.vb0, C4Set.vb113, C4Set.vcnt, a0, a1]
      · rw [ac_ge _ _ j (by omega)])
  set A1 := install (slx C.t (hoffS C) (stripExt C)) In'
    (Fin.addCases (Fin.addCases (wenc (2 * pr + 2) τ).A (xB pr)) (fun _ : Fin 1 => List.replicate m8 false)) with hA1
  have A1y : A1 (yT C) = frame pfx := by
    have hx123 : stripExt C ⟨123, by omega⟩ = none := by unfold stripExt; simp
    rw [pv1 ⟨123, by omega⟩ _ hx123 (by simp [yT]), ac_lt _ _ _ (by norm_num), ac_lt _ _ _ (by norm_num)]
    have e : (⟨123, by omega⟩ : Fin BT) = sTape (nr := LNR) sY := rfl
    rw [e, wenc_A_s, hY]
  have A1in : A1 (Fin.castAdd (BX + 1) C.inS) = frame w := by
    have e0 : stripExt C ⟨0, by omega⟩ = some (Fin.castAdd (BX + 1) C.inS) := by unfold stripExt; simp
    rw [ex1 _ _ e0, ac_lt _ _ _ (by norm_num), ac_lt _ _ _ (by norm_num)]
    have e : (⟨0, by omega⟩ : Fin BT) = sTape (nr := LNR) (sk 0 0) := rfl
    rw [e, wenc_A_s, h0]
  have A1p : A1 (Fin.castAdd (BX + 1) C.pS) = List.replicate pr true := by
    have e1 : stripExt C ⟨674, by omega⟩ = some (Fin.castAdd (BX + 1) C.pS) := by unfold stripExt; simp
    rw [ex1 _ _ e1, ac_lt _ _ _ (by norm_num), ac_ge _ _ _ (by norm_num)]
    rfl
  have A1o : ∀ X : Fin C.t, X ≠ C.inS → X ≠ C.pS → A1 (Fin.castAdd (BX + 1) X) = In' (Fin.castAdd (BX + 1) X) := by
    intro X h1 h2
    apply un1 _ (by rw [castAdd_val]; exact X.isLt)
    intro j e
    unfold stripExt at e
    split_ifs at e <;> simp only [Option.some.injEq] at e
    · exact h1 (Fin.castAdd_injective _ _ e).symm
    · exact h2 (Fin.castAdd_injective _ _ e).symm
  -- 2: the writer on the stripped request
  obtain ⟨J, hJ, hr⟩ := hC
  have sC := C3Dock.readyStep hr
  have d2 := GeoFront.dockZ sC (c3Sl C) (c3Sl_inj C) (fun _ => 0) A1 (fun _ => rfl)
    (fun j => by
      by_cases hj : j = C.inS
      · subst hj; rw [show c3Sl C C.inS = yT C by unfold c3Sl; simp, A1y]; unfold c3In; simp
      · rw [c3Sl_cast C j hj]
        by_cases hp : j = C.pS
        · subst hp; rw [A1p]; unfold c3In; simp [Ne.symm niP, Ne.symm nhP, Ne.symm nqP, Ne.symm nmP]
        · rw [A1o j hj hp, hIn', c3In_cast, c3In_word C w pfx h Q m pr j hj])
  set A2 := install (c3Sl C) A1 (c3Out C.inS C.hS C.qS C.mS C.pS C.preS C.postS pfx h Q m pr pre post J) with hA2
  have st := st1.seq d2
  -- 3: the exit bank
  have out : c3Out (Fin.castAdd (BX + 1) C.inS) (Fin.castAdd (BX + 1) C.hS) (Fin.castAdd (BX + 1) C.qS)
      (Fin.castAdd (BX + 1) C.mS) (Fin.castAdd (BX + 1) C.pS) (Fin.castAdd (BX + 1) C.preS)
      (Fin.castAdd (BX + 1) C.postS) w h Q m pr pre post A2 = A2 := by
    funext i
    unfold c3Out
    by_cases e1 : i = Fin.castAdd (BX + 1) C.preS
    · subst e1; rw [if_pos rfl, hA2, ← c3Sl_cast C C.preS (Ne.symm niPre), install_slot _ (c3Sl_inj C)]
      unfold c3Out; simp
    · rw [if_neg e1]
      by_cases e2 : i = Fin.castAdd (BX + 1) C.postS
      · subst e2; rw [if_pos rfl, hA2, ← c3Sl_cast C C.postS (Ne.symm niPost), install_slot _ (c3Sl_inj C)]
        unfold c3Out; simp [Ne.symm nPP]
      · rw [if_neg e2]
        split_ifs with hp
        · rcases hp with rfl | rfl | rfl | rfl | rfl
          · rw [hA2, install_other _ _ _ _ (c3Sl_ne_in C), A1in, c3In_cast]; unfold c3In; simp
          · have e := install_slot (c3Sl C) (c3Sl_inj C) A1 (c3Out C.inS C.hS C.qS C.mS C.pS C.preS C.postS pfx h Q m pr pre post J) C.hS
            rw [c3Sl_cast C C.hS (Ne.symm niH)] at e
            rw [hA2, e, c3In_cast]
            unfold c3Out c3In; simp [nhPre, nhPost, (Ne.symm niH)]
          · have e := install_slot (c3Sl C) (c3Sl_inj C) A1 (c3Out C.inS C.hS C.qS C.mS C.pS C.preS C.postS pfx h Q m pr pre post J) C.qS
            rw [c3Sl_cast C C.qS (Ne.symm niQ)] at e
            rw [hA2, e, c3In_cast]
            unfold c3Out c3In; simp [nqPre, nqPost, (Ne.symm niQ), (Ne.symm nhQ)]
          · have e := install_slot (c3Sl C) (c3Sl_inj C) A1 (c3Out C.inS C.hS C.qS C.mS C.pS C.preS C.postS pfx h Q m pr pre post J) C.mS
            rw [c3Sl_cast C C.mS (Ne.symm niM)] at e
            rw [hA2, e, c3In_cast]
            unfold c3Out c3In; simp [nmPre, nmPost, (Ne.symm niM), (Ne.symm nhM), (Ne.symm nqM)]
          · have e := install_slot (c3Sl C) (c3Sl_inj C) A1 (c3Out C.inS C.hS C.qS C.mS C.pS C.preS C.postS pfx h Q m pr pre post J) C.pS
            rw [c3Sl_cast C C.pS (Ne.symm niP)] at e
            rw [hA2, e, c3In_cast]
            unfold c3Out c3In; simp [npPre, npPost, (Ne.symm niP), (Ne.symm nhP), (Ne.symm nqP), (Ne.symm nmP)]
        · rfl
  -- 4: residues and the budget
  have hlen : ∀ i, (A2 i).length ≤ thrB B cs pr w.length h Q m := by
    intro i
    refine SourceFactorSel.RunBound.step_len_window st _ i ?_ rfl ?_
    · rw [hIn']; unfold c3In
      split_ifs <;> simp [frame_length, thrB] <;> omega
    · unfold thrB bigCost; omega
  refine ⟨A2, hlen, ?_⟩
  rw [← out] at st
  have st' := st.enlarge (show bigCost pr c + 1 + B ≤ thrB B cs pr w.length h Q m by unfold thrB bigCost; omega)
  exact Shell.ready_of_step st'

end NearCubicWires.WireExponent3_5.PrimAsm.ThrStrip
