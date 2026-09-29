import Proof.Wire_3_5.Primitive.Writers.ThrDataIface2
import Proof.Wire_3_5.Primitive.Writers.ThrDataCost

/-! # PA (d): the THR per-call data stage, v2 (the empty tuple allowed), built

`ThrDataIface2.ThrDataStage2`: the THR data stage for every tuple size `a' ≤ 4`. Two changes to v1:
* the tuple's table runs only if slot `0` is filled: `thrT2 = branchM (sSym 0 0) thrT idle` (at `a' = 0` nothing runs,
  the table and count streams stay blank);
* the collection emits the tuple's count unconditionally (`emitUW` on `sSym 0 5`, then the closing pair): at `a' = 0`
  the count `|tupleG Cs| = 0` (v1's slot test would drop it).

* `thrT2`, `thrCost2`, `ThrPost2`, **`thrT2_stage`**; `thrTabsM2`, **`thrTabs2_step`**; `collectT2`, **`collectT2_spec`**;
  `coreT2`, `thrDataM2`, `thrCoreCost2`, **`thrData2_step`**; **`thrCost2_le`**; **`thrDataStage2 : ThrDataStage2`**.

Paper quantities of the main type: as `ThrDataStage` (the tuple's gate table, the carriers' tables, the slice lengths
`thrCounts`), for every tuple size. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## The table stage, the empty tuple allowed -/

/-- The tuple's table if slot `0` is filled, else nothing. -/
noncomputable def thrT2 := Block.branchM (sTape (nr := DR) (sSym 0 0)) thrT (Block.idle (DS + 2 + DR))

/-- Its cost. -/
noncomputable def thrCost2 {n : ℕ} (a : ℕ) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ) : ℕ :=
  thrCost a Cs L + 2

theorem tupleG_zero {n : ℕ} (Cs : Fin 0 → NormalizedThresholdThresholdCircuit n) : PrimT.ThrTab.tupleG Cs = [] := by
  simp [PrimT.ThrTab.tupleG]

/-- The table stage's exit facts, the empty tuple included: the count stream, the table stream. -/
def ThrPost2 {n a : ℕ} (σ : WState DS DR) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) : Prop :=
  σ.st (sSym 0 5) = List.replicate (PrimT.ThrTab.tupleG Cs).length true ∧ σ.sh (sSym 0 5) = 0 ∧
    σ.st (sSym 0 3) = (if a = 0 then [] else
      FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs))

theorem ThrPost2_tr {n a : ℕ} {σ σ' : WState DS DR} {Cs : Fin a → NormalizedThresholdThresholdCircuit n}
    (h : SameSym σ σ' 0) : ThrPost2 σ Cs → ThrPost2 σ' Cs := by
  intro ⟨b2, b3, b4⟩
  exact ⟨by rw [(h 5).1, b2], by rw [(h 5).2, b3], by rw [(h 3).1, b4]⟩

section Dock2
variable (cap : ℕ)

/-- **The table stage, the empty tuple allowed.** -/
theorem thrT2_stage {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ) (ha : a ≤ 4)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) (σ : WState DS DR)
    (hdone : ∀ i : Fin 4, ∀ h : i.val < a,
      Done σ (symTrip i) (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L)
    (hblank : ∀ i : Fin 4, a ≤ i.val → Blank σ (symTrip i))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0) :
    ∃ σ' : WState DS DR, Step thrT2 (thrCost2 a Cs L) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H
      (wenc cap σ').A ∧ ThrPost2 σ' Cs ∧ (∀ s, (∀ i j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧
      σ'.val = σ.val ∧ σ'.cell = σ.cell := by
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · have e : thrCost2 0 Cs L = 0 + 2 := rfl
    rw [e]
    refine ⟨σ, Block.branch_false _ _ (ListMachine.Print.idle_step _ _) (bit_blank cap σ 0 (hblank 0 (by decide))),
      ⟨?_, (hb 0 5 (by decide)).2, ?_⟩, fun s _ => ⟨rfl, rfl⟩, rfl, rfl⟩
    · rw [tupleG_zero, (hb 0 5 (by decide)).1]; rfl
    · rw [if_pos rfl]; exact (hb 0 3 (by decide)).1
  · obtain ⟨σ', s, p, f, v, c⟩ := thrT_stage cap Cs L ha1 ha hL h2 σ hdone hblank hb
    exact ⟨σ', Block.branch_true _ _ s (bit_done cap σ 0 _ L (hdone 0 ha1)),
      ⟨p.2.1, p.2.2.1, by rw [if_neg (by omega)]; exact p.2.2.2⟩, f, v, c⟩

end Dock2

/-! ## The three table stages -/

/-- The tuple's table (if any), then the two carrier slots. -/
noncomputable def thrTabsM2 := Composition.machine (Composition.machine thrT2 (carT 0)) (carT 1)

/-- Their cost. -/
noncomputable def thrTabsCost2 {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ)
    (ox : Fin 2 → Option (Stars.Carrier n)) : ℕ :=
  thrCost2 a Cs L + 1 + carCostO L (ox 0) + 1 + carCostO L (ox 1)

section Tabs2
variable (cap : ℕ)

theorem thrTabs2_step {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ) (ha : a ≤ 4)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) (ox : Fin 2 → Option (Stars.Carrier n))
    (hLX : ∀ k X, ox k = some X → ∀ g ∈ X, g.encodingBits + 1 ≤ L) (σ : WState DS DR)
    (hdone : ∀ i : Fin 4, ∀ h : i.val < a,
      Done σ (symTrip i) (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L)
    (hblank : ∀ i : Fin 4, a ≤ i.val → Blank σ (symTrip i)) (hpreX : ∀ k, carPre L σ k (ox k))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hbX : ∀ k (j : Fin 1357), 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0) :
    ∃ σ' : WState DS DR, Step thrTabsM2 (thrTabsCost2 Cs L ox) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H
      (wenc cap σ').A ∧ ThrPost2 σ' Cs ∧ (∀ k, carPost σ' k (ox k)) ∧
      (∀ s, (∀ i j, sSym i j ≠ s) → (∀ k j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧
      σ'.val = σ.val ∧ σ'.cell = σ.cell ∧ (∀ k, ox k = none → ∀ j, σ'.st (sCar k j) = σ.st (sCar k j)) := by
  obtain ⟨σ1, s1, p1, f1, v1, c1⟩ := thrT2_stage cap Cs L ha hL h2 σ hdone hblank hb
  have kc : ∀ k, SameCar σ σ1 k := fun k j => f1 (sCar k j) (fun i j' => sSym_ne_sCar i j' k j)
  obtain ⟨σ2, s2, p2, f2, v2, c2, n2⟩ := carT_stage2 cap L 0 (ox 0) σ1 (carPre_tr L (kc 0) _ (hpreX 0))
    (blankCar_tr (kc 0) (hbX 0)) (hLX 0) h2
  obtain ⟨σ3, s3, p3, f3, v3, c3, n3⟩ := carT_stage2 cap L 1 (ox 1) σ2
    (carPre_tr L ((kc 1).trans (car_keeps_car f2 1 (by decide))) _ (hpreX 1))
    (blankCar_tr ((kc 1).trans (car_keeps_car f2 1 (by decide))) (hbX 1)) (hLX 1) h2
  refine ⟨σ3, (s1.seq s2).seq s3, ThrPost2_tr ((car_keeps_sym f2 0).trans (car_keeps_sym f3 0)) p1, ?_, ?_,
    by rw [v3, v2, v1], by rw [c3, c2, c1], ?_⟩
  rotate_left 2
  · intro k hk j
    have k01 : k = 0 ∨ k = 1 := by
      rcases k with ⟨k, hk2⟩
      interval_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases k01 with rfl | rfl
    · have e2 : σ2 = σ1 := n2 hk
      rw [((car_keeps_car f3 0 (by decide)) j).1, e2, ((kc 0) j).1]
    · have e3 : σ3 = σ2 := n3 hk
      rw [e3, ((car_keeps_car f2 1 (by decide)) j).1, ((kc 1) j).1]
  · intro k
    fin_cases k
    · exact carPost_tr (car_keeps_car f3 0 (by decide)) _ p2
    · exact p3
  · intro s hs hs'
    have e1 := f1 s hs
    have e2 := f2 s (fun j => hs' 0 j)
    have e3 := f3 s (fun j => hs' 1 j)
    exact ⟨e3.1.trans (e2.1.trans e1.1), e3.2.trans (e2.2.trans e1.2)⟩

end Tabs2

/-! ## The collection -/

/-- **The collection**: the leading `0`, the carriers' counts, the tuple's count (unconditionally), the closing `0`. -/
def collectT2 : WM DS DR :=
  .seq (.wr sOUT false) (.seq (.fwd sOUT) (.seq (slotsC carC) (.seq (.seq (emitUW (sSym 0 5))
    (emitPair sOUT rOP false)) (.wr sOUT false))))

def collectCostT2 (cx : List ℕ) (c : ℕ) : ℕ :=
  1 + 1 + (1 + 1 + (slotsCost carC cx + 1 + ((c * 19 + 1 + 1 + 15) + 1 + 1)))

section Col2
variable (cap : ℕ)

/-- **The collection's spec**: the output stream holds `dataWord (cx ++ [c])`. -/
theorem collectT2_spec (σ : WState DS DR) (cx : List ℕ) (c : ℕ) (hx : cx.length ≤ 2)
    (hcx : ∀ k : Fin 2, ∀ h : k.val < cx.length, readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = true ∧
      σ.st (sCar k 5) = List.replicate (cx.get ⟨k.val, h⟩) true ∧ σ.sh (sCar k 5) = 0)
    (hcx' : ∀ k : Fin 2, cx.length ≤ k.val → readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = false)
    (hT : σ.st (sSym 0 5) = List.replicate c true ∧ σ.sh (sSym 0 5) = 0)
    (hO : σ.st sOUT = []) (hOh : σ.sh sOUT = 0) (hOP : σ.val rOP = 0)
    (hcap : 2 * (unaryList cx).length + 2 * (unaryList [c]).length + 2 ≤ cap) :
    ∃ τ : WState DS DR, WExec cap collectT2 σ τ (collectCostT2 cx c) ∧ τ.st sOUT = dataWord (cx ++ [c]) ∧
      (∀ s, s ≠ sOUT → τ.st s = σ.st s) ∧ (∀ r, r ≠ rOP → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have w1 := WExec.wr (cap := cap) sOUT false σ
  set σ1 := σ.sets sOUT (writeTapeBit (σ.st sOUT) (σ.sh sOUT) false) with hσ1
  have f1 := WExec.fwd (cap := cap) sOUT σ1
  set σ2 := σ1.seth sOUT (σ1.sh sOUT + 1) with hσ2
  have st2 : ∀ s, s ≠ sOUT → σ2.st s = σ.st s := fun s hs => by simp [hσ2, hσ1, Function.update_apply, hs]
  have sh2 : ∀ s, s ≠ sOUT → σ2.sh s = σ.sh s := fun s hs => by simp [hσ2, hσ1, Function.update_apply, hs]
  have o2 : σ2.st sOUT = [false] := by simp [hσ2, hσ1, hO, hOh, writeTapeBit]
  obtain ⟨τ1, q1, a1, b1, c1, d1, e1, g1, i1⟩ := slotsC_spec cap carC cx σ2 (by simpa [carC] using hx)
    (fun k h hl => by
      rw [carC_get]
      obtain ⟨x1, x2, x3⟩ := hcx ⟨k, by simpa [carC] using hl⟩ h
      exact ⟨by rw [st2 _ (sCar_ne_low _ _ _ sOUT_low), sh2 _ (sCar_ne_low _ _ _ sOUT_low)]; exact x1,
        by rw [st2 _ (sCar_ne_low _ _ _ sOUT_low)]; exact x2, by rw [sh2 _ (sCar_ne_low _ _ _ sOUT_low)]; exact x3⟩)
    (fun k hl hk => by
      rw [carC_get]
      rw [st2 _ (sCar_ne_low _ _ _ sOUT_low), sh2 _ (sCar_ne_low _ _ _ sOUT_low)]
      exact hcx' ⟨k, by simpa [carC] using hl⟩ hk)
    carC_no carC_pw (by rw [o2]; simp [hσ2, hσ1, hOh]) (by simp [hσ2, hσ1, hOP]; omega)
  have csh : ∀ j, τ1.sh (sSym 0 j) = σ.sh (sSym 0 j) := by
    intro j
    rw [e1 _ (sSym_ne_low _ _ _ sOUT_low) (fun t ht => by
      simp only [carC, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> exact sSym_ne_sCar _ _ _ _), sh2 _ (sSym_ne_low _ _ _ sOUT_low)]
  have cst : ∀ j, τ1.st (sSym 0 j) = σ.st (sSym 0 j) := by
    intro j
    rw [d1 _ (sSym_ne_low _ _ _ sOUT_low), st2 _ (sSym_ne_low _ _ _ sOUT_low)]
  obtain ⟨hT5, hT5h⟩ := hT
  have hml := RepairOrdinary.Streaming.marks_length (List.replicate c true)
  have hu1 : (unaryList [c]).length = c + 1 := by simp [unaryList]
  have r1 : τ1.val rOP = 2 * (unaryList cx).length := by rw [c1]; simp [hσ2, hσ1, hOP]
  have u1 := emitUW_spec cap (sSym 0 5) (sSym_ne_low _ _ _ sOUT_low) c τ1 (by rw [cst]; exact hT5)
    (by rw [csh]; exact hT5h) b1 (by rw [r1]; omega)
  set τ3 := (appendO τ1 sOUT rOP (marks (List.replicate c true))).seth (sSym 0 5) c with hτ3
  have u2 := emitPair_spec cap sOUT rOP false τ3
    (by simp [hτ3, Function.update_apply, Ne.symm (sSym_ne_low 0 5 sOUT sOUT_low), b1])
    (by simp [hτ3] at hml ⊢; rw [r1]; omega)
  set τ2 := appendO τ3 sOUT rOP [true, false] with hτ2
  have b2 : τ2.sh sOUT = (τ2.st sOUT).length := by
    simp [hτ2, hτ3, Function.update_apply, Ne.symm (sSym_ne_low 0 5 sOUT sOUT_low), b1] at hml ⊢ <;> omega
  have a2 : τ2.st sOUT = τ1.st sOUT ++ marks (unaryList [c]) := by
    rw [marks_unary_cons]
    simp [hτ2, hτ3, unaryList, marks, List.append_assoc]
  have d2 : ∀ s, s ≠ sOUT → τ2.st s = τ1.st s := fun s hs => by
    simp [hτ2, hτ3, Function.update_apply, hs]
  have g2 : ∀ r, r ≠ rOP → τ2.val r = τ1.val r := fun r hr => by
    simp [hτ2, hτ3, Function.update_apply, hr]
  have i2 : τ2.cell = τ1.cell := by simp [hτ2, hτ3]
  have q2 : WExec cap (.seq (emitUW (sSym 0 5)) (emitPair sOUT rOP false)) τ1 τ2 (c * 19 + 1 + 1 + 15) :=
    WExec.seq u1 u2
  have w3 := WExec.wr (cap := cap) sOUT false τ2
  refine ⟨τ2.sets sOUT (writeTapeBit (τ2.st sOUT) (τ2.sh sOUT) false), ?_, ?_, ?_, ?_, ?_⟩
  · exact WExec.cast cap (WExec.seq w1 (WExec.seq f1 (WExec.seq q1 (WExec.seq q2 w3)))) rfl
      (by unfold collectCostT2; omega)
  · simp only [WState.sets_st, Function.update_apply, if_pos rfl]
    rw [b2, wtb_end, a2, a1, o2, dataWord, unaryList_append, ← RankBody.marks_frame, marks_append]
    simp [List.append_assoc]
  · intro s hs
    simp only [WState.sets_st, Function.update_apply, if_neg hs]
    rw [d2 s hs, d1 s hs, st2 s hs]
  · intro r hr
    simp only [WState.sets_val]
    rw [g2 r hr, g1 r hr]
    simp [hσ2, hσ1]
  · simp only [WState.sets_cell]
    rw [i2, i1]
    simp [hσ2, hσ1]

end Col2

/-! ## The stage as one run -/

/-- The stage before its teardown: the fill, the inputs, the tables, the collection. -/
noncomputable def coreT2 := Composition.machine (Composition.machine (Composition.machine fillAct.compile
  setupW.toProg.compile) thrTabsM2) collectT2.toProg.compile

/-- **The THR per-call data stage** (every head back at `0`). -/
noncomputable def thrDataM2 := MaskedReset.machine coreT2 (fun _ => true)

section Run2
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- The stage's cost before the teardown. -/
noncomputable def thrCoreCost2 (L W : ℕ) : ℕ :=
  11 * W + 20 + 1 + 1 + 1 + setupCost n L (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) + 1 +
    thrTabsCost2 Cs L (oxOf carriers) + 1 +
    collectCostT2 (carriers.map (·.length)) (PrimT.ThrTab.tupleG Cs).length

/-- **The THR per-call data stage's run** (the `ThrDataStage.run` shape): from `frame w` (`w` the THR request's word
shape), `1^n`, `1^L`, `1^W`, in `2·thrCoreCost + 2` steps, every head back at `0`: the output stream holds
`dataWord (thrCounts …)`, the request stays, the tuple's table is on `sSym 0 3`, each filled carrier slot holds its
table and each empty one stays blank. -/
theorem thrData2_step (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2) :
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ),
      Step thrDataM2 (2 * thrCoreCost2 a' Cs carriers L W + 2) (fun _ => 0)
        (Fin.addCases (rawIn (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) n L W)
          (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape sOUT) = dataWord (thrCounts Cs carriers) ∧
      tout (sTape sIN) =
        RepairOrdinary.frame (reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape (sSym 0 3)) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = [] := by
  set w := reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl with hw
  set cap := 2 * W + 2 with hcap
  have hcl : (ReqBridge.thrCodes Cs).length = a' := by simp [ReqBridge.thrCodes]
  have h4 : 4 ≤ cap := by
    have hb : 1 ≤ natBitLength a' := by unfold natBitLength; omega
    have : 2 ^ 2 ≤ 2 ^ (natBitLength a' + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- 0: the fill and the cell
  have s0 := Exec.step (fillAct_exec w n L W)
  -- 1: the slots' inputs
  obtain ⟨τ1, q1, d1, b1, dx1, bx1, f1, i1, v1, c1⟩ := setup_spec cap n L true (ReqBridge.thrCodes Cs)
    (carriers.map Stars.Carrier.code) tl (σ0 w n L W) (by rw [hcl]; exact ha) (by simpa using hk)
    (by simp [σ0, hw]) rfl (by simp [σ0, sNT, sIN]) rfl (by simp [σ0, sLT, sIN, sNT]) rfl
    (fun i => ⟨σ0_sym w L W i 0, rfl, σ0_sym w L W i 1, rfl, σ0_sym w L W i 2, rfl⟩)
    (fun k => ⟨σ0_car w L W k 0, rfl, σ0_car w L W k 1, rfl, σ0_car w L W k 2, rfl⟩)
    rfl rfl rfl rfl rfl rfl rfl rfl hcN (by rw [hcl]; exact hcA) (by simpa using hcK) hcx hcy h4
  have s1 := Exec.step (WExec.exec cap q1)
  -- 2: the tables
  have keepS : ∀ i : Fin 4, ∀ j : Fin 1789, 3 ≤ j.val → τ1.st (sSym i j) = [] ∧ τ1.sh (sSym i j) = 0 := by
    intro i j hj
    have hnot : ∀ i', ¬ tmem (sSym i j) (symTrip i') := by
      intro i' hm
      simp only [symTrip, tmem, sSym_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sSym i j) hnot (fun k => not_tmem_carTrip_of_sym _ _ _) (sSym_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (σ0_sym w L W i j), this.2⟩
  have keepC : ∀ k : Fin 2, ∀ j : Fin 1357, 3 ≤ j.val → τ1.st (sCar k j) = [] ∧ τ1.sh (sCar k j) = 0 := by
    intro k j hj
    have hnot : ∀ k', ¬ tmem (sCar k j) (carTrip k') := by
      intro k' hm
      simp only [carTrip, tmem, sCar_eq_iff] at hm
      rcases hm with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp at hj
    have := f1 (sCar k j) (fun i => not_tmem_symTrip_of_car _ _ _) hnot (sCar_ne_low _ _ _ (by decide))
    exact ⟨this.1.trans (σ0_car w L W k j), this.2⟩
  obtain ⟨σ2, s2, p2, px2, f2, v2, c2, n2⟩ := thrTabs2_step cap Cs L ha hL h2 (oxOf carriers)
    (fun k X hX => by
      unfold oxOf at hX
      exact hLX X (List.mem_of_getElem? hX))
    τ1
    (fun i h => by
      have := d1 i (by rw [hcl]; exact h)
      simpa [ReqBridge.thrCodes] using this)
    (fun i h => b1 i (by rw [hcl]; exact h))
    (fun k => by
      unfold oxOf
      by_cases hk' : k.val < carriers.length
      · rw [List.getElem?_eq_getElem hk']
        have := dx1 k (by simpa using hk')
        simpa [carPre] using this
      · rw [List.getElem?_eq_none (by omega)]
        exact bx1 k (by simpa using (by omega : carriers.length ≤ k.val)))
    keepS keepC
  -- 3: the collection
  have oOUT : σ2.st sOUT = [] ∧ σ2.sh sOUT = 0 := by
    have a := f2 sOUT (fun i j => sSym_ne_low _ _ _ sOUT_low) (fun k j => sCar_ne_low _ _ _ sOUT_low)
    have b := f1 sOUT (fun i => low_not_tmem_sym _ sOUT_low i) (fun k => low_not_tmem_car _ sOUT_low k) (by decide)
    refine ⟨by rw [a.1, b.1]; simp [σ0, sOUT, sIN, sNT, sLT, sCT, sAUX], by rw [a.2, b.2]; rfl⟩
  have hcu' : 2 * (unaryList (carriers.map (·.length))).length +
      2 * (unaryList [(PrimT.ThrTab.tupleG Cs).length]).length + 2 ≤ cap := by
    have := hcu
    rw [thrCounts, unaryList_append, List.length_append] at this
    omega
  obtain ⟨τ3, q3, o3, f3, v3, c3⟩ := collectT2_spec cap σ2 (carriers.map (·.length))
    (PrimT.ThrTab.tupleG Cs).length (by simpa using hk)
    (fun k h => by
      have hk' : k.val < carriers.length := by simpa using h
      have := px2 k
      simp only [oxOf, List.getElem?_eq_getElem hk', carPost] at this
      obtain ⟨x1, x2, x3, _⟩ := this
      exact ⟨x1, by simpa using x2, x3⟩)
    (fun k h => by
      have hk' : carriers.length ≤ k.val := by simpa using h
      have := px2 k
      simp only [oxOf, List.getElem?_eq_none hk', carPost] at this
      exact this)
    ⟨p2.1, p2.2.1⟩ oOUT.1 oOUT.2 (by rw [v2, v1 rOP (by decide) (by decide)]; rfl) hcu'
  have s3 := Exec.step (WExec.exec cap q3)
  have core : Step coreT2 (thrCoreCost2 a' Cs carriers L W) (fun _ => 0) (rawIn w n L W) (wenc cap τ3).H
      (wenc cap τ3).A :=
    ((s0.seq s1).seq s2).seq s3
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (DS + 2 + DR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc cap τ3).H i)
      (fun _ : Fin 1 => 0) : Fin (DS + 2 + DR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc cap τ3).A, m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hm.congr_in eh rfl).congr eh' rfl
  · rw [wenc_A_s, o3]
    rfl
  · rw [wenc_A_s, f3 _ (by decide)]
    have a := f2 sIN (fun i j => sSym_ne_low _ _ _ (by decide)) (fun k j => sCar_ne_low _ _ _ (by decide))
    rw [a.1, i1]
    simp [σ0, hw]
  · rw [wenc_A_s, f3 _ (sSym_ne_low _ _ _ sOUT_low)]
    exact p2.2.2
  · intro k h
    rw [wenc_A_s, f3 _ (sCar_ne_low _ _ _ sOUT_low)]
    have := px2 k
    simp only [oxOf, List.getElem?_eq_getElem h, carPost] at this
    exact this.2.2.2
  · intro k h
    rw [wenc_A_s, f3 _ (sCar_ne_low _ _ _ sOUT_low), n2 k (by simp [oxOf, List.getElem?_eq_none h]) 3]
    exact (keepC k 3 (by decide)).1

end Run2

/-! ## The cost -/

/-- **The THR data stage's cost is polynomial** in `K + n + L + W`. -/
theorem thrCost2_le {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (L W K : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (hK : ∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ K)
    (hKX : ∀ X ∈ carriers, natBitLength X.code ≤ K) (h2 : 2 ≤ n + L) :
    PolyBounded (2 * thrCoreCost2 a' Cs carriers L W + 2) (K + n + L + W) (40 * cTT + 80 * cX + 70100) dD := by
  unfold PolyBounded
  obtain ⟨P, hP⟩ : ∃ P, P = (K + n + L + W + 1) ^ dD := ⟨_, rfl⟩
  have hP1 : K + n + L + W + 1 ≤ P := by
    rw [hP]
    have : 1 ≤ dD := by unfold dD; omega
    calc K + n + L + W + 1 = (K + n + L + W + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) this
  rw [← hP]
  have tTG : thrCost a' Cs L ≤ cTT * (K + n + L + W + 1) ^ dD + 6 ∧
      (PrimT.ThrTab.tupleG Cs).length ≤ cTT * (K + n + L + W + 1) ^ dD := by
    rcases Nat.eq_zero_or_pos a' with h0 | h1
    · subst h0
      refine ⟨by show 0 ≤ _; omega, by rw [tupleG_zero]; simp⟩
    · exact thr_piece Cs L K (K + n + L + W) h1 ha hL hK h2 (by omega)
  obtain ⟨tT, tG⟩ := tTG
  rw [← hP] at tT tG
  -- the carriers
  have hcar : ∀ k : Fin 2, carCostO L (oxOf carriers k) ≤ cX * P + 2 := by
    intro k
    unfold oxOf
    by_cases hkl : k.val < carriers.length
    · rw [List.getElem?_eq_getElem hkl]
      have hm := List.getElem_mem hkl
      have := (car_piece _ L K (K + n + L + W) (hLX _ hm) (hKX _ hm) h2 (by omega)).1
      rw [← hP] at this
      show PrimT.CarTable.carTableCost _ L + 2 ≤ _
      omega
    · rw [List.getElem?_eq_none (by omega)]
      show 2 ≤ _
      omega
  have hsum : (carriers.map (·.length)).sum ≤ 2 * (cX * P) := by
    have hX : ∀ X ∈ carriers, X.length ≤ cX * P := fun X hX => by
      have := (car_piece X L K (K + n + L + W) (hLX X hX) (hKX X hX) h2 (by omega)).2
      rw [← hP] at this; exact this
    have : (carriers.map (·.length)).sum ≤ carriers.length * (cX * P) := by
      have := List.sum_le_card_nsmul (carriers.map (·.length)) (cX * P) (fun x hx => by
        rw [List.mem_map] at hx
        obtain ⟨X, hX', rfl⟩ := hx
        exact hX X hX')
      simpa using this
    calc _ ≤ carriers.length * (cX * P) := this
      _ ≤ 2 * (cX * P) := Nat.mul_le_mul_right _ hk
  -- the setup
  have hcodes : ∀ x ∈ ReqBridge.thrCodes Cs, natBitLength x ≤ K := by
    intro x hx
    simp only [ReqBridge.thrCodes, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hK i
  have hcc : ∀ y ∈ carriers.map Stars.Carrier.code, natBitLength y ≤ K := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨X, hX, rfl⟩ := hy
    exact hKX X hX
  have b1 : blocksCost n L symTrips (ReqBridge.thrCodes Cs) ≤ 4 * (140 * K + 18 * n + 18 * L + 201) :=
    blocksCost_le n L K symTrips (ReqBridge.thrCodes Cs) hcodes
  have b2 : blocksCost n L carTrips (carriers.map Stars.Carrier.code) ≤ 2 * (140 * K + 18 * n + 18 * L + 201) :=
    blocksCost_le n L K carTrips (carriers.map Stars.Carrier.code) hcc
  have hlenc : (ReqBridge.thrCodes Cs).length ≤ 4 := by simp [ReqBridge.thrCodes]; omega
  have hlencc : (carriers.map Stars.Carrier.code).length ≤ 4 := by simp; omega
  have s1 := nbl_small _ hlenc
  have s2 := nbl_small _ hlencc
  have hnb := CopyNat.natBitLength_le_self_succ n
  have hsetup : setupCost n L (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) ≤ 30000 * P := by
    unfold setupCost
    omega
  -- the collection
  have hcol := slotsCost_le carC (carriers.map (·.length))
  have hcolT := slotsCost_le thrC [(PrimT.ThrTab.tupleG Cs).length]
  rw [show carC.length = 2 from rfl] at hcol
  rw [show thrC.length = 1 from rfl, List.sum_singleton] at hcolT
  -- the tables
  have h0 := hcar 0
  have h1 := hcar 1
  unfold thrCoreCost2 thrTabsCost2 collectCostT2 thrCost2
  have e : (40 * cTT + 80 * cX + 70100) * P = 40 * (cTT * P) + 80 * (cX * P) + 70100 * P := by ring
  rw [e]
  clear hcolT s1 s2 b1 b2 hlenc hlencc hcodes hcc
  generalize setupCost n L (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) = t1 at hsetup ⊢
  generalize thrCost a' Cs L = t2 at tT ⊢
  generalize carCostO L (oxOf carriers 0) = t3 at h0 ⊢
  generalize carCostO L (oxOf carriers 1) = t4 at h1 ⊢
  generalize slotsCost carC (carriers.map (·.length)) = t5 at hcol ⊢
  generalize (PrimT.ThrTab.tupleG Cs).length = t6 at tG ⊢
  generalize cTT * P = t7 at tT tG ⊢
  generalize cX * P = t8 at h0 h1 hsum ⊢
  generalize (carriers.map (·.length)).sum = t9 at hsum hcol ⊢
  omega

/-! ## The packaged stage -/

/-- **The THR per-call data stage, v2** (`ThrDataIface2.ThrDataStage2`): `thrDataM2`, the tuple's table on `sSym 0 3`
(blank for the empty tuple), the cost `2·thrCoreCost2 + 2`, polynomial by `thrCost2_le`, the run `thrData2_step`. -/
noncomputable def thrDataStage2 : ThrDataStage2 where
  s := _
  M := thrDataM2
  tabS := sSym 0 3
  cost := fun a' Cs carriers L W => 2 * thrCoreCost2 a' Cs carriers L W + 2
  Cc := 40 * cTT + 80 * cX + 70100
  Dc := dD
  cost_le := fun Cs carriers L W K ha hk hL hLX hK hKX h2 =>
    thrCost2_le Cs carriers L W K ha hk hL hLX hK hKX h2
  run := fun Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu =>
    thrData2_step _ Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
