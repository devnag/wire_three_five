import Proof.Wire_3_5.Primitive.Writers.DataRun

/-! # PA (d), the per-call data stage, part 4: the unfilled slots stay blank (`data_step_blank`, /(A))

`Data.data_step` (verified) states the tables of the FILLED slots only. The gate-frame converter
(G1/G2, P3:1655-1664: the pool's gates in slot order) reads every slot's table stream, a blank one as an empty gate list,
so it needs the unfilled slots' streams `3` blank. This file re-runs the same stage with the empty slots' stages the
identity (`symT_off`, `carT_off`: the setup leaves those streams blank):

* `symT_stage2`, `carT_stage2` (`Data`'s slot stages, with `none → σ' = σ`), `tabs_step2`;
* **`data_step_blank`**: `data_step`'s statement, plus `∀ i, a' ≤ i → tout (sSym i 3) = []` and
  `∀ k, |carriers| ≤ k → tout (sCar k 3) = []`.

Paper quantities of the main type: the count list of the call's slices and the gate tables (as `data_step`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Stages2
variable (cap : ℕ) {n : ℕ} (L : ℕ)

/-- `symT_stage`, with the empty slot's stage the identity. -/
theorem symT_stage2 (i : Fin 4) (oc : Option (NormalizedSymmetricThresholdCircuit n)) (σ : WState DS DR)
    (hpre : symPre L σ i oc) (hb : ∀ j : Fin 1789, 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hL : ∀ C, oc = some C → C.descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step (symT i) (symCostO L oc) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      symPost σ' i oc ∧ (∀ s, (∀ j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell ∧ (oc = none → σ' = σ) := by
  cases oc with
  | none =>
    refine ⟨σ, symT_off cap i σ hpre, ?_, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => rfl⟩
    obtain ⟨b1, b2, _, _, _, _⟩ := hpre
    simp only [symTrip] at b1 b2
    show readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = false
    rw [b1]
    rfl
  | some C =>
    obtain ⟨σ', s, p, f, v, c⟩ := symT_stage cap L i (some C) σ hpre hb hL h2
    exact ⟨σ', s, p, f, v, c, fun h => by cases h⟩

/-- `carT_stage`, with the empty slot's stage the identity. -/
theorem carT_stage2 (k : Fin 2) (ox : Option (Stars.Carrier n)) (σ : WState DS DR)
    (hpre : carPre L σ k ox) (hb : ∀ j : Fin 1357, 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0)
    (hL : ∀ X, ox = some X → ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step (carT k) (carCostO L ox) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      carPost σ' k ox ∧ (∀ s, (∀ j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell ∧ (ox = none → σ' = σ) := by
  cases ox with
  | none =>
    refine ⟨σ, carT_off cap k σ hpre, ?_, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => rfl⟩
    obtain ⟨b1, b2, _, _, _, _⟩ := hpre
    simp only [carTrip] at b1 b2
    show readTapeBit (σ.st (sCar k 0)) (σ.sh (sCar k 0)) = false
    rw [b1]
    rfl
  | some X =>
    obtain ⟨σ', s, p, f, v, c⟩ := carT_stage cap L k (some X) σ hpre hb hL h2
    exact ⟨σ', s, p, f, v, c, fun h => by cases h⟩

end Stages2

section Chain2
variable {n : ℕ} (L : ℕ) (cap : ℕ)

theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  rcases i with ⟨i, hi⟩
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨k, hk⟩
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The six table stages**, `tabs_step` plus: an empty slot's streams are unchanged. -/
theorem tabs_step2 (oc : Fin 4 → Option (NormalizedSymmetricThresholdCircuit n)) (ox : Fin 2 → Option (Stars.Carrier n))
    (σ : WState DS DR) (hpre : ∀ i, symPre L σ i (oc i)) (hpreX : ∀ k, carPre L σ k (ox k))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hbX : ∀ k (j : Fin 1357), 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0)
    (hL : ∀ i C, oc i = some C → C.descriptionBits ≤ L)
    (hLX : ∀ k X, ox k = some X → ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step tabsM (tabsCost L oc ox) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      (∀ i, symPost σ' i (oc i)) ∧ (∀ k, carPost σ' k (ox k)) ∧
      (∀ s, (∀ i j, sSym i j ≠ s) → (∀ k j, sCar k j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧
      σ'.val = σ.val ∧ σ'.cell = σ.cell ∧
      (∀ i, oc i = none → ∀ j, σ'.st (sSym i j) = σ.st (sSym i j)) ∧
      (∀ k, ox k = none → ∀ j, σ'.st (sCar k j) = σ.st (sCar k j)) := by
  obtain ⟨σ1, s1, p1, f1, v1, c1, n1⟩ := symT_stage2 cap L 0 (oc 0) σ (hpre 0) (hb 0) (hL 0) h2
  obtain ⟨σ2, s2, p2, f2, v2, c2, n2⟩ := symT_stage2 cap L 1 (oc 1) σ1
    (symPre_tr L (sym_keeps_sym f1 1 (by decide)) _ (hpre 1)) (blankSym_tr (sym_keeps_sym f1 1 (by decide)) (hb 1))
    (hL 1) h2
  obtain ⟨σ3, s3, p3, f3, v3, c3, n3⟩ := symT_stage2 cap L 2 (oc 2) σ2
    (symPre_tr L ((sym_keeps_sym f1 2 (by decide)).trans (sym_keeps_sym f2 2 (by decide))) _ (hpre 2))
    (blankSym_tr ((sym_keeps_sym f1 2 (by decide)).trans (sym_keeps_sym f2 2 (by decide))) (hb 2)) (hL 2) h2
  obtain ⟨σ4, s4, p4, f4, v4, c4, n4⟩ := symT_stage2 cap L 3 (oc 3) σ3
    (symPre_tr L (((sym_keeps_sym f1 3 (by decide)).trans (sym_keeps_sym f2 3 (by decide))).trans
      (sym_keeps_sym f3 3 (by decide))) _ (hpre 3))
    (blankSym_tr (((sym_keeps_sym f1 3 (by decide)).trans (sym_keeps_sym f2 3 (by decide))).trans
      (sym_keeps_sym f3 3 (by decide))) (hb 3)) (hL 3) h2
  have kc : ∀ k, SameCar σ σ4 k := fun k =>
    (((sym_keeps_car f1 k).trans (sym_keeps_car f2 k)).trans (sym_keeps_car f3 k)).trans (sym_keeps_car f4 k)
  obtain ⟨σ5, s5, p5, f5, v5, c5, n5⟩ := carT_stage2 cap L 0 (ox 0) σ4 (carPre_tr L (kc 0) _ (hpreX 0))
    (blankCar_tr (kc 0) (hbX 0)) (hLX 0) h2
  obtain ⟨σ6, s6, p6, f6, v6, c6, n6⟩ := carT_stage2 cap L 1 (ox 1) σ5
    (carPre_tr L ((kc 1).trans (car_keeps_car f5 1 (by decide))) _ (hpreX 1))
    (blankCar_tr ((kc 1).trans (car_keeps_car f5 1 (by decide))) (hbX 1)) (hLX 1) h2
  have t56 : ∀ i, SameSym σ4 σ6 i := fun i => (car_keeps_sym f5 i).trans (car_keeps_sym f6 i)
  refine ⟨σ6, ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact symPost_tr (((sym_keeps_sym f2 0 (by decide)).trans (sym_keeps_sym f3 0 (by decide))).trans
        ((sym_keeps_sym f4 0 (by decide)).trans (t56 0))) _ p1
    · exact symPost_tr ((sym_keeps_sym f3 1 (by decide)).trans ((sym_keeps_sym f4 1 (by decide)).trans (t56 1))) _ p2
    · exact symPost_tr ((sym_keeps_sym f4 2 (by decide)).trans (t56 2)) _ p3
    · exact symPost_tr (t56 3) _ p4
  · intro k
    rcases fin2_cases k with rfl | rfl
    · exact carPost_tr (car_keeps_car f6 0 (by decide)) _ p5
    · exact p6
  · intro s hs hs'
    have e1 := f1 s (fun j => hs 0 j)
    have e2 := f2 s (fun j => hs 1 j)
    have e3 := f3 s (fun j => hs 2 j)
    have e4 := f4 s (fun j => hs 3 j)
    have e5 := f5 s (fun j => hs' 0 j)
    have e6 := f6 s (fun j => hs' 1 j)
    exact ⟨e6.1.trans (e5.1.trans (e4.1.trans (e3.1.trans (e2.1.trans e1.1)))),
      e6.2.trans (e5.2.trans (e4.2.trans (e3.2.trans (e2.2.trans e1.2))))⟩
  · rw [v6, v5, v4, v3, v2, v1]
  · rw [c6, c5, c4, c3, c2, c1]
  · intro i hi j
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · have e : σ1 = σ := n1 hi
      rw [(t56 0 j).1, (sym_keeps_sym f4 0 (by decide) j).1, (sym_keeps_sym f3 0 (by decide) j).1,
        (sym_keeps_sym f2 0 (by decide) j).1, e]
    · have e : σ2 = σ1 := n2 hi
      rw [(t56 1 j).1, (sym_keeps_sym f4 1 (by decide) j).1, (sym_keeps_sym f3 1 (by decide) j).1, e,
        (sym_keeps_sym f1 1 (by decide) j).1]
    · have e : σ3 = σ2 := n3 hi
      rw [(t56 2 j).1, (sym_keeps_sym f4 2 (by decide) j).1, e, (sym_keeps_sym f2 2 (by decide) j).1,
        (sym_keeps_sym f1 2 (by decide) j).1]
    · have e : σ4 = σ3 := n4 hi
      rw [(t56 3 j).1, e, (sym_keeps_sym f3 3 (by decide) j).1, (sym_keeps_sym f2 3 (by decide) j).1,
        (sym_keeps_sym f1 3 (by decide) j).1]
  · intro k hk j
    rcases fin2_cases k with rfl | rfl
    · have e : σ5 = σ4 := n5 hk
      rw [(car_keeps_car f6 0 (by decide) j).1, e, (kc 0 j).1]
    · have e : σ6 = σ5 := n6 hk
      rw [e, (car_keeps_car f5 1 (by decide) j).1, (kc 1 j).1]

end Chain2

section Run
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The per-call data stage with the empty slots** (SYM, `data_step` plus the unfilled slots' table streams blank): from `frame w` (`w` the request's word shape, circuits' and carriers' codes),
`1^n`, `1^L`, `1^W`, in `2·coreCost + 2` steps, every head back at `0`: the output stream holds
`dataWord (symCounts …)`, the request stays, and each filled slot holds the table. -/
theorem data_step_blank (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (carriers.map (·.length))).length +
      2 * (unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2) :
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ),
      Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun _ => 0)
        (Fin.addCases (rawIn (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W)
          (fun _ : Fin 1 => List.replicate 0 false))
        (fun _ => 0) (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) ∧
      tout (sTape sOUT) = dataWord (symCounts a' Cs carriers) ∧
      tout (sTape sIN) = RepairOrdinary.frame (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (sTape (sSym i 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (sTape (sSym i 3)) = []) ∧
      (∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = []) := by
  set w := reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl with hw
  set cap := 2 * W + 2 with hcap
  have hcl : (symCodes a' Cs).length = a' := by simp [symCodes]
  have h4 : 4 ≤ cap := by
    have hb : 1 ≤ natBitLength a' := by unfold natBitLength; omega
    have : 2 ^ 2 ≤ 2 ^ (natBitLength a' + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  -- 0: the fill and the cell
  have s0 := Exec.step (fillAct_exec w n L W)
  -- 1: the slots' inputs
  obtain ⟨τ1, q1, d1, b1, dx1, bx1, f1, i1, v1, c1⟩ := setup_spec cap n L false (symCodes a' Cs)
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
  obtain ⟨σ2, s2, p2, px2, f2, v2, c2, n2, nx2⟩ := tabs_step2 L cap (ocOf a' Cs) (oxOf carriers) τ1
    (fun i => by
      unfold ocOf
      split
      · next h =>
        have := d1 i (by rw [hcl]; exact h)
        simpa [symPre, symCodes] using this
      · next h => exact b1 i (by rw [hcl]; omega))
    (fun k => by
      unfold oxOf
      by_cases hk' : k.val < carriers.length
      · rw [List.getElem?_eq_getElem hk']
        have := dx1 k (by simpa using hk')
        simpa [carPre] using this
      · rw [List.getElem?_eq_none (by omega)]
        exact bx1 k (by simpa using (by omega : carriers.length ≤ k.val)))
    keepS keepC
    (fun i C hC => by
      unfold ocOf at hC
      split at hC
      · cases hC; exact hL _
      · cases hC)
    (fun k X hX => by
      unfold oxOf at hX
      exact hLX X (List.mem_of_getElem? hX))
    h2
  -- 3: the collection
  have oOUT : σ2.st sOUT = [] ∧ σ2.sh sOUT = 0 := by
    have a := f2 sOUT (fun i j => sSym_ne_low _ _ _ sOUT_low) (fun k j => sCar_ne_low _ _ _ sOUT_low)
    have b := f1 sOUT (fun i => low_not_tmem_sym _ sOUT_low i) (fun k => low_not_tmem_car _ sOUT_low k) (by decide)
    refine ⟨by rw [a.1, b.1]; simp [σ0, sOUT, sIN, sNT, sLT, sCT, sAUX], by rw [a.2, b.2]; rfl⟩
  obtain ⟨τ3, q3, o3, f3, v3, c3⟩ := collect_spec cap σ2 (carriers.map (·.length))
    (List.ofFn fun i => (Stars.symGates (Cs i)).length) (by simpa using hk) (by simpa using ha)
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
    (fun i h => by
      have hi : i.val < a' := by simpa using h
      have := p2 i
      simp only [ocOf, dif_pos hi, symPost] at this
      obtain ⟨x1, x2, x3, _⟩ := this
      exact ⟨x1, by simpa using x2, x3⟩)
    (fun i h => by
      have hi : a' ≤ i.val := by simpa using h
      have := p2 i
      simp only [ocOf, dif_neg (by omega : ¬ i.val < a'), symPost] at this
      exact this)
    oOUT.1 oOUT.2 (by rw [v2, v1 rOP (by decide) (by decide)]; rfl) hcu
  have s3 := Exec.step (WExec.exec cap q3)
  have core : Step coreM (coreCost a' Cs carriers L W) (fun _ => 0) (rawIn w n L W) (wenc cap τ3).H (wenc cap τ3).A :=
    ((s0.seq s1).seq s2).seq s3
  obtain ⟨m, hm⟩ := ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0
  have eh : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (DS + 2 + DR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh' : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (wenc cap τ3).H i)
      (fun _ : Fin 1 => 0) : Fin (DS + 2 + DR + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  refine ⟨(wenc cap τ3).A, m, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hm.congr_in eh rfl).congr eh' rfl
  · rw [wenc_A_s, o3]
    simp [symCounts]
  · rw [wenc_A_s, f3 _ (by decide)]
    have a := f2 sIN (fun i j => sSym_ne_low _ _ _ (by decide)) (fun k j => sCar_ne_low _ _ _ (by decide))
    rw [a.1, i1]
    simp [σ0, hw]
  · intro i h
    rw [wenc_A_s, f3 _ (sSym_ne_low _ _ _ sOUT_low)]
    have := p2 i
    simp only [ocOf, dif_pos h, symPost] at this
    exact this.2.2.2
  · intro k h
    rw [wenc_A_s, f3 _ (sCar_ne_low _ _ _ sOUT_low)]
    have := px2 k
    simp only [oxOf, List.getElem?_eq_getElem h, carPost] at this
    exact this.2.2.2
  · intro i h
    rw [wenc_A_s, f3 _ (sSym_ne_low _ _ _ sOUT_low), n2 i (by simp [ocOf, dif_neg (by omega : ¬ i.val < a')]) 3]
    exact (keepS i 3 (by decide)).1
  · intro k h
    rw [wenc_A_s, f3 _ (sCar_ne_low _ _ _ sOUT_low), nx2 k (by simp [oxOf, List.getElem?_eq_none h]) 3]
    exact (keepC k 3 (by decide)).1

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.Data
