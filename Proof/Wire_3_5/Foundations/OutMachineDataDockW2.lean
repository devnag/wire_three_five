import Proof.Wire_3_5.Foundations.OutMachineDataDockW

/-! # `dataDock_stepW'` (the request for SWt): the unfilled slots' scan tapes blank

`dataDock_stepW` exports every FILLED SYM slot's scan word; SWt branches on the scan tape's first cell, so it
also needs the unfilled slots' scan tapes blank (an empty slot's stage is the identity, `symT_stage2W`'s
`oc = none → σ' = σ`, and the raw inputs are blank there):

* **`data_step_blankW2`**, **`dataDock_stepW'`**: `…W` plus `∀ i, a' ≤ i.val → tout (… (sSym i (scanSl 0))) = []`.

Paper quantity of the main type: the SYM circuits' top vectors and bottom counts (P3:3049-3050). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.DataW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.SymTab
open NearCubicWires.WireExponent3_5.UnionMachine.DataDock
open NearCubicWires.RepairRepresentation (natWord)

section RunW2
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The per-call data stage with the empty slots** (SYM, `data_step` plus the unfilled slots' table streams blank): from `frame w` (`w` the request's word shape, circuits' and carriers' codes),
`1^n`, `1^L`, `1^W`, in `2·coreCost + 2` steps, every head back at `0`: the output stream holds
`dataWord (symCounts …)`, the request stays, and each filled slot holds the table. -/
theorem data_step_blankW2 (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
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
      (∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = []) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (sTape (sSym i (scanSl 0))) = scanWord (Cs ⟨i.val, h⟩)) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (sTape (sSym i (scanSl 0))) = []) := by
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
  obtain ⟨σ2, s2, p2, px2, f2, v2, c2, n2, nx2, q2⟩ := tabs_step2W L cap (ocOf a' Cs) (oxOf carriers) τ1
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
  refine ⟨(wenc cap τ3).A, m, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i h
    rw [wenc_A_s, f3 _ (sSym_ne_low _ _ _ sOUT_low)]
    exact q2 i (Cs ⟨i.val, h⟩) (by simp [ocOf, dif_pos h])
  · intro i h
    rw [wenc_A_s, f3 _ (sSym_ne_low _ _ _ sOUT_low),
      n2 i (by simp [ocOf, dif_neg (by omega : ¬ i.val < a')]) (scanSl 0)]
    exact (keepS i (scanSl 0) (by decide)).1

end RunW2

section DockW2
variable {n : ℕ} (a' : ℕ) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **`dataDock` with the scan tapes, both kinds**: `dataDock_stepW` plus every unfilled SYM slot's scan tape blank. -/
theorem dataDock_stepW' {ns nr : ℕ} (cap : ℕ) (tmap : Fin DT → Fin (ns + 1)) (hinj : Function.Injective tmap)
    (σ : WState ns nr) (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ n + L)
    (hcN : natBitLength n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ symCodes a' Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList (carriers.map (·.length))).length +
      2 * (unaryList (List.ofFn fun i => (Stars.symGates (Cs i)).length)).length + 2 ≤ 2 * W + 2)
    (hin : ∀ j, σ.st (tmap j) = dataIn (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W j)
    (hh : ∀ j, σ.sh (tmap j) = 0) :
    ∃ tout : Fin DT → List Bool,
      Step (dataDockM (nr := nr) tmap) (2 * coreCost a' Cs carriers L W + 2) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (DockW.updS tmap σ (fun _ => 0) tout)).H (wenc cap (DockW.updS tmap σ (fun _ => 0) tout)).A ∧
      tout iOUT = dataWord (symCounts a' Cs carriers) ∧
      tout iIN = RepairOrdinary.frame (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (iSym i) =
        FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (iCar k) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      (∀ j, (tout j).length ≤ dataB (reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl) n L W
        Cs carriers) ∧
      (∀ i : Fin 4, ∀ h : i.val < a', tout (iOf (sSym i (scanSl 0))) = scanWord (Cs ⟨i.val, h⟩)) ∧
      (∀ i : Fin 4, a' ≤ i.val → tout (iOf (sSym i (scanSl 0))) = []) := by
  obtain ⟨tout0, m, hs, ho, hi, hS, hC, -, -, hW, hE⟩ := data_step_blankW2 a' Cs carriers tl L W ha hk hL hLX h2 hcN
    hcA hcK hcx hcy hcu
  obtain ⟨w, hwd⟩ : ∃ v, v = reqW n false (symCodes a' Cs) (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hs hi hin ⊢
  have e1 : (fun j => σ.sh (tmap j)) = fun _ => 0 := funext hh
  have e2 : (fun j => σ.st (tmap j)) = dataIn w n L W := funext hin
  have hs' : Step dataM (2 * coreCost a' Cs carriers L W + 2) (fun j => σ.sh (tmap j)) (fun j => σ.st (tmap j))
      (fun _ => 0) (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false)) := by
    rw [e1, e2]; exact hs
  refine ⟨Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m false), DockW.dockS cap tmap hinj σ hs', ?_, ?_,
    fun i h => ?_, fun k h => ?_, ?_, fun i h => ?_, fun i h => ?_⟩
  · unfold iOUT iOf; beta_reduce; rw [Fin.addCases_left]; exact ho
  · unfold iIN iOf; beta_reduce; rw [Fin.addCases_left]; exact hi
  · unfold iSym iOf; beta_reduce; rw [Fin.addCases_left]; exact hS i h
  · unfold iCar iOf; beta_reduce; rw [Fin.addCases_left]; exact hC k h
  · intro j
    have hl := Shell.Step.len hs j (2 * w.length + n + L + W + 1) (Nat.zero_le _)
      (by have := dataIn_len w n L W j; unfold dataIn at this; exact this)
    unfold dataB
    beta_reduce
    omega
  · unfold iOf; beta_reduce; rw [Fin.addCases_left]; exact hW i h
  · unfold iOf; beta_reduce; rw [Fin.addCases_left]; exact hE i h

end DockW2

end NearCubicWires.WireExponent3_5.FinalPass.Out.DataW
