import Proof.Wire_3_5.UnionMachine.DataDock
import Proof.Wire_3_5.Foundations.SwPartsTabSymW

/-! # `dataDock` with every SYM slot's scan tape (build once)

PA's per-call data stage runs the SYM table machine on each filled slot; the machine's scan stage keeps its decoded
input on the tape `scanSl 0` (E's `TabSymW.symTable_stepW`): the circuit's native word
`natWord C.bottomCount ++ (frame (List.ofFn C.top) ++ tabSeg (symGates C))` (**`scanWord C`**). The later stages
keep every other slot's streams, so the word survives to the stage's exit. Threaded through PA's and the chain:

* **`symT_onW`**, **`symT_stageW`**, **`symT_stage2W`** (one slot, the scan tape exposed; `scanPost`, `scanPost_tr`);
* **`tabs_step2W`** (the six table stages), **`data_step_blankW`** (the per-call data stage);
* **`dataDock_stepW`**: `dataDock_step` plus `tout (iOf (sSym i (scanSl 0))) = scanWord (Cs i)` for every
  filled slot.

Paper quantity of the main type: the SYM circuits' top vectors and bottom counts (the SYM call's slices,
P3:3049-3050). -/

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

open PCJd4d1d9d7d1fa4313_Production in
/-- **A SYM circuit's scan word**: the bottom count, the framed top table, the gate segment. -/
noncomputable def scanWord {n : ℕ} (C : NormalizedSymmetricThresholdCircuit n) : List Bool :=
  natWord C.bottomCount ++ (frame (List.ofFn C.top) ++ tabSeg (Stars.symGates C))

section Stage
variable (cap : ℕ)

/-- **A filled SYM slot**, the scan tape exposed. -/
theorem symT_onW {n : ℕ} (i : Fin 4) (C : NormalizedSymmetricThresholdCircuit n) (L : ℕ) (hL : C.descriptionBits ≤ L)
    (h2 : 2 ≤ n + L) (σ : WState DS DR) (hd : Done σ (symTrip i) (encodeNormalizedSymmetricThresholdCircuit C) n L)
    (hb : ∀ j : Fin 1789, 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0) :
    ∃ tout : Fin 1789 → List Bool, Step (symT i) (symTableCost C L + 2) (wenc cap σ).H (wenc cap σ).A
      (wenc cap (updS (sSym i) σ (fun _ => 0) tout)).H (wenc cap (updS (sSym i) σ (fun _ => 0) tout)).A ∧
      tout 0 = RepairOrdinary.frame (natWord (encodeNormalizedSymmetricThresholdCircuit C)) ∧
      tout 3 = FinalPass.Corner.gatesW (tabH (Stars.symGates C)) (Stars.symGates C) ∧
      tout 5 = List.replicate (Stars.symGates C).length true ∧ tout (scanSl 0) = scanWord C := by
  obtain ⟨tout, hs, t0, _, _, t3, _, t5, tS⟩ := FinalPass.SymParts.TabSymW.symTable_stepW C L hL h2
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  simp only [symTrip] at d1 d2 d3 d4 d5 d6
  have hin : (fun j => σ.st (sSym i j)) = symIn (encodeNormalizedSymmetricThresholdCircuit C) n L := by
    funext j
    unfold symIn
    by_cases j0 : j.val = 0
    · rw [if_pos j0, show j = 0 from Fin.ext j0, d1]
    · by_cases j1 : j.val = 1
      · rw [if_neg j0, if_pos j1, show j = 1 from Fin.ext j1, d3]
      · by_cases j2 : j.val = 2
        · rw [if_neg j0, if_neg j1, if_pos j2, show j = 2 from Fin.ext j2, d5]
        · rw [if_neg j0, if_neg j1, if_neg j2]
          exact (hb j (by omega)).1
  have hh : (fun j => σ.sh (sSym i j)) = fun _ => 0 := by
    funext j
    by_cases j0 : j.val = 0
    · rw [show j = 0 from Fin.ext j0, d2]
    · by_cases j1 : j.val = 1
      · rw [show j = 1 from Fin.ext j1, d4]
      · by_cases j2 : j.val = 2
        · rw [show j = 2 from Fin.ext j2, d6]
        · exact (hb j (by omega)).2
  have hs' : Step symTableM (symTableCost C L) (fun j => σ.sh (sSym i j)) (fun j => σ.st (sSym i j)) (fun _ => 0)
      tout := by
    rw [hh, hin]
    exact hs
  have d := dockS cap (sSym i) (sSym_inj i) σ hs'
  refine ⟨tout, Block.branch_true _ _ d ?_, t0, t3, t5, tS⟩
  rw [wenc_A_s, wenc_H_s, d1, d2]
  exact frame_natWord_head _

/-- The scan tape's exit fact of a SYM slot (vacuous for an empty slot). -/
def scanPost {n : ℕ} (σ : WState DS DR) (i : Fin 4) (oc : Option (NormalizedSymmetricThresholdCircuit n)) : Prop :=
  ∀ C, oc = some C → σ.st (sSym i (scanSl 0)) = scanWord C

theorem scanPost_tr {n : ℕ} {σ σ' : WState DS DR} {i : Fin 4} (h : SameSym σ σ' i)
    (oc : Option (NormalizedSymmetricThresholdCircuit n)) : scanPost σ i oc → scanPost σ' i oc :=
  fun p C hC => (h (scanSl 0)).1.trans (p C hC)

variable {n : ℕ} (L : ℕ)

/-- **One SYM slot's stage**, the scan tape exposed. -/
theorem symT_stage2W (i : Fin 4) (oc : Option (NormalizedSymmetricThresholdCircuit n)) (σ : WState DS DR)
    (hpre : symPre L σ i oc) (hb : ∀ j : Fin 1789, 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hL : ∀ C, oc = some C → C.descriptionBits ≤ L) (h2 : 2 ≤ n + L) :
    ∃ σ' : WState DS DR, Step (symT i) (symCostO L oc) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      symPost σ' i oc ∧ (∀ s, (∀ j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell ∧ (oc = none → σ' = σ) ∧ scanPost σ' i oc := by
  cases oc with
  | none =>
    refine ⟨σ, symT_off cap i σ hpre, ?_, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, fun _ => rfl, fun C hC => by cases hC⟩
    obtain ⟨b1, b2, _, _, _, _⟩ := hpre
    simp only [symTrip] at b1 b2
    show readTapeBit (σ.st (sSym i 0)) (σ.sh (sSym i 0)) = false
    rw [b1]
    rfl
  | some C =>
    obtain ⟨tout, hs, t0, t3, t5, tS⟩ := symT_onW cap i C L (hL C rfl) h2 σ hpre hb
    refine ⟨updS (sSym i) σ (fun _ => 0) tout, hs, ?_, fun s hs' => ⟨updS_st_other _ _ _ _ s hs',
      updS_sh_other _ _ _ _ s hs'⟩, rfl, rfl, fun h => absurd h (Option.some_ne_none C), fun C' hC' => ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [updS_st_slot _ (sSym_inj i), updS_sh_slot _ (sSym_inj i), t0]
        exact frame_natWord_head _
      · rw [updS_st_slot _ (sSym_inj i), t5]
      · rw [updS_sh_slot _ (sSym_inj i)]
      · rw [updS_st_slot _ (sSym_inj i), t3]
    · cases hC'
      rw [updS_st_slot _ (sSym_inj i), tS]

end Stage

section Chain
variable {n : ℕ} (L : ℕ) (cap : ℕ)

/-- **The six table stages**, `tabs_step2` plus every filled slot's scan tape. -/
theorem tabs_step2W (oc : Fin 4 → Option (NormalizedSymmetricThresholdCircuit n)) (ox : Fin 2 → Option (Stars.Carrier n))
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
      (∀ k, ox k = none → ∀ j, σ'.st (sCar k j) = σ.st (sCar k j)) ∧ (∀ i, scanPost σ' i (oc i)) := by
  obtain ⟨σ1, s1, p1, f1, v1, c1, n1, q1⟩ := symT_stage2W cap L 0 (oc 0) σ (hpre 0) (hb 0) (hL 0) h2
  obtain ⟨σ2, s2, p2, f2, v2, c2, n2, q2⟩ := symT_stage2W cap L 1 (oc 1) σ1
    (symPre_tr L (sym_keeps_sym f1 1 (by decide)) _ (hpre 1)) (blankSym_tr (sym_keeps_sym f1 1 (by decide)) (hb 1))
    (hL 1) h2
  obtain ⟨σ3, s3, p3, f3, v3, c3, n3, q3⟩ := symT_stage2W cap L 2 (oc 2) σ2
    (symPre_tr L ((sym_keeps_sym f1 2 (by decide)).trans (sym_keeps_sym f2 2 (by decide))) _ (hpre 2))
    (blankSym_tr ((sym_keeps_sym f1 2 (by decide)).trans (sym_keeps_sym f2 2 (by decide))) (hb 2)) (hL 2) h2
  obtain ⟨σ4, s4, p4, f4, v4, c4, n4, q4⟩ := symT_stage2W cap L 3 (oc 3) σ3
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
  refine ⟨σ6, ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · intro i
    rcases fin4_cases i with rfl | rfl | rfl | rfl
    · exact scanPost_tr (((sym_keeps_sym f2 0 (by decide)).trans (sym_keeps_sym f3 0 (by decide))).trans
        ((sym_keeps_sym f4 0 (by decide)).trans (t56 0))) _ q1
    · exact scanPost_tr ((sym_keeps_sym f3 1 (by decide)).trans ((sym_keeps_sym f4 1 (by decide)).trans (t56 1))) _
        q2
    · exact scanPost_tr ((sym_keeps_sym f4 2 (by decide)).trans (t56 2)) _ q3
    · exact scanPost_tr (t56 3) _ q4

end Chain

section RunW

end RunW

section DockW

end DockW

end NearCubicWires.WireExponent3_5.FinalPass.Out.DataW
