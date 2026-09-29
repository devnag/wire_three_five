import Proof.Wire_3_5.Primitive.Writers.ThrDataIface

/-! # PA (d): the THR data stage, part 1: the THR table on the SYM slots' region

P3:3049-3050 ("One-sided scores may be computed directly at a sampled row in polynomial time"): a THR call's
evaluators read the tuple's retained bottoms as ONE table `gatesW h (tupleG Cs)` (`thrTableM a`, `a = 1 … 4`, with
the circuits' framed codes on tapes `0 … a−1`, `1^n` on `4`, `1^L` on `5`). After PA's verified `Data.setupW` (the
request split, mode `true`), the codes sit on the four SYM slots' code streams, so the machine is docked there:

* **`thrMap`** (tapes `0 … 3` ↦ the slots' code streams, `4`/`5` ↦ slot `0`'s `1^n`/`1^L`, the work tapes ↦ the slots'
  free streams, offset `≥ 3`; the table lands on `sSym 0 3`, its count on `sSym 0 5`), `thrMap_inj`;
* `thr_inputs` (the docked machine sees exactly `thrIn (codesOf a Cs) n L` at heads `0`), `dockThr`;
* **`thrT`** (`Block.branchM` on the slots' first cells picks `thrTableM a`), **`thrT_stage`**.

Paper quantity of the main type: the tuple's gate table `gatesW h (tupleG Cs)` and its count `|tupleG Cs|`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.PrimAsm.Data

/-! ## The dock map -/

/-- **The THR table's streams**: tapes `0 … 3` on the slots' code streams, `4`/`5` on slot `0`'s `1^n`/`1^L`, the
work tapes on the slots' free streams (offset `≥ 3`), `1786` per slot. -/
def thrMap (j : Fin 7123) : Fin (DS + 1) :=
  if h : j.val < 4 then sSym ⟨j.val, h⟩ 0
  else if j.val = 4 then sSym 0 1
  else if j.val = 5 then sSym 0 2
  else sSym ⟨(j.val - 6) / 1786, by have := j.isLt; omega⟩ ⟨3 + (j.val - 6) % 1786, by omega⟩

theorem thrMap_val (j : Fin 7123) : (thrMap j).val =
    if j.val < 4 then 14 + 1789 * j.val else if j.val = 4 then 15 else if j.val = 5 then 16
    else 17 + 1789 * ((j.val - 6) / 1786) + (j.val - 6) % 1786 := by
  unfold thrMap
  split_ifs <;> simp [sSym_val] <;> omega

theorem thrMap_inj : Function.Injective thrMap := by
  intro a b h
  have e := congrArg Fin.val h
  rw [thrMap_val, thrMap_val] at e
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  split_ifs at e <;> omega

theorem thrMap_ne (s : Fin (DS + 1)) (hs : ∀ i j, sSym i j ≠ s) (j : Fin 7123) : thrMap j ≠ s := by
  unfold thrMap
  split_ifs <;> exact hs _ _

theorem thrMap_zero : thrMap 0 = sSym 0 0 := Fin.ext (by rw [thrMap_val, sSym_val]; rfl)
theorem thrMap_six : thrMap 6 = sSym 0 3 := Fin.ext (by rw [thrMap_val, sSym_val]; rfl)
theorem thrMap_eight : thrMap 8 = sSym 0 5 := Fin.ext (by rw [thrMap_val, sSym_val]; rfl)

/-! ## The docked machine's inputs -/

section Dock
variable (cap : ℕ)

/-- After the setup, the docked THR machine sees exactly the entry bank, every head at `0`. -/
theorem thr_inputs {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ) (ha1 : 1 ≤ a)
    (σ : WState DS DR)
    (hdone : ∀ i : Fin 4, ∀ h : i.val < a,
      Done σ (symTrip i) (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L)
    (hblank : ∀ i : Fin 4, a ≤ i.val → Blank σ (symTrip i))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0) :
    (fun j => σ.st (thrMap j)) = PrimT.ThrTab.thrIn (PrimT.ThrTab.codesOf a Cs) n L ∧
      (fun j => σ.sh (thrMap j)) = fun _ => 0 := by
  have hlen : (PrimT.ThrTab.codesOf a Cs).length = a := by simp [PrimT.ThrTab.codesOf]
  have d0 := hdone 0 (by show 0 < a; omega)
  obtain ⟨_, _, d3, d4, d5, d6⟩ := d0
  simp only [symTrip] at d3 d4 d5 d6
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · by_cases h4 : j.val < 4
    · have e : thrMap j = sSym ⟨j.val, h4⟩ 0 := by unfold thrMap; rw [dif_pos h4]
      rw [e]
      by_cases hja : j.val < a
      · obtain ⟨c1, -, -, -, -, -⟩ := hdone ⟨j.val, h4⟩ hja
        simp only [symTrip] at c1
        rw [c1]
        unfold PrimT.ThrTab.thrIn
        rw [dif_pos ⟨by rw [hlen]; exact hja, h4⟩]
        simp [PrimT.ThrTab.codesOf]
      · obtain ⟨b1, -, -, -, -, -⟩ := hblank ⟨j.val, h4⟩ (by show a ≤ j.val; omega)
        simp only [symTrip] at b1
        rw [b1]
        unfold PrimT.ThrTab.thrIn
        rw [dif_neg (by rw [hlen]; omega), if_neg (by omega), if_neg (by omega)]
    · by_cases h5 : j.val = 4
      · have e : thrMap j = sSym 0 1 := by unfold thrMap; rw [dif_neg h4, if_pos h5]
        rw [e, d3]
        unfold PrimT.ThrTab.thrIn
        rw [dif_neg (by omega), if_pos h5]
      · by_cases h6 : j.val = 5
        · have e : thrMap j = sSym 0 2 := by unfold thrMap; rw [dif_neg h4, if_neg h5, if_pos h6]
          rw [e, d5]
          unfold PrimT.ThrTab.thrIn
          rw [dif_neg (by omega), if_neg h5, if_pos h6]
        · have e : thrMap j = sSym ⟨(j.val - 6) / 1786, by have := j.isLt; omega⟩
              ⟨3 + (j.val - 6) % 1786, by omega⟩ := by
            unfold thrMap; rw [dif_neg h4, if_neg h5, if_neg h6]
          rw [e, (hb _ _ (by simp)).1, PrimT.ThrTab.thrIn_blank _ _ _ _ (by omega)]
  · by_cases h4 : j.val < 4
    · have e : thrMap j = sSym ⟨j.val, h4⟩ 0 := by unfold thrMap; rw [dif_pos h4]
      rw [e]
      by_cases hja : j.val < a
      · obtain ⟨-, c2, -, -, -, -⟩ := hdone ⟨j.val, h4⟩ hja
        simpa only [symTrip] using c2
      · obtain ⟨-, b2, -, -, -, -⟩ := hblank ⟨j.val, h4⟩ (by show a ≤ j.val; omega)
        simpa only [symTrip] using b2
    · by_cases h5 : j.val = 4
      · have e : thrMap j = sSym 0 1 := by unfold thrMap; rw [dif_neg h4, if_pos h5]
        rw [e, d4]
      · by_cases h6 : j.val = 5
        · have e : thrMap j = sSym 0 2 := by unfold thrMap; rw [dif_neg h4, if_neg h5, if_pos h6]
          rw [e, d6]
        · have e : thrMap j = sSym ⟨(j.val - 6) / 1786, by have := j.isLt; omega⟩
              ⟨3 + (j.val - 6) % 1786, by omega⟩ := by
            unfold thrMap; rw [dif_neg h4, if_neg h5, if_neg h6]
          rw [e, (hb _ _ (by simp)).2]

/-- The THR machine docked on the slots' region. -/
noncomputable def dockT {s : ℕ} (M : Machine 7123 s) :=
  RecoveryFocus.machine (fun j => sTape (nr := DR) (thrMap j)) M

/-- The THR table's exit facts (the collection reads slot `0`'s first cell and the count on its stream `5`). -/
def ThrPost {n a : ℕ} (σ : WState DS DR) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) : Prop :=
  readTapeBit (σ.st (sSym 0 0)) (σ.sh (sSym 0 0)) = true ∧
    σ.st (sSym 0 5) = List.replicate (PrimT.ThrTab.tupleG Cs).length true ∧ σ.sh (sSym 0 5) = 0 ∧
    σ.st (sSym 0 3) = FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)

/-- **The docked THR table** from the run. -/
theorem dockThr {s : ℕ} (M : Machine 7123 s) (c : ℕ) {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n)
    (L : ℕ) (ha1 : 1 ≤ a) (σ : WState DS DR)
    (hdone : ∀ i : Fin 4, ∀ h : i.val < a,
      Done σ (symTrip i) (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L)
    (hblank : ∀ i : Fin 4, a ≤ i.val → Blank σ (symTrip i))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0)
    (hT : ∃ tout : Fin 7123 → List Bool,
      Step M c (fun _ => 0) (PrimT.ThrTab.thrIn (PrimT.ThrTab.codesOf a Cs) n L) (fun _ => 0) tout ∧
      (∀ i : Fin 7123, i.val < 4 → tout i = PrimT.ThrTab.thrIn (PrimT.ThrTab.codesOf a Cs) n L i) ∧
      tout 4 = List.replicate n true ∧ tout 5 = List.replicate L true ∧
      tout 6 = FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs) ∧
      tout 7 = List.replicate (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) true ∧
      tout 8 = List.replicate (PrimT.ThrTab.tupleG Cs).length true) :
    ∃ σ' : WState DS DR, Step (dockT M) c (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      ThrPost σ' Cs ∧ (∀ s, (∀ i j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell := by
  obtain ⟨tout, hs, t03, _, _, t6, _, t8⟩ := hT
  obtain ⟨hin, hh⟩ := thr_inputs Cs L ha1 σ hdone hblank hb
  have hs' : Step M c (fun j => σ.sh (thrMap j)) (fun j => σ.st (thrMap j)) (fun _ => 0) tout := by
    rw [hh, hin]; exact hs
  have d := dockS cap thrMap thrMap_inj σ hs'
  have hlen : (PrimT.ThrTab.codesOf a Cs).length = a := by simp [PrimT.ThrTab.codesOf]
  refine ⟨updS thrMap σ (fun _ => 0) tout, d, ⟨?_, ?_, ?_, ?_⟩, fun s hs => ⟨updS_st_other _ _ _ _ s (thrMap_ne s hs),
    updS_sh_other _ _ _ _ s (thrMap_ne s hs)⟩, rfl, rfl⟩
  · rw [← thrMap_zero, updS_st_slot _ thrMap_inj, updS_sh_slot _ thrMap_inj, t03 0 (by decide)]
    unfold PrimT.ThrTab.thrIn
    rw [dif_pos ⟨by rw [hlen]; show 0 < a; omega, by decide⟩]
    exact frame_natWord_head _
  · rw [← thrMap_eight, updS_st_slot _ thrMap_inj, t8]
  · rw [← thrMap_eight, updS_sh_slot _ thrMap_inj]
  · rw [← thrMap_six, updS_st_slot _ thrMap_inj, t6]

/-! ## The stage -/

/-- **The THR table stage**: `thrTableM a` for the tuple size `a` (the highest filled slot), docked. -/
noncomputable def thrT :=
  Block.branchM (sTape (nr := DR) (sSym 3 0)) (dockT PrimT.ThrTab.thrTableM4)
    (Block.branchM (sTape (nr := DR) (sSym 2 0)) (dockT PrimT.ThrTab.thrTableM3)
      (Block.branchM (sTape (nr := DR) (sSym 1 0)) (dockT PrimT.ThrTab.thrTableM2) (dockT PrimT.ThrTab.thrTableM1)))

/-- The THR table stage's cost. -/
noncomputable def thrCost {n : ℕ} : (a : ℕ) → (Fin a → NormalizedThresholdThresholdCircuit n) → ℕ → ℕ
  | 1, Cs, L => PrimT.ThrTab.thrTableCost1 Cs L + 6
  | 2, Cs, L => PrimT.ThrTab.thrTableCost2 Cs L + 6
  | 3, Cs, L => PrimT.ThrTab.thrTableCost3 Cs L + 4
  | 4, Cs, L => PrimT.ThrTab.thrTableCost4 Cs L + 2
  | _, _, _ => 0

theorem bit_blank (σ : WState DS DR) (i : Fin 4) (hb : Blank σ (symTrip i)) :
    readTapeBit ((wenc cap σ).A (sTape (sSym i 0))) ((wenc cap σ).H (sTape (sSym i 0))) = false := by
  obtain ⟨b1, b2, _, _, _, _⟩ := hb
  simp only [symTrip] at b1 b2
  rw [wenc_A_s, wenc_H_s, b1]
  rfl

theorem bit_done {n : ℕ} (σ : WState DS DR) (i : Fin 4) (x L : ℕ) (hd : Done σ (symTrip i) x n L) :
    readTapeBit ((wenc cap σ).A (sTape (sSym i 0))) ((wenc cap σ).H (sTape (sSym i 0))) = true := by
  obtain ⟨d1, d2, _, _, _, _⟩ := hd
  simp only [symTrip] at d1 d2
  rw [wenc_A_s, wenc_H_s, d1, d2]
  exact frame_natWord_head _

/-- **The THR table stage**: from the setup's slots (the first `a` filled with the circuits' codes, the rest blank,
every free slot stream blank), the tuple's table on `sSym 0 3` and its count on `sSym 0 5`; nothing outside the SYM
slots' region changes. -/
theorem thrT_stage {n a : ℕ} (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (L : ℕ) (ha1 : 1 ≤ a) (ha : a ≤ 4)
    (hL : ∀ j, (Cs j).descriptionBits ≤ L) (h2 : 2 ≤ n + L) (σ : WState DS DR)
    (hdone : ∀ i : Fin 4, ∀ h : i.val < a,
      Done σ (symTrip i) (encodeNormalizedThresholdThresholdCircuit (Cs ⟨i.val, h⟩)) n L)
    (hblank : ∀ i : Fin 4, a ≤ i.val → Blank σ (symTrip i))
    (hb : ∀ i (j : Fin 1789), 3 ≤ j.val → σ.st (sSym i j) = [] ∧ σ.sh (sSym i j) = 0) :
    ∃ σ' : WState DS DR, Step thrT (thrCost a Cs L) (wenc cap σ).H (wenc cap σ).A (wenc cap σ').H (wenc cap σ').A ∧
      ThrPost σ' Cs ∧ (∀ s, (∀ i j, sSym i j ≠ s) → σ'.st s = σ.st s ∧ σ'.sh s = σ.sh s) ∧ σ'.val = σ.val ∧
      σ'.cell = σ.cell := by
  obtain rfl | rfl | rfl | rfl : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
  · obtain ⟨σ', d, p, f, v, c⟩ := dockThr cap PrimT.ThrTab.thrTableM1 _ Cs L ha1 σ hdone hblank hb
      (PrimT.ThrTab.thrTable1_step Cs L hL h2)
    refine ⟨σ', ?_, p, f, v, c⟩
    exact Block.branch_false _ _ (Block.branch_false _ _ (Block.branch_false _ _ d
      (bit_blank cap σ 1 (hblank 1 (by decide)))) (bit_blank cap σ 2 (hblank 2 (by decide))))
      (bit_blank cap σ 3 (hblank 3 (by decide)))
  · obtain ⟨σ', d, p, f, v, c⟩ := dockThr cap PrimT.ThrTab.thrTableM2 _ Cs L ha1 σ hdone hblank hb
      (PrimT.ThrTab.thrTable2_step Cs L hL h2)
    refine ⟨σ', ?_, p, f, v, c⟩
    exact Block.branch_false _ _ (Block.branch_false _ _ (Block.branch_true _ _ d
      (bit_done cap σ 1 _ L (hdone 1 (by decide)))) (bit_blank cap σ 2 (hblank 2 (by decide))))
      (bit_blank cap σ 3 (hblank 3 (by decide)))
  · obtain ⟨σ', d, p, f, v, c⟩ := dockThr cap PrimT.ThrTab.thrTableM3 _ Cs L ha1 σ hdone hblank hb
      (PrimT.ThrTab.thrTable3_step Cs L hL h2)
    refine ⟨σ', ?_, p, f, v, c⟩
    exact Block.branch_false _ _ (Block.branch_true _ _ d (bit_done cap σ 2 _ L (hdone 2 (by decide))))
      (bit_blank cap σ 3 (hblank 3 (by decide)))
  · obtain ⟨σ', d, p, f, v, c⟩ := dockThr cap PrimT.ThrTab.thrTableM4 _ Cs L ha1 σ hdone hblank hb
      (PrimT.ThrTab.thrTable4_step Cs L hL h2)
    refine ⟨σ', ?_, p, f, v, c⟩
    exact Block.branch_true _ _ d (bit_done cap σ 3 _ L (hdone 3 (by decide)))

end Dock

end NearCubicWires.WireExponent3_5.PrimAsm.ThrData
