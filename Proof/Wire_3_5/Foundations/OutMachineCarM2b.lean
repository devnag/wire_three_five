import Proof.Wire_3_5.Foundations.OutMachineCarM2

/-! # The output machine carrier phase, part 3b: the carrier tables with the slots' code streams

`CarM2.m2_spec` with one more exported fact: after the stage each carrier slot's code stream `sCar k 0` holds
`frame (natWord code_k)` for a named carrier and is blank past the carriers. The count `1^{|carriers|}` (the carrier
phase's fifth word) is read off these first cells (a framed `natWord` starts with `1`). Proofs as `CarM2`'s, with
`carTable_step` output `0` kept (`carStage2`, **`m2_spec2`**).

Paper quantity of the main type: the carriers' mask tables and the named carriers' count (P3:3049-3050, 3071-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarM2b
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarM2
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- **One carrier slot**: from a filled (`Done`) or blank slot with blank streams `3 …`, the table and count. -/
theorem carStage2 (cap : ℕ) (k : Fin 2) {n : ℕ} (carriers : List (Stars.Carrier n)) (L : ℕ)
    (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ n + L) (σ : WState DS DR)
    (hon : ∀ h : k.val < carriers.length, Done σ (carTrip k) (carriers.get ⟨k.val, h⟩).code n L)
    (hoff : carriers.length ≤ k.val → Blank σ (carTrip k))
    (hb : ∀ j : Fin 1357, 3 ≤ j.val → σ.st (sCar k j) = [] ∧ σ.sh (sCar k j) = 0) :
    ∃ (τ : WState DS DR) (m : ℕ), Step (carT k) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ carCostB carriers L k.val ∧ τ.st (sCar k 3) = Seams.carTab carriers k.val ∧
      τ.st (sCar k 5) = List.replicate (carCnt carriers k.val) true ∧
      (∀ s, (∀ j, s ≠ sCar k j) → τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧
      (∀ j, τ.sh (sCar k j) = 0) ∧ τ.val = σ.val ∧ τ.cell = σ.cell ∧
      τ.st (sCar k 0) = (if h : k.val < carriers.length then
        frame (RepairRepresentation.natWord (carriers.get ⟨k.val, h⟩).code) else []) := by
  by_cases h : k.val < carriers.length
  · set X := carriers.get ⟨k.val, h⟩ with hX
    obtain ⟨tout, hs, t0, t3, t5⟩ := carT_on cap k X L (hLX X (List.get_mem _ _)) h2 σ (hon h) hb
    refine ⟨_, _, hs, by unfold carCostB; rw [dif_pos h], ?_, ?_, fun s hs' => ⟨updS_st_off k σ tout s hs',
      updS_sh_off k σ tout s hs'⟩, fun j => updS_sh_on k σ tout j, rfl, rfl, ?_⟩
    · rw [updS_st_on, t3]; unfold Seams.carTab; rw [dif_pos h]
    · rw [updS_st_on, t5]; unfold carCnt; rw [dif_pos h]
    · rw [updS_st_on, t0, dif_pos h]
  · have hbl := hoff (by omega)
    have hs := carT_off cap k σ hbl
    refine ⟨σ, 2, hs, by unfold carCostB; rw [dif_neg h], ?_, ?_, fun _ _ => ⟨rfl, rfl⟩, fun j => ?_, rfl, rfl,
      by rw [dif_neg h]; exact hbl.1⟩
    · rw [(hb 3 (by decide)).1]; unfold Seams.carTab; rw [dif_neg h]
    · rw [(hb 5 (by decide)).1]; unfold carCnt; rw [dif_neg h]; rfl
    · by_cases hj : 3 ≤ j.val
      · exact (hb j hj).2
      · obtain ⟨_, b1, _, b2, _, b3⟩ := hbl
        simp only [carTrip] at b1 b2 b3
        have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
        rcases this with e | e | e
        · rw [show j = 0 from Fin.ext e]; exact b1
        · rw [show j = 1 from Fin.ext e]; exact b2
        · rw [show j = 2 from Fin.ext e]; exact b3

/-- **The carrier tables' stage**: from the request, `1^n`, `1^L`, blank slots, every head and register `0`. -/
theorem m2_spec2 (cap n L : ℕ) (mb : Bool) (codes : List ℕ) (carriers : List (Stars.Carrier n)) (tl : List Bool)
    (σ : WState DS DR) (ha : codes.length ≤ 4) (hk : carriers.length ≤ 2)
    (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ n + L)
    (hIN : σ.st sIN = frame (reqW n mb codes (carriers.map Stars.Carrier.code) tl)) (hsh : ∀ i, σ.sh i = 0)
    (hNT : σ.st sNT = List.replicate n true) (hLT : σ.st sLT = List.replicate L true)
    (hbs : ∀ i, Blank σ (symTrip i)) (hbc : ∀ k : Fin 2, ∀ j : Fin 1357, σ.st (sCar k j) = [])
    (hv : ∀ r, σ.val r = 0)
    (hcapN : natBitLength n + 1 ≤ cap) (hcapA : 2 ^ (natBitLength codes.length + 1) ≤ cap)
    (hcapK : 2 ^ (natBitLength carriers.length + 1) ≤ cap)
    (hcx : ∀ x ∈ codes, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ cap)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ cap)
    (hc4 : 4 ≤ cap) :
    ∃ (τ : WState DS DR) (m : ℕ), Step m2M m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      m ≤ m2Bnd cap n L codes carriers ∧
      (∀ k : Fin 2, τ.st (sCar k 3) = Seams.carTab carriers k.val ∧
        τ.st (sCar k 5) = List.replicate (carCnt carriers k.val) true) ∧
      (∀ i, i ≠ sIN → τ.sh i = 0) ∧ (∀ r, τ.val r = 0) ∧ τ.st sIN = σ.st sIN ∧ τ.st s6 = σ.st s6 ∧
      τ.cell = σ.cell ∧ (∀ k : Fin 2, τ.st (sCar k 0) = (if h : k.val < carriers.length then
        frame (RepairRepresentation.natWord (carriers.get ⟨k.val, h⟩).code) else [])) := by
  obtain ⟨τ1, e1, ds1, bs1, dc1, bc1, keep1, in1, v1, c1⟩ := setup_spec cap n L mb codes
    (carriers.map Stars.Carrier.code) tl σ ha (by simpa using hk) hIN (hsh _) hNT (hsh _) hLT (hsh _) hbs
    (fun k => ⟨hbc k 0, hsh _, hbc k 1, hsh _, hbc k 2, hsh _⟩) (hv _) (hv _) (hv _) (hv _) (hv _) (hv _) (hv _)
    (hv _) hcapN hcapA (by simpa using hcapK) hcx hcy hc4
  have hle := FinalPass.S5T.WExec.val_le cap e1 (fun r => by rw [hv]; omega)
  have x1 := wclear_spec cap rA (τ1.val rA) τ1 rfl (hle _)
  have x2 := wclear_spec cap rK (τ1.val rK) (τ1.setv rA 0) (by simp [Function.update_of_ne (show rK ≠ rA by decide)])
    (by simp [Function.update_of_ne (show rK ≠ rA by decide)]; exact hle _)
  set τ2 := (τ1.setv rA 0).setv rK 0 with hτ2
  have sw := Exec.step (WExec.exec cap (WExec.seq e1 (WExec.seq x1 x2)))
  have hb0 : ∀ k : Fin 2, ∀ j : Fin 1357, 3 ≤ j.val → τ2.st (sCar k j) = [] ∧ τ2.sh (sCar k j) = 0 := by
    intro k j hj
    obtain ⟨a, b, c⟩ := sCar_hi_off k j hj
    obtain ⟨e1', e2'⟩ := keep1 _ a b c
    exact ⟨e1'.trans (hbc k j), e2'.trans (hsh _)⟩
  have hon : ∀ k : Fin 2, ∀ h : k.val < carriers.length, Done τ2 (carTrip k) (carriers.get ⟨k.val, h⟩).code n L := by
    intro k h
    have := dc1 k (by simpa using h)
    show Done τ1 (carTrip k) _ n L
    simpa using this
  have hoff : ∀ k : Fin 2, carriers.length ≤ k.val → Blank τ2 (carTrip k) := fun k h => bc1 k (by simpa using h)
  obtain ⟨τ3, m3, s3, b3, o3, c3, k3, h3, v3, cl3, z3⟩ := carStage2 cap 0 carriers L hLX h2 τ2 (hon 0) (hoff 0) (hb0 0)
  have hb1 : ∀ j : Fin 1357, 3 ≤ j.val → τ3.st (sCar 1 j) = [] ∧ τ3.sh (sCar 1 j) = 0 := by
    intro j hj
    rw [(k3 _ (fun j' => off01 j j')).1, (k3 _ (fun j' => off01 j j')).2]
    exact hb0 1 j hj
  obtain ⟨τ4, m4, s4, b4, o4, c4, k4, h4, v4, cl4, z4⟩ := carStage2 cap 1 carriers L hLX h2 τ3
    (fun h => (slot_tr τ2 τ3 k3 (carriers.get ⟨1, h⟩).code n L).1 (hon 1 h))
    (fun h => (slot_tr τ2 τ3 k3 0 n L).2 (hoff 1 h)) hb1
  have kk : ∀ s, (∀ j, s ≠ sCar 0 j) → (∀ j, s ≠ sCar 1 j) → τ4.st s = τ2.st s ∧ τ4.sh s = τ2.sh s := by
    intro s h0 h1
    exact ⟨(k4 s h1).1.trans (k3 s h0).1, (k4 s h1).2.trans (k3 s h0).2⟩
  refine ⟨τ4, _, Step.seq sw (Step.seq s3 s4), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold m2Bnd
    have := hle rA
    have := hle rK
    have b3' : m3 ≤ carCostB carriers L 0 := b3
    have b4' : m4 ≤ carCostB carriers L 1 := b4
    omega
  · intro k
    match k with
    | ⟨0, _⟩ => exact ⟨((k4 _ (fun j e => off01 j 3 e.symm)).1).trans o3,
        ((k4 _ (fun j e => off01 j 5 e.symm)).1).trans c3⟩
    | ⟨1, _⟩ => exact ⟨o4, c4⟩
  · intro i hi
    by_cases h1 : ∃ j, i = sCar 1 j
    · obtain ⟨j, rfl⟩ := h1; exact h4 j
    · simp only [not_exists] at h1
      by_cases h0 : ∃ j, i = sCar 0 j
      · obtain ⟨j, rfl⟩ := h0; rw [(k4 _ (fun j' => h1 j')).2]; exact h3 j
      · simp only [not_exists] at h0
        rw [(kk i h0 h1).2]
        by_cases hsym : ∃ i', tmem i (symTrip i')
        · obtain ⟨i', hi'⟩ := hsym
          by_cases hc : i'.val < codes.length
          · exact trip_sh τ2 _ _ n L (Or.inl (ds1 i' hc)) i hi'
          · exact trip_sh τ2 _ 0 n L (Or.inr (bs1 i' (by omega))) i hi'
        · simp only [not_exists] at hsym
          have hcar : ∀ k, ¬ tmem i (carTrip k) := by
            intro k hk'
            have hj : ∃ j, i = sCar k j := by
              simp only [carTrip, tmem] at hk'
              rcases hk' with e | e | e <;> exact ⟨_, e⟩
            obtain ⟨j, hj⟩ := hj
            match k with
            | ⟨0, _⟩ => exact h0 j hj
            | ⟨1, _⟩ => exact h1 j hj
          show τ1.sh i = 0
          rw [(keep1 i hsym hcar hi).2]; exact hsh i
  · intro r
    rw [v4, v3, hτ2]
    simp only [WState.setv_val, Function.update_apply]
    split_ifs with a b
    · rfl
    · rfl
    · rw [v1 r b a]; exact hv r
  · rw [(k4 _ (fun j e => sCar_ne_low 1 j sIN (by decide) e.symm)).1,
      (k3 _ (fun j e => sCar_ne_low 0 j sIN (by decide) e.symm)).1]; exact in1
  · rw [(kk s6 (fun j e => sCar_ne_low 0 j s6 (by decide) e.symm) (fun j e => sCar_ne_low 1 j s6 (by decide) e.symm)).1]
    exact (keep1 s6 (fun i => low_not_tmem_sym s6 (by decide) i) (fun k => low_not_tmem_car s6 (by decide) k)
      (by decide)).1
  · rw [cl4, cl3]; exact c1
  · intro k
    match k with
    | ⟨0, _⟩ => exact ((k4 _ (fun j e => off01 j 0 e.symm)).1).trans z3
    | ⟨1, _⟩ => exact z4

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarM2b
