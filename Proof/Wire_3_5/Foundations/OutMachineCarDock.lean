import Proof.Wire_3_5.Foundations.OutMachineCarIface

/-! # The output machine carrier phase, part 1: the outer layout and the masked dock

The carrier phase runs PA's data programs (`Data.setupW`, `Data.carT`, on `WM DS DR`) whose input head is left where
the parse stopped. A `CoreWordsM` run must end with every head at `0`, so each such stage runs under base's masked
reset (`Step.mask`, the selected head `sIN` returned to `0`; PA's `dataM` pattern), whose log is one more tape. The
phase's own layout is PA's plus that log stream:

* `NS = DS + 1`, `NR = DR`; `oS` (PA's streams inside), `oLog` (the log); `inner` (PA's state inside an outer one),
  `outerZ` (an outer state from PA's state and the log, heads `0`);
* **`mdock`** (PA's tapes and the log onto the outer tapes, a bijection), `mdock_inj`, its values;
* **`maskDock`**: any PA machine's run from the inner encoding (heads `0`) to one whose heads are `0` but on `sIN`,
  registers `0`, becomes a run of the masked, docked machine on the outer encoding within `2n + 2`, every head `0`,
  the log (`0^T`, `n ≤ T`) kept.

Paper quantity of the main type: none beyond the machine model (the carrier tables' stage, P3:3049-3050). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot)

/-! ## The outer layout -/

abbrev NS : ℕ := DS + 1
abbrev NR : ℕ := DR
abbrev OSt : Type := WState NS NR

/-- PA's stream `i` inside the outer layout. -/
def oS (i : Fin (DS + 1)) : Fin (NS + 1) := Fin.castSucc i
/-- The masked reset's log. -/
def oLog : Fin (NS + 1) := Fin.last (DS + 1)

theorem oS_ne_log (i : Fin (DS + 1)) : oS i ≠ oLog := Fin.castSucc_ne_last i

theorem oS_inj : Function.Injective oS := Fin.castSucc_injective _

/-- PA's state inside an outer state. -/
def inner (σ : OSt) : WState DS DR := ⟨fun i => σ.sh (oS i), fun i => σ.st (oS i), σ.val, σ.cell⟩

/-- The outer state from PA's state and the log, every head at `0`. -/
def outerZ (τ : WState DS DR) (lg : List Bool) : OSt :=
  ⟨fun _ => 0, Fin.lastCases (motive := fun _ => List Bool) lg τ.st, τ.val, τ.cell⟩

@[simp] theorem outerZ_st_oS (τ : WState DS DR) (lg : List Bool) (i : Fin (DS + 1)) :
    (outerZ τ lg).st (oS i) = τ.st i := by simp [outerZ, oS]
@[simp] theorem outerZ_st_log (τ : WState DS DR) (lg : List Bool) : (outerZ τ lg).st oLog = lg := by
  simp [outerZ, oLog]

/-! ## The dock -/

/-- **PA's tapes and the log onto the outer tapes**: streams and cell in place, registers one up, the log on
`oLog`'s tape. -/
def mdock (j : Fin (DS + 2 + DR + 1)) : Fin (NS + 2 + NR) :=
  ⟨if j.val < DS + 2 then j.val else if j.val < DS + 2 + DR then j.val + 1 else DS + 2, by
    have := j.isLt; show _ < DS + 1 + 2 + DR; split_ifs <;> omega⟩

theorem mdock_val (j : Fin (DS + 2 + DR + 1)) :
    (mdock j).val = if j.val < DS + 2 then j.val else if j.val < DS + 2 + DR then j.val + 1 else DS + 2 := rfl

theorem mdock_inj : Function.Injective mdock := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [mdock_val, mdock_val] at hv
  have ha : a.val < DS + 2 + DR + 1 := a.isLt
  have hb : b.val < DS + 2 + DR + 1 := b.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

theorem mdock_s (i : Fin (DS + 1)) :
    mdock (Fin.castAdd 1 (sTape (nr := DR) i)) = sTape (nr := NR) (oS i) := by
  apply Fin.ext
  rw [mdock_val]
  simp only [Fin.val_castAdd, sTape_val, oS, Fin.val_castSucc]
  have := i.isLt
  split_ifs <;> omega

theorem mdock_c : mdock (Fin.castAdd 1 (cTape (ns := DS) (nr := DR))) = cTape (ns := NS) (nr := NR) := by
  apply Fin.ext; rw [mdock_val]; simp only [Fin.val_castAdd, cTape_val]; decide

theorem mdock_r (r : Fin DR) : mdock (Fin.castAdd 1 (rTape (ns := DS) r)) = rTape (ns := NS) (nr := NR) r := by
  apply Fin.ext
  rw [mdock_val]
  simp only [Fin.val_castAdd, rTape_val]
  have := r.isLt
  have hN : NS = DS + 1 := rfl
  split_ifs <;> omega

theorem mdock_log : mdock (Fin.natAdd (DS + 2 + DR) (0 : Fin 1)) = sTape (nr := NR) oLog := by
  apply Fin.ext
  rw [mdock_val]
  simp only [Fin.val_natAdd, Fin.val_zero, sTape_val, oLog, Fin.val_last]
  split_ifs <;> omega

/-- The outer encoding at a docked tape is the inner encoding with the log. -/
theorem wenc_mdock (K : ℕ) (σ : OSt) (j : Fin (DS + 2 + DR + 1)) :
    (wenc K σ).A (mdock j) = Fin.addCases (wenc K (inner σ)).A (fun _ : Fin 1 => σ.st oLog) j := by
  refine Fin.addCases (fun j' => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    rcases tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [mdock_s, wenc_A_s, wenc_A_s]; rfl
    · rw [mdock_c, wenc_A_c, wenc_A_c]; rfl
    · rw [mdock_r, wenc_A_r, wenc_A_r]; rfl
  · rw [Fin.addCases_right]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rw [mdock_log, wenc_A_s]

/-- Every outer tape is docked. -/
theorem mdock_surj (j : Fin (NS + 2 + NR)) : ∃ j', mdock j' = j := by
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · refine Fin.lastCases ?_ (fun i' => ?_) i
    · exact ⟨_, mdock_log⟩
    · exact ⟨_, mdock_s i'⟩
  · exact ⟨_, mdock_c⟩
  · exact ⟨_, mdock_r r⟩

/-- The installed exit is the outer encoding of `outerZ`. -/
theorem install_mdock (K : ℕ) (σ : OSt) (τ : WState DS DR) (lg : List Bool) :
    install mdock (wenc K σ).A (Fin.addCases (wenc K τ).A (fun _ : Fin 1 => lg)) = (wenc K (outerZ τ lg)).A := by
  funext j
  obtain ⟨j', rfl⟩ := mdock_surj j
  rw [install_slot _ mdock_inj]
  refine Fin.addCases (fun j'' => ?_) (fun k => ?_) j'
  · rw [Fin.addCases_left]
    rcases tape_cases j'' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [mdock_s, wenc_A_s, wenc_A_s, outerZ_st_oS]
    · rw [mdock_c, wenc_A_c, wenc_A_c]; rfl
    · rw [mdock_r, wenc_A_r, wenc_A_r]; rfl
  · rw [Fin.addCases_right]
    have hk : k = 0 := Subsingleton.elim _ _
    subst hk
    rw [mdock_log, wenc_A_s, outerZ_st_log]

/-- The selected head: PA's input. -/
def selIn (j : Fin (DS + 2 + DR)) : Bool := decide (j = sTape (nr := DR) sIN)

/-- **The masked dock**: a PA machine's run from the inner encoding, every head `0`, to an encoding whose heads are
`0` but on `sIN` and whose registers are `0`, runs masked and docked on the outer encoding, every head back at `0`,
the log `0^T` kept (`n ≤ T`). -/
theorem maskDock {s : ℕ} (M : Machine (DS + 2 + DR) s) (K T n : ℕ) (σ : OSt) (τ : WState DS DR)
    (hlog : σ.st oLog = List.replicate T false) (hnT : n ≤ T)
    (hstep : Step M n (fun _ => 0) (wenc K (inner σ)).A (wenc K τ).H (wenc K τ).A)
    (hτsh : ∀ i, i ≠ sIN → τ.sh i = 0) (hτv : ∀ r, τ.val r = 0) :
    Step (RecoveryFocus.machine mdock (MaskedReset.machine M selIn)) (2 * n + 2) (fun _ => 0) (wenc K σ).A
      (fun _ => 0) (wenc K (outerZ τ (List.replicate T false))).A := by
  have hm := hstep.mask selIn (fun _ _ => rfl) hnT
  have h0 : Fin.addCases (fun _ : Fin (DS + 2 + DR) => (0 : ℕ)) (fun _ : Fin 1 => (0 : ℕ)) = fun _ => 0 := by
    funext j; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) j <;> simp
  have h1 : Fin.addCases (fun i => if selIn i = true then 0 else (wenc K τ).H i) (fun _ : Fin 1 => (0 : ℕ)) =
      fun _ => 0 := by
    funext j
    refine Fin.addCases (fun j' => ?_) (fun _ => ?_) j
    · rw [Fin.addCases_left]
      split_ifs with hs
      · rfl
      · rcases tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
        · have hi : i ≠ sIN := fun e => by subst e; simp [selIn] at hs
          rw [wenc_H_s, hτsh i hi]
        · rw [wenc_H_c]
        · rw [wenc_H_r, hτv]
    · simp
  rw [h0, h1] at hm
  have hd := Block.dockKeep hm mdock mdock_inj (fun _ => 0) (wenc K σ).A (fun _ => rfl) (fun j => by
    rw [wenc_mdock, hlog])
  rwa [install_mdock] at hd

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarL
