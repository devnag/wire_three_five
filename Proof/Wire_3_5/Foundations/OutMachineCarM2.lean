import Proof.Wire_3_5.Foundations.OutMachineCarM1

/-! # The output machine carrier phase, part 3: the carrier tables

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050): the final pass reads
each named carrier `X` as the table `gatesW h (maskGates X)` (P3:3071-3086). From the request with `1^n`, `1^L`, PA's
`setupW` fills the carrier slots (`Done`/`Blank`), both countdowns are cleared, and `carTableM` runs on each filled
slot (`Data.carT`):

* `carCostB` (a slot's step bound), **`carStage`**: one slot, filled or blank: `sCar k 3 = carTab carriers k`,
  `sCar k 5 = 1^{carCnt carriers k}`, the slot's heads `0`, everything off the slot kept;
* `m2W`, **`m2M`**, **`m2_spec`**: the whole stage from the request, `1^n`, `1^L` and blank slots: the two tables
  and counts, every head `0` but the request's, every register `0`, the request and the spare stream `6` kept.

Paper quantity of the main type: the carriers' mask tables `carTab carriers k` and their counts (P3:3049-3050). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarM2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- A slot's step bound: the table machine on a filled slot, the idle branch on a blank one. -/
noncomputable def carCostB {n : ℕ} (carriers : List (Stars.Carrier n)) (L : ℕ) (k : ℕ) : ℕ :=
  if h : k < carriers.length then PrimT.CarTable.carTableCost (carriers.get ⟨k, h⟩) L + 2 else 2

theorem updS_st_off (k : Fin 2) (σ : WState DS DR) (tout : Fin 1357 → List Bool) (s : Fin (DS + 1))
    (hs : ∀ j, s ≠ sCar k j) : (updS (sCar k) σ (fun _ => 0) tout).st s = σ.st s := by
  show install (sCar k) σ.st tout s = σ.st s
  exact install_other _ _ _ _ (fun j e => hs j e.symm)

theorem updS_sh_off (k : Fin 2) (σ : WState DS DR) (tout : Fin 1357 → List Bool) (s : Fin (DS + 1))
    (hs : ∀ j, s ≠ sCar k j) : (updS (sCar k) σ (fun _ => 0) tout).sh s = σ.sh s := by
  show dockH (sCar k) σ.sh (fun _ => 0) s = σ.sh s
  exact dockH_other _ _ _ _ (fun j e => hs j e.symm)

theorem updS_st_on (k : Fin 2) (σ : WState DS DR) (tout : Fin 1357 → List Bool) (j : Fin 1357) :
    (updS (sCar k) σ (fun _ => 0) tout).st (sCar k j) = tout j := by
  show install (sCar k) σ.st tout (sCar k j) = tout j
  exact install_slot _ (sCar_inj k) _ _ _

theorem updS_sh_on (k : Fin 2) (σ : WState DS DR) (tout : Fin 1357 → List Bool) (j : Fin 1357) :
    (updS (sCar k) σ (fun _ => 0) tout).sh (sCar k j) = 0 := by
  show dockH (sCar k) σ.sh (fun _ => 0) (sCar k j) = 0
  rw [dockH_slot _ (sCar_inj k)]

/-! ## The stage -/

/-- The spare stream `6` (the carrier count's output). -/
def s6 : Fin (DS + 1) := 6

/-- The setup, then both countdowns cleared. -/
def m2W : WM DS DR := .seq setupW (.seq (WM.clear rA) (WM.clear rK))

/-- **The stage's machine**: the setup, then the table machine on each carrier slot. -/
noncomputable def m2M := Composition.machine m2W.toProg.compile (Composition.machine (carT 0) (carT 1))

/-- The stage's step bound. -/
noncomputable def m2Bnd (cap n L : ℕ) (codes : List ℕ) {n' : ℕ} (carriers : List (Stars.Carrier n')) : ℕ :=
  setupCost n L codes (carriers.map Stars.Carrier.code) + 1 + (3 * cap + 1 + 1 + (3 * cap + 1)) + 1 +
    (carCostB carriers L 0 + 1 + carCostB carriers L 1)

theorem sCar_hi_off (k : Fin 2) (j : Fin 1357) (hj : 3 ≤ j.val) :
    (∀ i, ¬ tmem (sCar k j) (symTrip i)) ∧ (∀ k', ¬ tmem (sCar k j) (carTrip k')) ∧ sCar k j ≠ sIN := by
  refine ⟨fun i => ?_, fun k' => ?_, sCar_ne_low k j sIN (by decide)⟩
  · simp only [symTrip, tmem, not_or]
    exact ⟨(sSym_ne_sCar _ _ _ _).symm, (sSym_ne_sCar _ _ _ _).symm, (sSym_ne_sCar _ _ _ _).symm⟩
  · simp only [carTrip, tmem, not_or, sCar_eq_iff, not_and]
    refine ⟨fun _ e => ?_, fun _ e => ?_, fun _ e => ?_⟩ <;> (rw [e] at hj; simp at hj)

theorem trip_sh (τ : WState DS DR) (t : Trip) (x n L : ℕ) (h : Done τ t x n L ∨ Blank τ t) (s : Fin (DS + 1))
    (hs : tmem s t) : τ.sh s = 0 := by
  rcases h with ⟨_, a, _, b, _, c⟩ | ⟨_, a, _, b, _, c⟩ <;>
    rcases hs with rfl | rfl | rfl <;> assumption

theorem off01 (j j' : Fin 1357) : sCar 1 j ≠ sCar 0 j' := fun e => by
  rw [sCar_eq_iff] at e; exact absurd e.1 (by decide)

theorem slot_tr (τ τ' : WState DS DR) (hk : ∀ s, (∀ j, s ≠ sCar 0 j) → τ'.st s = τ.st s ∧ τ'.sh s = τ.sh s)
    (x n L : ℕ) : (Done τ (carTrip 1) x n L → Done τ' (carTrip 1) x n L) ∧ (Blank τ (carTrip 1) → Blank τ' (carTrip 1)) := by
  have e0 := hk (sCar 1 0) (fun j => off01 0 j)
  have e1 := hk (sCar 1 1) (fun j => off01 1 j)
  have e2 := hk (sCar 1 2) (fun j => off01 2 j)
  refine ⟨fun ⟨d1, d2, d3, d4, d5, d6⟩ => ?_, fun ⟨d1, d2, d3, d4, d5, d6⟩ => ?_⟩ <;>
    simp only [carTrip] at d1 d2 d3 d4 d5 d6 ⊢ <;>
    exact ⟨e0.1.trans d1, e0.2.trans d2, e1.1.trans d3, e1.2.trans d4, e2.1.trans d5, e2.2.trans d6⟩

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarM2
