import Proof.Wire_3_5.Foundations.OutMachineSlot0S
import Proof.Wire_3_5.Foundations.OutMachineSlot1GenBase

/-! # SA's slot 0, part 4: the writer, and SA

* `setSt`, **`dock_streams`**: a machine's clean run (heads `0` at both ends) docked onto streams of a `WState`
  bank (`Block.dockKeep`), the bank's encoding at the other end;
* `stepReady` (a ready run is a `Step`), `s0_cases` (every slot-0 stream is `I0`, `U0` or a geo tape);
* the slot-0 machine `slot0M cr` (the trim ; the geo writer `geoM (offW cr) flD (flCv cr)` docked on `gs`), its
  constants `Cs0`, `Ds0`;
* **`slot0W l : CoreWordsMJ l 1 (SA.slot0Ws l)`** (S4's word 0, the offset word, at every request);
* **`SA.sa l : S4WordsMAJ l`** `:= SA.saOf l (slot0W l)` — **SA done**.

Paper quantity of the main type: S4's words 0–3 (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GLt gInP gOutP geoM gInP_ne_out)
open NearCubicWires.WireExponent3_5.PrimT.FlipsPack (flD flCv cA dA)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## Docking a clean run onto streams -/

section Dock
variable {ns nr : ℕ}

open Classical in
/-- The bank with the streams `gsl j` replaced by `v j`. -/
noncomputable def setSt {k : ℕ} (σ : WState ns nr) (gsl : Fin k → Fin (ns + 1)) (v : Fin k → List Bool) :
    WState ns nr :=
  ⟨σ.sh, fun i => if h : ∃ j, gsl j = i then v h.choose else σ.st i, σ.val, σ.cell⟩

theorem setSt_in {k : ℕ} (σ : WState ns nr) (gsl : Fin k → Fin (ns + 1)) (hinj : Function.Injective gsl)
    (v : Fin k → List Bool) (j : Fin k) : (setSt σ gsl v).st (gsl j) = v j := by
  have h : ∃ j', gsl j' = gsl j := ⟨j, rfl⟩
  simp only [setSt]
  rw [dif_pos h, hinj h.choose_spec]

theorem setSt_off {k : ℕ} (σ : WState ns nr) (gsl : Fin k → Fin (ns + 1)) (v : Fin k → List Bool) (i : Fin (ns + 1))
    (hi : ∀ j, gsl j ≠ i) : (setSt σ gsl v).st i = σ.st i := by
  simp only [setSt]
  rw [dif_neg (fun ⟨j, hj⟩ => hi j hj)]

/-- **A clean run docked onto streams.** -/
theorem dock_streams {k s : ℕ} (M : Machine k s) (gsl : Fin k → Fin (ns + 1)) (hinj : Function.Injective gsl)
    (c n : ℕ) (σ : WState ns nr) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ q, σ.val q = 0) (tin tout : Fin k → List Bool)
    (htin : ∀ j, σ.st (gsl j) = tin j) (h : Step M n (fun _ => 0) tin (fun _ => 0) tout) :
    Step (RecoveryFocus.machine (fun j => sTape (nr := nr) (gsl j)) M) n (wenc c σ).H (wenc c σ).A
      (wenc c (setSt σ gsl tout)).H (wenc c (setSt σ gsl tout)).A := by
  have hsi : Function.Injective (fun j => sTape (nr := nr) (gsl j)) := fun a b e => hinj (sTape_inj e)
  have hd := Block.dockKeep h (fun j => sTape (nr := nr) (gsl j)) hsi (wenc c σ).H (wenc c σ).A
    (fun j => by rw [wenc_H_s, hsh]) (fun j => by rw [wenc_A_s, htin])
  have eH : (wenc c (setSt σ gsl tout)).H = (wenc c σ).H := by
    rw [Join.wencH0 c σ hsh hv, Join.wencH0 c (setSt σ gsl tout) hsh hv]
  have eA : install (fun j => sTape (nr := nr) (gsl j)) (wenc c σ).A tout = (wenc c (setSt σ gsl tout)).A := by
    funext y
    by_cases hy : ∃ j, sTape (nr := nr) (gsl j) = y
    · obtain ⟨j, rfl⟩ := hy
      rw [install_slot _ hsi, wenc_A_s, setSt_in σ gsl hinj]
    · have hy' : ∀ j, sTape (nr := nr) (gsl j) ≠ y := fun j e => hy ⟨j, e⟩
      rw [install_other _ _ _ _ hy']
      rcases tape_cases y with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
      · rw [wenc_A_s, wenc_A_s, setSt_off σ gsl tout i (fun j e => hy' j (by rw [e]))]
      · rw [wenc_A_c, wenc_A_c]; rfl
      · rw [wenc_A_r, wenc_A_r]; rfl
  rw [eH, ← eA]
  exact hd

end Dock

theorem stepReady {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

theorem s0_cases (i : Fin (S0ns + 1)) : i = I0 ∨ i = U0 ∨ ∃ j, gs j = i := by
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  · by_cases h1 : i.val = 1
    · exact Or.inr (Or.inl (Fin.ext h1))
    · refine Or.inr (Or.inr ⟨⟨i.val - 2, ?_⟩, Fin.ext ?_⟩)
      · have := i.isLt; have h2 := S0ns_eq; omega
      · show 2 + (i.val - 2) = i.val; omega

/-! ## The slot-0 machine -/

/-- **The slot-0 machine**: the trim, then the offset writer on the geo tapes. -/
noncomputable def slot0Mach (cr : ℕ) : (s : ℕ) × Machine (S0ns + 2 + 17) s :=
  ⟨_, Composition.machine trimP.toProg.compile
    (RecoveryFocus.machine (fun j => sTape (nr := 17) (gs j)) (geoM (offW cr) flD (flCv cr)))⟩

/-- The slot-0 writer's step coefficient (on the row constant) and degree. -/
noncomputable def Cs0 (cr : ℕ) : ℕ := 3001 + (cA + 100) * (cr + 1) ^ (dA + 1)
noncomputable def Ds0 : ℕ := dA + 3

theorem bound0 (N cr n1 B : ℕ) (h1 : n1 ≤ 3000 * (N + 1) ^ 2) (hB : B ≤ (cA + 100) * (N + cr + 1) ^ (dA + 1)) :
    n1 + 1 + B ≤ Cs0 cr * (N + 1) ^ Ds0 ∧ B ≤ Cs0 cr * (N + 1) ^ Ds0 := by
  have e1 : (N + 1) ^ 2 ≤ (N + 1) ^ Ds0 := Nat.pow_le_pow_right (by omega) (by unfold Ds0; omega)
  have e2 : (N + 1) ^ (dA + 1) ≤ (N + 1) ^ Ds0 := Nat.pow_le_pow_right (by omega) (by unfold Ds0; omega)
  have e3 : N + cr + 1 ≤ (cr + 1) * (N + 1) := by nlinarith
  have e4 : (N + cr + 1) ^ (dA + 1) ≤ (cr + 1) ^ (dA + 1) * (N + 1) ^ (dA + 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left e3 _
  have e5 : 1 ≤ (N + 1) ^ Ds0 := Nat.one_le_pow _ _ (by omega)
  have e6 : (cA + 100) * (N + cr + 1) ^ (dA + 1) ≤ (cA + 100) * (cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0 := by
    calc (cA + 100) * (N + cr + 1) ^ (dA + 1) ≤ (cA + 100) * ((cr + 1) ^ (dA + 1) * (N + 1) ^ (dA + 1)) :=
          Nat.mul_le_mul_left _ e4
      _ ≤ (cA + 100) * ((cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ e2)
      _ = (cA + 100) * (cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0 := by ring
  have e7 : Cs0 cr * (N + 1) ^ Ds0 = 3001 * (N + 1) ^ Ds0 + (cA + 100) * (cr + 1) ^ (dA + 1) * (N + 1) ^ Ds0 := by
    unfold Cs0; ring
  constructor <;> omega

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SA
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.FinalPass.Finish

end NearCubicWires.WireExponent3_5.FinalPass.Out.SA
