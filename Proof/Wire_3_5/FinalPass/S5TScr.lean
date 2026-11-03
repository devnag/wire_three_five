import Lean
import Proof.Wire_3_5.FinalPass.S5TPost2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.S5TStage
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.FinalPass.S5TScrBase


noncomputable section
set_option maxRecDepth 120000


/-! # S5-THR, part 31: the THR half on the scrub's layout (P3:3170-3181)

The whole THR half on the scrub's layout `(ns + 2 + nr) + 1 + 1`: the prelude (`pre_step3`: the scrub's source bank
at `R = W`, `L = 2W + 3`), the stage under base's scrub (`Scrub.step` with every head reset and the scratch `scS`:
the cell and every stream but the input, the THR slots and the top power), then the register tapes and the driver
erased (`eraseRegs`, `eraseT`). At the exit the input and the THR slots are the stage's, every other tape is
`List.replicate ℓ false` with `ℓ ≤ 2W + 3`, every head is at `0`.

* `scS`, `regL`, `thrM`, **`thrM_run`**.

Paper quantity of the main type: the THR half's exit (THR slots `8 … 15`, blank scratch within `2W + 3`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c)

section Scr
variable (D : ℕ) (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ)

/-- **The THR half on the scrub's layout.** -/
noncomputable def thrM (l : Literals) (cr j0 jL j1 c0 : ℕ) :=
  Composition.machine (Composition.machine
    (preM3 (nr := nrL) D (fs2 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) c0)
    (Scrub.machine (stageM D alg Dexp l cr j0 jL j1) (fun _ => true)
      (scS D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x)))
    (Prog.seq (eraseRegs (regL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x))
      (eraseT Scrub.driverTape)).compile

/-- **The THR half on the scrub's layout, run**: from the final pass's entry bank, given the stage's run from the
prelude's exit within `W − 1` steps. -/
theorem thrM_step (l : Literals) (cr j0 jL j1 c0 : ℕ) (u : List Bool) (W : ℕ)
    (hW : (u.length + 1 + c0) ^ (D + 1) = W) (hD : 1 ≤ D) (hy : 2 ≤ u.length + 1 + c0)
    (σE : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) nrL) (n : ℕ)
    (hst : Step (stageM D alg Dexp l cr j0 jL j1) n
      (wenc (2 * W + 2) (σ03 (nr := nrL) D (fs2 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) c0 u)).H
      (wenc (2 * W + 2) (σ03 (nr := nrL) D (fs2 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) c0 u)).A (wenc (2 * W + 2) σE).H
      (wenc (2 * W + 2) σE).A)
    (hR : n + 1 ≤ W) (hreg : ∀ r, σE.val r ≤ 2 * W + 2) :
    Step (thrM D alg Dexp l cr j0 jL j1 c0)
      (preTotal3 (u.length + 1) c0 D + 1 + (2 * n + 2 + 1 + (2 * W + 4)) + 1 +
        (nrL * (6 * (2 * W + 3) + 12) + 1 + (6 * W + 8)))
      (fun _ => 0) (A02 u) (fun _ => 0) (thrAf D alg Dexp W σE) := by
  have hge := nsL_ge D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x
  have hWy : u.length + 1 + c0 + 1 ≤ W := by
    rw [← hW]
    have h1 : (u.length + 1 + c0) ^ 2 ≤ (u.length + 1 + c0) ^ (D + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (u.length + 1 + c0) * 2 ≤ (u.length + 1 + c0) ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_left _ hy
    omega
  have hWj : ∀ j, j < D → (u.length + 1 + c0) ^ (j + 1) + 1 ≤ W := fun j hj => by
    rw [← hW]
    have h1 : (u.length + 1 + c0) ^ (j + 2) ≤ (u.length + 1 + c0) ^ (D + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (u.length + 1 + c0) ^ (j + 1) * 2 ≤ (u.length + 1 + c0) ^ (j + 2) := by
      rw [pow_succ (u.length + 1 + c0) (j + 1)]; exact Nat.mul_le_mul_left _ hy
    have h3 : 1 ≤ (u.length + 1 + c0) ^ (j + 1) := Nat.one_le_pow _ _ (by omega)
    omega
  have hH0 := wenc_H_zero (2 * W + 2) (σ03 (nr := nrL) D (fs2 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) c0 u) (σ03_sh D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x c0 u)
    (σ03_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x c0 u)
  have hA : ∀ i, scS D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x i = true →
      ((wenc (2 * W + 2) (σ03 (nr := nrL) D (fs2 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) c0 u)).A i).length ≤ W := by
    intro i hi
    rcases tape_cases i with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [wenc_A_s]
      have hs := s.isLt
      simp only [scS, PrimAsm.DockW.sTape_val, decide_eq_true_eq] at hi
      by_cases h9 : s.val = 9
      · rw [show s = sTm D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x from Fin.ext h9, σ03_tm]; simp [sent]; omega
      by_cases hp : s.val = 21 + D
      · rw [show s = sPad D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x from Fin.ext (by simp [sPad, sMisc]; omega), σ03_pad]; simp [sent]; omega
      by_cases hx : 12 ≤ s.val ∧ s.val < 12 + D
      · rw [show s = xsN D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x (s.val - 12) from Fin.ext (by rw [xsN_val D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x _ (by omega)]; omega),
          σ03_xs D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x c0 u _ (by omega)]
        simp [sent]; have := hWj (s.val - 12) (by omega); omega
      · rw [σ03_blank D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x c0 u s (by split at hi <;> omega) h9 hp (by split at hi <;> omega)]; simp
    · rw [wenc_A_c]; simp; omega
    · simp only [scS, PrimAsm.DockW.rTape_val, decide_eq_true_eq] at hi; omega
  have s1 := pre_step3 (nr := nrL) D (fs2 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) (fs2_inj D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) (fs2_0 D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) c0 u
  rw [hW] at s1
  have s2 := Scrub.step hst (fun _ => true) (scS D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) W (2 * W + 3) (fun i _ => by rw [hH0]) (fun _ _ => rfl)
    hA hR (by omega)
  rw [hH0, heads_zero, show Scrub.rewound (fun _ => true) (wenc (2 * W + 2) σE).H = fun _ => 0 from
    funext fun i => by simp [Scrub.rewound], heads_zero] at s2
  obtain ⟨b3, hb3⟩ : ∃ b : Bank (nsL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x + 2 + nrL + 1 + 1),
      b = ⟨fun _ => 0, Scrub.bank (Scrub.blank (scS D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) (wenc (2 * W + 2) σE).A W) W (2 * W + 3)⟩ := ⟨_, rfl⟩
  have regA : ∀ r : Fin nrL, b3.A (Scrub.inner (rTape r)) = regTape (2 * W + 2) (σE.val r) := fun r => by
    rw [hb3]
    simp only [Scrub.bank_inner, Scrub.blank]
    rw [if_neg (by simp only [scS, PrimAsm.DockW.rTape_val, decide_eq_true_eq]; omega), wenc_A_r]
  have e3a := eraseRegs_exec (2 * W + 3) (regL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x) b3 (regL_nodup D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x)
    (fun j hj => by
      obtain ⟨r, rfl⟩ := (mem_regL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x j).1 hj
      refine ⟨by rw [hb3], ⟨σE.val r, 2 * W + 2 - σE.val r, by rw [regA]; rfl⟩, ?_⟩
      rw [regA]; simp [regTape]; have := hreg r; omega)
  have hdr : Scrub.driverTape ∉ regL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x := fun h => by
    obtain ⟨r, hr⟩ := (mem_regL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x _).1 h
    exact Scrub.inner_ne_driver _ hr.symm
  have e3b := eraseT_exec Scrub.driverTape ⟨b3.H, fun i => if i ∈ regL D (PrimT.W6.numsW6 alg Dexp).x (PrimThrW.TF3Cost.topFront3 alg).x then
      List.replicate (b3.A i).length false else b3.A i⟩ W 0
    (by simp only [if_neg hdr]; rw [hb3]; simp) (by rw [hb3])
  have s3 := Exec.step (Exec.seq e3a e3b)
  rw [hb3] at s3
  exact Step.seq (Step.seq s1 s2) s3

end Scr

end NearCubicWires.WireExponent3_5.FinalPass.S5T

end
