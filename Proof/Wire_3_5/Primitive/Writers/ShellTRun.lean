import Proof.Wire_3_5.Primitive.Writers.ShellTBoot

/-! # for THR and C6: the THR writer shell's run, part 2: any unit machine, and the run

CellLoopD's loop with the unit machine abstracted to THR's `UnitOK` (the only `unitM`-specific step,
`CellUnit.unit_step`, is `UnitOK`'s content), then ShellX's assembly with the THR boot (`ShellTBoot.bootX_stepT`):

* `loop_stageU`, `loopCellsU`, `loop_stepU` (the loop body `PrimThrW.Shell.bodyU x U`);
* `shellMG`, `shellCostG`, **`shell_runG`**: the run with any dimension stage (`ShellTBoot.DimOK`);
* **`shell_runT`**: THR's `PrimThrW.Shell.ThrShellRun S x U D C D2 C2 Dv Cv cr DL CL` for every
  `ThrDataStage S`, unit machine `U` and constants (`shell_runG` at `NumsX.numsM cr`, `m = mOf P`).

Paper quantity of the main type: the THR writer's output tape `(List.range b).flatMap emit ++ [false]` from the THR
request word (lem:primitive P3:3068-3084), the loop dimensioned by `n' = 2^(2·kh + L)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.CellState NearCubicWires.WireExponent3_5.PrimAsm.CellUnit
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoopD NearCubicWires.WireExponent3_5.PrimAsm.ShellD
open NearCubicWires.WireExponent3_5.PrimAsm.ShellX NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Loop
variable (cap : ℕ)

theorem loop_stageU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) {e : ℕ} (R nU : ℕ) (w u : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (j : ℕ) (out : List Bool) (hcap : cap + 1 ≤ R)
    (hU : PrimThrW.Shell.UnitOK cap x U nU w u emit j out) :
    ∃ H' A', Step (PrimThrW.Shell.bodyU x U e) nU (loopHD x e out) (loopAD cap x e R w (false :: (marks u ++ [false])) Wk j out)
      H' A' ∧
      (∀ i, scrSD x e i = false →
        A' i = loopAD cap x e R w (false :: (marks u ++ [false])) Wk (j + 1) (out ++ emit j) i) ∧
      (∀ i, scrResetD x e i = false → H' i = loopHD x e (out ++ emit j) i) := by
  obtain ⟨σE, mU, stU, e0, e1, e1h, e2, hn⟩ := hU
  have n0 : sk x 113 ≠ sk x 0 := fun h => absurd (sk_inj x h) (by decide)
  have n1 : sk x 113 ≠ sk x 1 := fun h => absurd (sk_inj x h) (by decide)
  have n2 : sk x 113 ≠ sk x 2 := fun h => absurd (sk_inj x h) (by decide)
  have eH0 : (Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).H (fun _ : Fin 1 => 0)) (fun _ => 0) :
      Fin ((TT x + 1) + e) → ℕ) = loopHD x e out := by
    rw [blank_H]
    rfl
  -- 1: the copy-in
  have cp := cpW_spec 0 u (⟨fun _ => 0, ![false :: (marks u ++ [false]), []], fun r => r.elim0, false⟩ : WState 1 0)
    rfl rfl rfl rfl
  have cps := (WExec.exec 0 cp).step
  have dk := Rec.dockRun cps (cpSlots x e) (cpSlots_inj x e)
    (Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).H (fun _ : Fin 1 => 0)) (fun _ => 0))
    (Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).A (fun _ : Fin 1 => false :: (marks u ++ [false])))
      Wk)
    (by
      intro k
      fin_cases k
      · show _ = (wenc 0 _).H (sTape 0)
        rw [wenc_H_s]; simp [cpSlots, dataP]
      · show _ = (wenc 0 _).H cTape
        rw [wenc_H_c]; simp [cpSlots, cellP, wenc_H_c]
      · show _ = (wenc 0 _).H (sTape 1)
        rw [wenc_H_s]; simp [cpSlots, cellP, wenc_H_s, blankCell, n1])
    (by
      intro k
      fin_cases k
      · show _ = (wenc 0 _).A (sTape 0)
        rw [wenc_A_s]; simp [cpSlots, dataP]
      · show _ = (wenc 0 _).A cTape
        rw [wenc_A_c]; simp [cpSlots, cellP, wenc_A_c, blankCell]
      · show _ = (wenc 0 _).A (sTape 1)
        rw [wenc_A_s]; simp [cpSlots, cellP, wenc_A_s, blankCell, n0, n1, n2])
  have eH : dockH (cpSlots x e) (Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).H
      (fun _ : Fin 1 => 0)) (fun _ => 0))
      (wenc 0 ((⟨fun _ => 0, ![false :: (marks u ++ [false]), []], fun r => r.elim0, false⟩ : WState 1 0).sets 1 u)).H =
      Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).H (fun _ : Fin 1 => 0)) (fun _ => 0) := by
    refine Shell.dockH_eq _ (cpSlots_inj x e) _ _ _ ?_ (fun _ _ => rfl)
    intro k
    fin_cases k
    · show _ = (wenc 0 _).H (sTape 0)
      rw [wenc_H_s]; simp [cpSlots, dataP]
    · show _ = (wenc 0 _).H cTape
      rw [wenc_H_c]; simp [cpSlots, cellP, wenc_H_c]
    · show _ = (wenc 0 _).H (sTape 1)
      rw [wenc_H_s]; simp [cpSlots, cellP, wenc_H_s, blankCell, n1]
  have eA : install (cpSlots x e) (Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).A
      (fun _ : Fin 1 => false :: (marks u ++ [false]))) Wk)
      (wenc 0 ((⟨fun _ => 0, ![false :: (marks u ++ [false]), []], fun r => r.elim0, false⟩ : WState 1 0).sets 1 u)).A =
      Fin.addCases (Fin.addCases (wenc cap (blankCellD x w out j u)).A
        (fun _ : Fin 1 => false :: (marks u ++ [false]))) Wk := by
    refine Shell.install_eq _ (cpSlots_inj x e) _ _ _ ?_ ?_
    · intro k
      fin_cases k
      · show _ = (wenc 0 _).A (sTape 0)
        rw [wenc_A_s]; simp [cpSlots, dataP]
      · show _ = (wenc 0 _).A cTape
        rw [wenc_A_c]; simp [cpSlots, cellP, wenc_A_c, blankCellD, blankCell]
      · show _ = (wenc 0 _).A (sTape 1)
        rw [wenc_A_s]; simp [cpSlots, cellP, wenc_A_s, blankCellD]
    · intro i hi
      revert hi
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hc : c ≠ sTape (sk x 113) := fun h => hi 2 (by rw [h]; rfl)
          simp only [Fin.addCases_left]
          exact blankCellD_A cap x w out j u c hc
        · intro _
          simp
      · intro _
        simp
  rw [eH, eA] at dk
  -- 2: the unit
  have su := (stU.embed (fun _ : Fin 1 => 0) (fun _ => false :: (marks u ++ [false]))).embed (fun _ : Fin e => 0) Wk
  rw [blankCellD_H] at su
  have whole := dk.seq su
  -- 3: from the cleared state
  have c := Scrub.cleared_entry whole (scrSD x e) R (by
    intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · intro hc
        have hk : kept x c = false := by simpa [scrSD, keptD] using hc
        obtain ⟨k, hk1, hk2⟩ := blank_scratch cap x w out j c hk
        exact ⟨k, by omega, by simpa using hk2⟩
      · intro hv
        simp [scrSD, keptD] at hv
    · intro hk
      simp [scrSD] at hk)
  have ce := c.enlarge hn
  have eB0 : Scrub.blank (scrSD x e) (Fin.addCases (Fin.addCases (wenc cap (blankCell x w out j)).A
      (fun _ : Fin 1 => false :: (marks u ++ [false]))) Wk) R =
      loopAD cap x e R w (false :: (marks u ++ [false])) Wk j out := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · simp only [Scrub.blank, scrSD, keptD, loopAD, Fin.addCases_left]
        cases hk : kept x c <;> simp [hk]
      · simp [Scrub.blank, scrSD, keptD, loopAD]
    · simp [Scrub.blank, scrSD, loopAD]
  rw [eH0, eB0] at ce
  refine ⟨_, _, ce, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · intro hi
        have hk : kept x c = true := by simpa [scrSD, keptD] using hi
        simp only [Fin.addCases_left, loopAD, hk, if_true, Bool.not_true, Bool.false_eq_true, if_false,
          ZeroPadding.pad_zero, scrSD, keptD]
        have hk' := hk
        simp only [kept, Bool.or_eq_true, decide_eq_true_eq] at hk'
        rcases hk' with (rfl | rfl) | rfl
        · rw [wenc_A_s, wenc_A_s, e0, blankCell_st0]
        · rw [wenc_A_s, wenc_A_s, e1, blankCell_st1]
        · rw [wenc_A_s, wenc_A_s, e2, blankCell_st2]
      · intro _
        simp [loopAD, scrSD, keptD]
    · intro _
      simp [loopAD, scrSD]
  · intro i
    refine Fin.addCases (fun a => ?_) (fun k => ?_) i
    · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
      · intro hi
        have ha : c = sTape (sk x 1) := by simpa [scrResetD] using hi
        subst ha
        simp only [Fin.addCases_left, loopHD, if_true]
        rw [wenc_H_s, e1h]
      · intro hi
        exfalso
        have he : Fin.natAdd (TT x) v = Fin.castAdd 1 (sTape (nr := LNR) (sk x 1)) := by
          simpa [scrResetD] using hi
        have hv := congrArg Fin.val he
        have h2 : (sTape (nr := LNR) (sk x 1)).val = 2 := rfl
        simp only [Fin.val_natAdd, Fin.val_castAdd, h2] at hv
        have hT : 3 ≤ TT x := by unfold TT LNS LNR; omega
        omega
    · intro hi
      simp [scrResetD] at hi

end Loop

section Cells
variable (cap : ℕ)

/-- **The writer's loop with the data tape** as base `Cells`. -/
noncomputable def loopCellsU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) {e : ℕ} (R nU bound : ℕ) (w u : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (hcap : cap + 1 ≤ R) (hR : nU + 1 ≤ R)
    (hdec : ∀ j < bound, ∀ out : List Bool, PrimThrW.Shell.UnitOK cap x U nU w u emit j out) :=
  Cells.ofScrub (PrimThrW.Shell.bodyU x U e) (scrResetD x e) (scrSD x e) R (R + 2) bound
    (fun _ out => loopHD x e out) (fun j out => loopAD cap x e R w (false :: (marks u ++ [false])) Wk j out) emit
    (fun i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hk : kept x c = false := by simpa [scrSD, keptD] using hi
          have hne : c ≠ sTape (sk x 1) := fun h => by subst h; simp [kept] at hk
          simp [scrResetD, hne]
        · intro hi
          simp [scrSD, keptD] at hi
      · intro hi
        simp [scrSD] at hi)
    hR (by omega)
    (fun j _ out i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hne : c ≠ sTape (sk x 1) := by simpa [scrResetD] using hi
          simp [loopHD, hne]
        · intro _
          simp [loopHD]
      · intro _
        simp [loopHD])
    (fun j _ out i => by
      refine Fin.addCases (fun a => ?_) (fun k => ?_) i
      · refine Fin.addCases (fun c => ?_) (fun v => ?_) a
        · intro hi
          have hk : kept x c = false := by simpa [scrSD, keptD] using hi
          simp [loopAD, hk]
        · intro hi
          simp [scrSD, keptD] at hi
      · intro hi
        simp [scrSD] at hi)
    (fun j hj out => loop_stageU cap x U R nU w u Wk emit j out hcap (hdec j hj out))

/-- **The writer's loop with the data tape, as one `Step`** (base `Cells.loopStep`). -/
theorem loop_stepU (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU) {e : ℕ} (R nU bound : ℕ) (w u : List Bool)
    (Wk : Fin e → List Bool) (emit : ℕ → List Bool) (hcap : cap + 1 ≤ R) (hR : nU + 1 ≤ R)
    (hdec : ∀ j < bound, ∀ out : List Bool, PrimThrW.Shell.UnitOK cap x U nU w u emit j out) :
    Step (CloseoutRowsDegreeLoop.machine (Scrub.machine (PrimThrW.Shell.bodyU x U e) (scrResetD x e) (scrSD x e)))
      (bound * ((2 * nU + 2 + 1 + (2 * R + 4)) + 3) + 3)
      (Fin.addCases (Scrub.heads (loopHD x e [])) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (loopAD cap x e R w (false :: (marks u ++ [false])) Wk 0 []) R (R + 2))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound))
      (Fin.addCases (Scrub.heads (loopHD x e ([] ++ (List.range bound).flatMap emit))) (fun _ : Fin 1 => 1))
      (Fin.addCases (Scrub.bank (loopAD cap x e R w (false :: (marks u ++ [false])) Wk bound
        ([] ++ (List.range bound).flatMap emit)) R (R + 2))
        (fun _ : Fin 1 => RepairSource.VerifierDecoding.CompareMachine.word bound)) :=
  Cells.loopStep (loopCellsU cap x U R nU bound w u Wk emit hcap hR hdec) []

end Cells

section Run

/-- **The THR shell's machine with any dimension stage** (`PrimThrW.Shell.shellMT` at `M2 = NumsX.numsM cr`). -/
noncomputable def shellMG (S : ThrData.ThrDataStage) (x : ℕ) {sU : ℕ} (U : Machine (TT x) sU)
    (D C D2 C2 Dv Cv DL CL : ℕ) {s2 : ℕ} (M2 : Machine NUn s2) :=
  MaskedReset.machine (Composition.machine (Composition.machine (bootXMG S x D D2 Dv DL C2 Cv CL M2)
    (entryEX x D D2 Dv DL C)) (PrimThrW.Shell.loopEU x U D D2 Dv DL)) (fun _ => true)

/-- The shell's cost with the dimension stage's cost `c2` (`ShellX.shellCostX` at `c2 = 2·numsStageCost + 2`). -/
def shellCostG (w : List Bool) (n D C D2 C2 cc Dv Cv c2 m DL CL nU : ℕ) : ℕ :=
  bootXCostG w n D2 C2 cc Dv Cv c2 m DL CL + 1 + Scrub.entryCost D C (2 ^ m) + 1 +
    (UnaryCalc.value DL CL (2 ^ m) * ((2 * nU + 2 + 1 + (2 * UnaryCalc.value D C (2 ^ m) + 4)) + 3) + 3)

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
