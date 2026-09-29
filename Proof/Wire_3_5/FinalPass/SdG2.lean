import Proof.Wire_3_5.FinalPass.SdG1

/-! # S4 (the seeds phase), part 42: the seeds phase's machine and its run (P3:3170-3178)

**`s4M E tw sw win wout Mw`**: S4's machine on the layout `gLay E tw`: the prep (`prepWM`, lifted onto the body's
streams), the tables writer `Mw` docked on its tapes (`DockW.dockS`: input port on the body's stream `28`, output
port on `tTW`), the body (`bodyW E`, lifted). **`s4_run`**: from an entry state with S4's small numbers on word `7`,
blank ports and writer tapes, every head at `0` and every register `0`, given the writer's run on the prep's request
and the body's run from any state after the writer, S4's machine steps (`Step`) to a state whose numerator stream is
the body's, the denominator's stream untouched, every head at `0` and every register `0`.

Paper quantity of the main type: the seeds phase's run (the printed numerator, P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymPtEval2)
open NearCubicWires.WireExponent3_5.FinalPass.ThrPt (updW updW_st_in updW_st_out updW_sh_in updW_sh_out
  updW_val_in updW_cell)

variable (E : SymPtEval2)

/-- The prep on the seeds phase's layout. -/
noncomputable def prepG (tw : ℕ) : WM (gns E.nw E.nsc tw) (bnr E.nn E.nrs) :=
  WM.liftW fsB id (prepWM (ns := bns E.nw E.nsc) (nr := bnr E.nn E.nrs) (tW ⟨7, by omega⟩) (bst 28 (by omega)) sRp)

/-- The body on the seeds phase's layout. -/
noncomputable def bodyG (tw : ℕ) : WM (gns E.nw E.nsc tw) (bnr E.nn E.nrs) := WM.liftW fsB id (bodyW E)

/-- **S4's machine**: the prep, the docked tables writer, the body. -/
noncomputable def s4M (tw sw : ℕ) (win wout : Fin tw) (Mw : Machine tw sw) :=
  Composition.machine
    (Composition.machine (prepG E tw).toProg.compile
      (RecoveryFocus.machine (fun j => sTape (nr := bnr E.nn E.nrs) (tmW (nw := E.nw) (nsc := E.nsc) win wout j)) Mw))
    (bodyG E tw).toProg.compile

theorem id_inj {α : Type} : Function.Injective (id : α → α) := fun _ _ h => h

theorem s4_run (tw sw : ℕ) (win wout : Fin tw) (hio : win ≠ wout) (Mw : Machine tw sw) (cap Bud W X Mb : ℕ)
    (σ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs)) (vs : List ℕ) (hvl : vs.length = 16) (v : List Bool)
    (hst7 : σ.st (fsB (tW ⟨7, by omega⟩)) = Data.unaryList vs)
    (h28 : σ.st (fsB (bst 28 (by omega))) = []) (h27 : σ.st (fsB tTW) = [])
    (hWx : ∀ x, x ≠ win → x ≠ wout → σ.st (tmW win wout x) = [])
    (hsh : ∀ i, σ.sh i = 0) (hreg : ∀ q, σ.val q = 0)
    (hcap : (Data.unaryList vs).length + ppN vs + 2 ^ (vs.getD 11 0 + 1) + 4 * (ppReq vs).length + 10 ≤ cap)
    (hwr : WriterIfaceJ.WriterRun Mw Bud win wout (ppReq vs) v)
    (hbody : ∀ σ0 : BS E.nw E.nn E.nsc E.nrs,
      (∀ j : Fin (bns E.nw E.nsc + 1), j.val ≠ 27 → j.val ≠ 28 → σ0.st j = σ.st (fsB j)) → σ0.st tTW = v →
      (∀ j, σ0.sh j = 0) → (∀ k : Fin 16, σ0.val (sRp ⟨k.val, by omega⟩) = vs.getD k.val 0) →
      σ0.val (sRp 17) = ppN vs → σ0.val (sRp 18) = 2 ^ vs.getD 11 0 → (∀ q, ¬ IsPrepReg q → σ0.val q = 0) →
      σ0.cell = σ.cell →
      ∃ ω : BS E.nw E.nn E.nsc E.nrs, ∃ m, WExec cap (bodyW E) σ0 ω m ∧ m ≤ Mb ∧
        ω.st tN = frame (binary W X) ∧ ω.sh = σ0.sh ∧ ∀ q, ω.val q = 0) :
    ∃ τ : WState (gns E.nw E.nsc tw) (bnr E.nn E.nrs),
      Step (s4M E tw sw win wout Mw) (prepCost vs + 1 + Bud + 1 + Mb) (wenc cap σ).H (wenc cap σ).A
        (wenc cap τ).H (wenc cap τ).A ∧
      τ.st (fsB tN) = frame (binary W X) ∧ τ.st gD = σ.st gD ∧ (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  -- the prep on the body's view
  obtain ⟨σB, m1, e1, hm1, st1, sh1, rp1, n1, nE1, o1, cell1⟩ := prepWM_spec cap (tW ⟨7, by omega⟩) (bst 28 (by omega)) sRp vs hvl
    (viewW fsB id σ) hst7 (hsh _) h28 (hsh _) (fun k => hreg _) hcap
  have e1' := ThrPt.WExec.liftW_upd cap fsB_inj id_inj e1 σ (liftW_view fsB id σ)
  obtain ⟨σ1, g1⟩ : ∃ y, y = updW fsB id σ σB := ⟨_, rfl⟩
  rw [← g1] at e1'
  have s1in : ∀ j, σ1.st (fsB j) = σB.st j := fun j => by rw [g1]; exact updW_st_in fsB_inj σ σB j
  have h1in : ∀ j, σ1.sh (fsB j) = σB.sh j := fun j => by rw [g1]; exact updW_sh_in fsB_inj σ σB j
  have v1 : ∀ q, σ1.val q = σB.val q := fun q => by rw [g1]; exact updW_val_in id_inj σ σB q
  have s1out : ∀ i, (∀ j, fsB j ≠ i) → σ1.st i = σ.st i := fun i h => by rw [g1]; exact updW_st_out σ σB i h
  have h1out : ∀ i, (∀ j, fsB j ≠ i) → σ1.sh i = σ.sh i := fun i h => by rw [g1]; exact updW_sh_out σ σB i h
  have c1 : σ1.cell = σ.cell := by rw [g1, updW_cell, cell1]; rfl
  have hB28 : σB.st (bst 28 (by omega)) = frame (ppReq vs) := by rw [st1, Function.update_self]
  have hBo : ∀ j : Fin (bns E.nw E.nsc + 1), j.val ≠ 28 → σB.st j = σ.st (fsB j) := fun j hj => by
    rw [st1, Function.update_of_ne (ne_of_val (show j.val ≠ 28 from hj))]; rfl
  have hBsh : ∀ j, σB.sh j = 0 := fun j => by rw [sh1]; exact hsh _
  -- the writer
  obtain ⟨J, _, hready⟩ := hwr
  have hwh : (fun j => σ1.sh (tmW (nw := E.nw) (nsc := E.nsc) win wout j)) = fun _ => 0 := by
    funext x
    by_cases hx1 : x = win
    · rw [hx1, show (tmW (nw := E.nw) (nsc := E.nsc) win wout win) = fsB (bst 28 (by omega)) by simp [tmW], h1in, hBsh]
    · by_cases hx2 : x = wout
      · rw [hx2, show (tmW (nw := E.nw) (nsc := E.nsc) win wout wout) = fsB tTW by simp [tmW, Ne.symm hio], h1in, hBsh]
      · rw [h1out _ (fun j h => tmW_off win wout x hx1 hx2 j h.symm), hsh]
  have hwa : (fun j => σ1.st (tmW (nw := E.nw) (nsc := E.nsc) win wout j)) = WriterIface.inBank win (ppReq vs) := by
    funext x
    unfold WriterIface.inBank
    by_cases hx1 : x = win
    · rw [if_pos hx1, hx1, show (tmW (nw := E.nw) (nsc := E.nsc) win wout win) = fsB (bst 28 (by omega)) by simp [tmW],
        s1in, hB28]
    · rw [if_neg hx1]
      by_cases hx2 : x = wout
      · rw [hx2, show (tmW (nw := E.nw) (nsc := E.nsc) win wout wout) = fsB tTW by simp [tmW, Ne.symm hio], s1in,
          hBo _ (by show (27 : ℕ) ≠ 28; omega), h27]
      · rw [s1out _ (fun j h => tmW_off win wout x hx1 hx2 j h.symm), hWx x hx1 hx2]
  have hstep : Step Mw Bud (fun j => σ1.sh (tmW (nw := E.nw) (nsc := E.nsc) win wout j))
      (fun j => σ1.st (tmW (nw := E.nw) (nsc := E.nsc) win wout j)) (fun _ => 0)
      (WriterIfaceJ.outBankJ win wout (ppReq vs) v J) := by
    rw [hwh, hwa]
    obtain ⟨r, hr, ht, hh, hs⟩ := hready
    exact ⟨r, hr, funext hh, ht, hs⟩
  have e2 := DockW.dockS (cap := cap) (tmW win wout) (tmW_inj win wout) σ1 hstep
  obtain ⟨σ2, g2⟩ : ∃ y, y = DockW.updS (tmW (nw := E.nw) (nsc := E.nsc) win wout) σ1 (fun _ => 0)
      (WriterIfaceJ.outBankJ win wout (ppReq vs) v J) := ⟨_, rfl⟩
  rw [← g2] at e2
  have s2 : ∀ i, σ2.st i = install (tmW (nw := E.nw) (nsc := E.nsc) win wout) σ1.st
      (WriterIfaceJ.outBankJ win wout (ppReq vs) v J) i := fun i => by rw [g2]; rfl
  have sh2 : ∀ i, σ2.sh i = dockH (tmW (nw := E.nw) (nsc := E.nsc) win wout) σ1.sh (fun _ => 0) i := fun i => by
    rw [g2]; rfl
  have v2 : ∀ q, σ2.val q = σ1.val q := fun q => by rw [g2]; rfl
  have c2 : σ2.cell = σ1.cell := by rw [g2]; rfl
  have sh20 : ∀ i, σ2.sh i = 0 := fun i => by
    rw [sh2]
    by_cases hx : ∃ x, tmW (nw := E.nw) (nsc := E.nsc) win wout x = i
    · obtain ⟨x, rfl⟩ := hx
      rw [dockH_slot _ (tmW_inj win wout)]
    · rw [dockH_other _ _ _ _ (fun x h => hx ⟨x, h⟩)]
      by_cases hy : ∃ j, fsB j = i
      · obtain ⟨j, rfl⟩ := hy
        rw [h1in, hBsh]
      · rw [h1out _ (fun j h => hy ⟨j, h⟩), hsh]
  -- the body on the view after the writer
  have hin : tmW (nw := E.nw) (nsc := E.nsc) win wout win = fsB (bst 28 (by omega)) := by simp [tmW]
  have hout : tmW (nw := E.nw) (nsc := E.nsc) win wout wout = fsB tTW := by simp [tmW, Ne.symm hio]
  obtain ⟨ω, m3, e3, hm3, hN, hshω, hvω⟩ := hbody (viewW fsB id σ2)
    (fun j h27 h28 => by
      show σ2.st (fsB j) = σ.st (fsB j)
      rw [s2, install_other _ _ _ _ (fun x h => by
        have := tmW_body win wout x j h
        omega), s1in, hBo j h28])
    (by
      show σ2.st (fsB tTW) = v
      rw [s2, ← hout, install_slot _ (tmW_inj win wout)]
      exact WriterIfaceJ.outBankJ_out win wout hio _ _ _)
    (fun j => sh20 _)
    (fun k => by show σ2.val _ = _; rw [v2, v1]; exact rp1 k)
    (by show σ2.val _ = _; rw [v2, v1]; exact n1)
    (by show σ2.val _ = _; rw [v2, v1]; exact nE1)
    (fun q hq => by
      show σ2.val q = 0
      rw [v2, v1, o1 q (fun k h => hq ⟨⟨k.val, by omega⟩, show k.val ≠ 16 by omega, show k.val < 19 by omega, h⟩)
        (fun h => hq ⟨17, by decide, by decide, h⟩) (fun h => hq ⟨18, by decide, by decide, h⟩)]
      exact hreg q)
    (by show σ2.cell = σ.cell; rw [c2, c1])
  have e3' := ThrPt.WExec.liftW_upd cap fsB_inj id_inj e3 σ2 (liftW_view fsB id σ2)
  refine ⟨updW fsB id σ2 ω, Step.enlarge (Step.seq (Step.seq (WExec.exec cap e1').step e2) (WExec.exec cap e3').step)
    (by omega), ?_, ?_, ?_, ?_⟩
  · rw [updW_st_in fsB_inj, hN]
  · rw [updW_st_out σ2 ω gD (fun j => fsB_ne_gD j), s2,
      install_other _ _ _ _ (fun x => tmW_ne_gD win wout x), s1out _ (fun j => fsB_ne_gD j)]
  · intro i
    by_cases hy : ∃ j, fsB j = i
    · obtain ⟨j, rfl⟩ := hy
      rw [updW_sh_in fsB_inj, hshω]
      exact sh20 _
    · rw [updW_sh_out σ2 ω i (fun j h => hy ⟨j, h⟩)]
      exact sh20 i
  · intro q
    exact (updW_val_in id_inj σ2 ω q).trans (hvω q)

end NearCubicWires.WireExponent3_5.FinalPass.Sd
