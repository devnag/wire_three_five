import Proof.Wire_3_5.FinalPass.SymF9

/-! # SWf (the SYM words writer's flat tables), part 10: the part's tail, run

**`tail_run`**: from a state whose registers hold `n` (`320`), `M, B, errExp` (`440 … 442`), `|FlatSeed|` (`449`) and
`L_c` (`330 + c`), every register within the capacity, the four writer blocks blank with heads `0`, and the flat
tables writer's run on each request `reqT n M B errExp L_c 0 |FlatSeed|` with output `v_c`: the tail `tailM` steps
(within `tailCost`) to a state with `v_c` on block `c`'s output tape, the request on its input tape, the writer's
residues (`≤ Bud`) on its other tapes, every block head `0`, every stream off the blocks untouched, every register `0`.

Paper quantity of the main type: the four circuits' flat tables words (`tablesJ k j`, P3:1508-1520) on the part's
output streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Run
variable (xF tw : ℕ)

theorem upd_in (c : Fin 4) (ρ : WState (LNS (xP xF tw)) LNR) (H : Fin tw → ℕ) (A : Fin tw → List Bool) (j : Fin tw) :
    (DockW.updS (tmC xF tw c) ρ H A).st (tmC xF tw c j) = A j :=
  install_slot _ (tmC_inj xF tw c) _ _ j

theorem upd_out (c : Fin 4) (ρ : WState (LNS (xP xF tw)) LNR) (H : Fin tw → ℕ) (A : Fin tw → List Bool)
    (i : Fin (LNS (xP xF tw) + 1)) (h : ∀ j, tmC xF tw c j ≠ i) : (DockW.updS (tmC xF tw c) ρ H A).st i = ρ.st i :=
  install_other _ _ _ i h

theorem upd_hin (c : Fin 4) (ρ : WState (LNS (xP xF tw)) LNR) (H : Fin tw → ℕ) (A : Fin tw → List Bool) (j : Fin tw) :
    (DockW.updS (tmC xF tw c) ρ H A).sh (tmC xF tw c j) = H j :=
  dockH_slot _ (tmC_inj xF tw c) _ _ j

theorem upd_hout (c : Fin 4) (ρ : WState (LNS (xP xF tw)) LNR) (H : Fin tw → ℕ) (A : Fin tw → List Bool)
    (i : Fin (LNS (xP xF tw) + 1)) (h : ∀ j, tmC xF tw c j ≠ i) : (DockW.updS (tmC xF tw c) ρ H A).sh i = ρ.sh i :=
  dockH_other _ _ _ i h

theorem blk_out (c c' : Fin 4) (hc : c' ≠ c) (j : Fin tw) : ∀ j', tmC xF tw c' j' ≠ tmC xF tw c j :=
  fun j' => tmC_ne xF tw c' c hc j' j

variable {sw : ℕ} (Mw : Machine tw sw) (win : Fin tw)

/-- **The part's tail, run.** -/
theorem tail_run (cap : ℕ) (wout : Fin tw) (hio : win ≠ wout) (Bud : Fin 4 → ℕ) (n M B err K lw : ℕ) (Ls : Fin 4 → ℕ)
    (vs : Fin 4 → List Bool) (σ : WState (LNS (xP xF tw)) LNR)
    (hn : σ.val ⟨320, by decide⟩ = n) (hM : σ.val ⟨440, by decide⟩ = M) (hB : σ.val ⟨441, by decide⟩ = B)
    (hE : σ.val ⟨442, by decide⟩ = err) (hK : σ.val ⟨449, by decide⟩ = K)
    (hL : ∀ c : Fin 4, σ.val ⟨330 + c.val, by have := c.isLt; show 330 + c.val < 512; omega⟩ = Ls c)
    (hblk : ∀ c j, σ.st (tmC xF tw c j) = [] ∧ σ.sh (tmC xF tw c j) = 0)
    (hregs : ∀ q, σ.val q ≤ cap)
    (hlw : ∀ c, (TabW.reqT n M B err (Ls c) 0 K).length ≤ lw) (hcapR : n + 4 * lw + 10 ≤ cap)
    (hwr : ∀ c, WriterIfaceJ.WriterRun Mw (Bud c) win wout (TabW.reqT n M B err (Ls c) 0 K) (vs c)) :
    ∃ τ : WState (LNS (xP xF tw)) LNR, Step (tailM xF tw Mw win) (tailCost cap Bud n lw) (wenc cap σ).H
        (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      (∀ c, τ.st (tmC xF tw c wout) = vs c) ∧
      (∀ c, τ.st (tmC xF tw c win) = frame (TabW.reqT n M B err (Ls c) 0 K)) ∧
      (∀ c j, j ≠ win → j ≠ wout → (τ.st (tmC xF tw c j)).length ≤ Bud c) ∧
      (∀ c j, τ.sh (tmC xF tw c j) = 0) ∧
      (∀ i, (∀ c j, tmC xF tw c j ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ q, τ.val q = 0) ∧ τ.cell = σ.cell := by
  set w : Fin 4 → List Bool := fun c => TabW.reqT n M B err (Ls c) 0 K with hwd
  -- the scratch cleared
  have hsl : scrL.length = 10 := by simp [scrL]
  have e0 := SymDec.clrs_spec cap scrL σ hregs
  rw [hsl] at e0
  set σ0 := SymDec.zeroOut σ scrL with hσ0
  have v0 : ∀ q, σ0.val q = if q ∈ scrL then 0 else σ.val q := fun q => SymDec.zeroOut_val scrL σ q
  have st0 : σ0.st = σ.st := SymDec.zeroOut_st scrL σ
  have sh0 : σ0.sh = σ.sh := SymDec.zeroOut_sh scrL σ
  have cl0 : σ0.cell = σ.cell := SymDec.zeroOut_cell scrL σ
  -- one request
  have req : ∀ (c : Fin 4) (ρ : WState (LNS (xP xF tw)) LNR), ρ.val = σ0.val → ρ.st (tmC xF tw c win) = [] →
      ρ.sh (tmC xF tw c win) = 0 → ∃ m, WExec cap (Sd.reqWM (tmC xF tw c win) (RwC c)) ρ
        (ρ.sets (tmC xF tw c win) (frame (w c))) m ∧ m ≤ Sd.reqCost n lw := by
    intro c ρ hρ hst hsh
    have rv : ∀ k : Fin 16, ρ.val (RwC c k) = σ0.val ⟨rwv c k, rwv_lt c k⟩ := fun k => by rw [hρ]; rfl
    have nz : ∀ k : Fin 16, 1 ≤ k.val → k.val ≤ 9 → ρ.val (RwC c k) = 0 := fun k h1 h9 => by
      rw [rv, v0, if_pos ((mem_scrL _).2 ?_)]
      show 500 ≤ rwv c k ∧ rwv c k ≤ 509
      fin_cases k <;> simp_all [rwv]
    have nv : ∀ (k : Fin 16) (v : ℕ) (hv : v < 512), rwv c k = v → ¬ (500 ≤ v ∧ v ≤ 509) →
        ρ.val (RwC c k) = σ.val ⟨v, hv⟩ := fun k v hv e hn => by
      rw [rv, v0, if_neg (fun h => hn (by rw [mem_scrL] at h; simpa [e] using h))]
      congr 1
      exact Fin.ext e
    obtain ⟨m, e, hm⟩ := Sd.reqWM_spec cap (tmC xF tw c win) (RwC c) n M B err (Ls c) 0 K ρ hst hsh nz
      (by rw [nv 0 320 (by decide) rfl (by omega)]; exact hn)
      (by rw [nv 10 440 (by decide) rfl (by omega)]; exact hM)
      (by rw [nv 11 441 (by decide) rfl (by omega)]; exact hB)
      (by rw [nv 12 442 (by decide) rfl (by omega)]; exact hE)
      (by rw [nv 13 (330 + c.val) (by have := c.isLt; omega) rfl (by have := c.isLt; omega)]; exact hL c)
      (by rw [rv, v0, if_pos ((mem_scrL _).2 (by show 500 ≤ 509 ∧ 509 ≤ 509; omega))])
      (by rw [nv 15 449 (by decide) rfl (by omega)]; exact hK)
      (by have := hlw c; omega)
    refine ⟨m, e, hm.trans ?_⟩
    unfold Sd.reqCost
    have := hlw c
    omega
  -- the four requests
  have hw0 := (hblk 0 win)
  obtain ⟨m1, r1, b1⟩ := req 0 σ0 rfl (by rw [st0]; exact (hblk 0 win).1) (by rw [sh0]; exact (hblk 0 win).2)
  set ρ1 := σ0.sets (tmC xF tw 0 win) (frame (w 0)) with hρ1
  obtain ⟨m2, r2, b2⟩ := req 1 ρ1 rfl
    (by rw [hρ1]; simp only [WState.sets_st]; rw [Function.update_of_ne (tmC_ne xF tw 1 0 (by decide) win win), st0]
        exact (hblk 1 win).1)
    (by rw [hρ1]; simp only [WState.sets_sh]; rw [sh0]; exact (hblk 1 win).2)
  set ρ2 := ρ1.sets (tmC xF tw 1 win) (frame (w 1)) with hρ2
  obtain ⟨m3, r3, b3⟩ := req 2 ρ2 rfl
    (by
      rw [hρ2, hρ1]; simp only [WState.sets_st]
      rw [Function.update_of_ne (tmC_ne xF tw 2 1 (by decide) win win),
        Function.update_of_ne (tmC_ne xF tw 2 0 (by decide) win win), st0]
      exact (hblk 2 win).1)
    (by rw [hρ2, hρ1]; simp only [WState.sets_sh]; rw [sh0]; exact (hblk 2 win).2)
  set ρ3 := ρ2.sets (tmC xF tw 2 win) (frame (w 2)) with hρ3
  obtain ⟨m4, r4, b4⟩ := req 3 ρ3 rfl
    (by
      rw [hρ3, hρ2, hρ1]; simp only [WState.sets_st]
      rw [Function.update_of_ne (tmC_ne xF tw 3 2 (by decide) win win),
        Function.update_of_ne (tmC_ne xF tw 3 1 (by decide) win win),
        Function.update_of_ne (tmC_ne xF tw 3 0 (by decide) win win), st0]
      exact (hblk 3 win).1)
    (by rw [hρ3, hρ2, hρ1]; simp only [WState.sets_sh]; rw [sh0]; exact (hblk 3 win).2)
  set P := ρ3.sets (tmC xF tw 3 win) (frame (w 3)) with hP
  have ePre : WExec cap (preT xF tw win) σ P (10 * (3 * cap + 2) + 1 + (Sd.reqCost n lw + 1 + (Sd.reqCost n lw + 1 +
      (Sd.reqCost n lw + 1 + Sd.reqCost n lw)))) :=
    WExec.mono (WExec.seq e0 (WExec.seq r1 (WExec.seq r2 (WExec.seq r3 r4)))) (by omega)
  have Pval : P.val = σ0.val := rfl
  have Psh : P.sh = σ.sh := by rw [hP, hρ3, hρ2, hρ1]; simp only [WState.sets_sh]; exact sh0
  have Pcell : P.cell = σ.cell := by rw [hP, hρ3, hρ2, hρ1]; simp only [WState.sets_cell]; exact cl0
  have Pst : ∀ i, P.st i = if i = tmC xF tw 3 win then frame (w 3) else if i = tmC xF tw 2 win then frame (w 2) else
      if i = tmC xF tw 1 win then frame (w 1) else if i = tmC xF tw 0 win then frame (w 0) else σ.st i := by
    intro i
    rw [hP, hρ3, hρ2, hρ1]
    simp only [WState.sets_st, Function.update_apply, st0]
  have Pin : ∀ c, P.st (tmC xF tw c win) = frame (w c) := by
    intro c
    rw [Pst]
    fin_cases c <;> simp [tmC_ne xF tw, Ne.symm]
  have Pbl : ∀ c j, j ≠ win → P.st (tmC xF tw c j) = [] := by
    intro c j hj
    have hne : ∀ c', tmC xF tw c j ≠ tmC xF tw c' win := fun c' h => by
      have := tmC_inj' xF tw c c' j win h
      exact hj this.2
    rw [Pst, if_neg (hne 3), if_neg (hne 2), if_neg (hne 1), if_neg (hne 0)]
    exact (hblk c j).1
  have Pout : ∀ i, (∀ c j, tmC xF tw c j ≠ i) → P.st i = σ.st i := by
    intro i hi
    rw [Pst, if_neg (fun h => hi 3 win h.symm), if_neg (fun h => hi 2 win h.symm), if_neg (fun h => hi 1 win h.symm),
      if_neg (fun h => hi 0 win h.symm)]
  -- the four docks
  obtain ⟨J0, hJ0, s0⟩ := dock_one xF tw Mw win cap wout 0 (Bud 0) (w 0) (vs 0) (hwr 0) P (Pin 0) (Pbl 0)
    (fun j => by rw [Psh]; exact (hblk 0 j).2)
  set D0 := DockW.updS (tmC xF tw 0) P (fun _ => 0) (WriterIfaceJ.outBankJ win wout (w 0) (vs 0) J0) with hD0
  obtain ⟨J1, hJ1, s1⟩ := dock_one xF tw Mw win cap wout 1 (Bud 1) (w 1) (vs 1) (hwr 1) D0
    (by rw [hD0, upd_out _ _ _ _ _ _ _ (blk_out xF tw 1 0 (by decide) win)]; exact Pin 1)
    (fun j hj => by rw [hD0, upd_out _ _ _ _ _ _ _ (blk_out xF tw 1 0 (by decide) j)]; exact Pbl 1 j hj)
    (fun j => by rw [hD0, upd_hout _ _ _ _ _ _ _ (blk_out xF tw 1 0 (by decide) j), Psh]; exact (hblk 1 j).2)
  set D1 := DockW.updS (tmC xF tw 1) D0 (fun _ => 0) (WriterIfaceJ.outBankJ win wout (w 1) (vs 1) J1) with hD1
  obtain ⟨J2, hJ2, s2⟩ := dock_one xF tw Mw win cap wout 2 (Bud 2) (w 2) (vs 2) (hwr 2) D1
    (by rw [hD1, upd_out _ _ _ _ _ _ _ (blk_out xF tw 2 1 (by decide) win), hD0,
      upd_out _ _ _ _ _ _ _ (blk_out xF tw 2 0 (by decide) win)]; exact Pin 2)
    (fun j hj => by rw [hD1, upd_out _ _ _ _ _ _ _ (blk_out xF tw 2 1 (by decide) j), hD0,
      upd_out _ _ _ _ _ _ _ (blk_out xF tw 2 0 (by decide) j)]; exact Pbl 2 j hj)
    (fun j => by rw [hD1, upd_hout _ _ _ _ _ _ _ (blk_out xF tw 2 1 (by decide) j), hD0,
      upd_hout _ _ _ _ _ _ _ (blk_out xF tw 2 0 (by decide) j), Psh]; exact (hblk 2 j).2)
  set D2 := DockW.updS (tmC xF tw 2) D1 (fun _ => 0) (WriterIfaceJ.outBankJ win wout (w 2) (vs 2) J2) with hD2
  obtain ⟨J3, hJ3, s3⟩ := dock_one xF tw Mw win cap wout 3 (Bud 3) (w 3) (vs 3) (hwr 3) D2
    (by rw [hD2, upd_out _ _ _ _ _ _ _ (blk_out xF tw 3 2 (by decide) win), hD1,
      upd_out _ _ _ _ _ _ _ (blk_out xF tw 3 1 (by decide) win), hD0,
      upd_out _ _ _ _ _ _ _ (blk_out xF tw 3 0 (by decide) win)]; exact Pin 3)
    (fun j hj => by rw [hD2, upd_out _ _ _ _ _ _ _ (blk_out xF tw 3 2 (by decide) j), hD1,
      upd_out _ _ _ _ _ _ _ (blk_out xF tw 3 1 (by decide) j), hD0,
      upd_out _ _ _ _ _ _ _ (blk_out xF tw 3 0 (by decide) j)]; exact Pbl 3 j hj)
    (fun j => by rw [hD2, upd_hout _ _ _ _ _ _ _ (blk_out xF tw 3 2 (by decide) j), hD1,
      upd_hout _ _ _ _ _ _ _ (blk_out xF tw 3 1 (by decide) j), hD0,
      upd_hout _ _ _ _ _ _ _ (blk_out xF tw 3 0 (by decide) j), Psh]; exact (hblk 3 j).2)
  set D3 := DockW.updS (tmC xF tw 3) D2 (fun _ => 0) (WriterIfaceJ.outBankJ win wout (w 3) (vs 3) J3) with hD3
  -- the registers cleared
  have D3val : D3.val = σ0.val := rfl
  have eC := SymDec.clrs_spec cap (List.finRange LNR) D3 (fun q => by
    rw [D3val, v0]; split
    · omega
    · exact hregs q)
  rw [List.length_finRange] at eC
  set τ := SymDec.zeroOut D3 (List.finRange LNR) with hτ
  have tst : τ.st = D3.st := SymDec.zeroOut_st _ D3
  have tsh : τ.sh = D3.sh := SymDec.zeroOut_sh _ D3
  -- the block contents after the docks
  have O : ∀ c j, τ.st (tmC xF tw c j) = WriterIfaceJ.outBankJ win wout (w c) (vs c)
      (![J0, J1, J2, J3] c) j := by
    intro c j
    rw [tst]
    fin_cases c
    · show D3.st (tmC xF tw 0 j) = _
      rw [hD3, upd_out _ _ _ _ _ _ _ (blk_out xF tw 0 3 (by decide) j), hD2,
        upd_out _ _ _ _ _ _ _ (blk_out xF tw 0 2 (by decide) j), hD1,
        upd_out _ _ _ _ _ _ _ (blk_out xF tw 0 1 (by decide) j), hD0, upd_in]
      rfl
    · show D3.st (tmC xF tw 1 j) = _
      rw [hD3, upd_out _ _ _ _ _ _ _ (blk_out xF tw 1 3 (by decide) j), hD2,
        upd_out _ _ _ _ _ _ _ (blk_out xF tw 1 2 (by decide) j), hD1, upd_in]
      rfl
    · show D3.st (tmC xF tw 2 j) = _
      rw [hD3, upd_out _ _ _ _ _ _ _ (blk_out xF tw 2 3 (by decide) j), hD2, upd_in]
      rfl
    · show D3.st (tmC xF tw 3 j) = _
      rw [hD3, upd_in]
      rfl
  have Oh : ∀ c j, τ.sh (tmC xF tw c j) = 0 := by
    intro c j
    rw [tsh]
    fin_cases c
    · show D3.sh (tmC xF tw 0 j) = 0
      rw [hD3, upd_hout _ _ _ _ _ _ _ (blk_out xF tw 0 3 (by decide) j), hD2,
        upd_hout _ _ _ _ _ _ _ (blk_out xF tw 0 2 (by decide) j), hD1,
        upd_hout _ _ _ _ _ _ _ (blk_out xF tw 0 1 (by decide) j), hD0, upd_hin]
    · show D3.sh (tmC xF tw 1 j) = 0
      rw [hD3, upd_hout _ _ _ _ _ _ _ (blk_out xF tw 1 3 (by decide) j), hD2,
        upd_hout _ _ _ _ _ _ _ (blk_out xF tw 1 2 (by decide) j), hD1, upd_hin]
    · show D3.sh (tmC xF tw 2 j) = 0
      rw [hD3, upd_hout _ _ _ _ _ _ _ (blk_out xF tw 2 3 (by decide) j), hD2, upd_hin]
    · show D3.sh (tmC xF tw 3 j) = 0
      rw [hD3, upd_hin]
  have hJ : ∀ c j, (![J0, J1, J2, J3] c j).length ≤ Bud c := by
    intro c j
    fin_cases c
    · exact hJ0 j
    · exact hJ1 j
    · exact hJ2 j
    · exact hJ3 j
  refine ⟨τ, Step.seq (Step.seq (Step.seq (Step.seq (Step.seq (WExec.exec cap ePre).step s0) s1) s2) s3)
    (WExec.exec cap eC).step, fun c => ?_, fun c => ?_, fun c j h1 h2 => ?_, Oh, fun i hi => ?_, fun q => ?_, ?_⟩
  · rw [O, WriterIfaceJ.outBankJ_out _ _ hio]
  · rw [O, WriterIfaceJ.outBankJ_in]
  · rw [O]
    unfold WriterIfaceJ.outBankJ
    rw [if_neg h1, if_neg h2]
    exact hJ c j
  · have a : ∀ c j, tmC xF tw c j ≠ i := hi
    refine ⟨?_, ?_⟩
    · rw [tst, hD3, upd_out _ _ _ _ _ _ _ (a 3), hD2, upd_out _ _ _ _ _ _ _ (a 2), hD1, upd_out _ _ _ _ _ _ _ (a 1), hD0,
        upd_out _ _ _ _ _ _ _ (a 0)]
      exact Pout i hi
    · rw [tsh, hD3, upd_hout _ _ _ _ _ _ _ (a 3), hD2, upd_hout _ _ _ _ _ _ _ (a 2), hD1,
        upd_hout _ _ _ _ _ _ _ (a 1), hD0, upd_hout _ _ _ _ _ _ _ (a 0), Psh]
  · rw [hτ, SymDec.zeroOut_val, if_pos (List.mem_finRange q)]
  · rw [hτ, SymDec.zeroOut_cell]
    show P.cell = σ.cell
    exact Pcell

end Run

end NearCubicWires.WireExponent3_5.FinalPass.SymF
