import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellIface

/-! # The writers' unit machine with two arbitrary pipes (generalize `CellUnit.unitM` ONCE)

PA's `CellUnit.unitM W decW` (decode ; branch on the flag streams `150` (POP) / `151` (FILTER) ; counter increment) has
its two pipes hard-wired. The THR writer's unit branches on the registers `398` (RADIX) / `399` (FILTER) of the decode
front (`ThrDec.ThrDecOut`) into its own pipes. Here, once, for any decode machine and any two pipes selected by two
registers:

* **`PipeOK cap P σ out e Bp`**: the pipe `P` runs from `σ` within `Bp`, prints `e` on the output (head on the closing
  `false`), and keeps the request (stream `0`) and the counter (stream `2`);
* **`unitMG dec r₁ r₂ P₁ P₂`** = `dec ; branchM (r₁ ≠ 0) P₁ (branchM (r₂ ≠ 0) P₂ idle) ; incW`;
* **`DecOKG`**: the decode's exit: both flags `0` and `e` printed, or `r₁ ≠ 0` and `PipeOK P₁`, or `r₁ = 0`,
  `r₂ ≠ 0` and `PipeOK P₂`;
* **`unit_stepG`** (the unit's run from the decode's), **`unitOK_ofG`** (`Shell.UnitOK` from the decode's run).

Paper quantity of the main type: the unit's printed body `e` on the writer's output (one unit of the THR tape). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.UnitG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.PrimAsm.CellLoop

variable (cap : ℕ) {x : ℕ}

/-- **A pipe's run at a state**: within `Bp`, the unit's body `e` printed, the request and the counter kept. -/
def PipeOK {s : ℕ} (P : Machine (TT x) s) (σ : WState (LNS x) LNR) (out e : List Bool) (Bp : ℕ) : Prop :=
  ∃ σF : WState (LNS x) LNR, Step P Bp (wenc cap σ).H (wenc cap σ).A (wenc cap σF).H (wenc cap σF).A ∧
    σF.st (sk x 0) = σ.st (sk x 0) ∧ σF.st (sk x 1) = out ++ e ++ [false] ∧ σF.sh (sk x 1) = (out ++ e).length ∧
    σF.st (sk x 2) = σ.st (sk x 2) ∧ σF.sh (sk x 2) = σ.sh (sk x 2)

/-- **The unit machine with two pipes**: the decode, the branch on `r₁ ≠ 0` (pipe 1), else on `r₂ ≠ 0` (pipe 2), else
nothing, then the counter increment. -/
noncomputable def unitMG {s₀ s₁ s₂ : ℕ} (dec : Machine (TT x) s₀) (r₁ r₂ : Fin LNR) (P₁ : Machine (TT x) s₁)
    (P₂ : Machine (TT x) s₂) :=
  Composition.machine (Composition.machine dec
    (Block.branchM (rTape (ns := LNS x) (nr := LNR) r₁) P₁
      (Block.branchM (rTape (ns := LNS x) (nr := LNR) r₂) P₂ (Block.idle (LNS x + 2 + LNR)))))
    (CellUnit.incW x).toProg.compile

/-- **What the decode leaves** for the two-pipe unit. -/
def DecOKG {s₁ s₂ : ℕ} (r₁ r₂ : Fin LNR) (P₁ : Machine (TT x) s₁) (P₂ : Machine (TT x) s₂)
    (σ : WState (LNS x) LNR) (out e : List Bool) (Bp : ℕ) : Prop :=
  (σ.val r₁ = 0 ∧ σ.val r₂ = 0 ∧ σ.st (sk x 1) = out ++ e ++ [false] ∧ σ.sh (sk x 1) = (out ++ e).length) ∨
  (σ.val r₁ ≠ 0 ∧ PipeOK cap P₁ σ out e Bp) ∨
  (σ.val r₁ = 0 ∧ σ.val r₂ ≠ 0 ∧ PipeOK cap P₂ σ out e Bp)

theorem bit_reg (σ : WState (LNS x) LNR) (r : Fin LNR) :
    readTapeBit ((wenc cap σ).A (rTape r)) ((wenc cap σ).H (rTape r)) = decide (σ.val r ≠ 0) := by
  rw [wenc_A_r, wenc_H_r, regTape_read]

theorem inc_keep (σ : WState (LNS x) LNR) (j : ℕ) (k : Fin 161) (hk : k ≠ 2) :
    ((σ.seth (sk x 2) j).sets (sk x 2) (List.replicate (j + 1) true)).st (sk x k) = σ.st (sk x k) ∧
    ((σ.seth (sk x 2) j).sets (sk x 2) (List.replicate (j + 1) true)).sh (sk x k) = σ.sh (sk x k) := by
  have hne : sk x k ≠ sk x 2 := fun e => hk (sk_inj x e)
  simp [hne]

/-- **One unit**: from the decode's run to a `DecOKG` state (request and counter at head `0`), the unit machine prints
the unit's body `e` and increments the counter. -/
theorem unit_stepG {s₀ s₁ s₂ : ℕ} (dec : Machine (TT x) s₀) (r₁ r₂ : Fin LNR) (P₁ : Machine (TT x) s₁)
    (P₂ : Machine (TT x) s₂) (σ0 σD : WState (LNS x) LNR) (m j Bp : ℕ) (out e w : List Bool)
    (hdec : Step dec m (wenc cap σ0).H (wenc cap σ0).A (wenc cap σD).H (wenc cap σD).A)
    (hok : DecOKG cap r₁ r₂ P₁ P₂ σD out e Bp) (hIN : σD.st (sk x 0) = frame w)
    (hCTR : σD.st (sk x 2) = List.replicate j true) (hCTRh : σD.sh (sk x 2) = 0) :
    ∃ σE : WState (LNS x) LNR, Step (unitMG dec r₁ r₂ P₁ P₂) (m + 1 + (Bp + 4) + 1 + (3 * j + 3))
        (wenc cap σ0).H (wenc cap σ0).A (wenc cap σE).H (wenc cap σE).A ∧
      σE.st (sk x 0) = frame w ∧ σE.st (sk x 1) = out ++ e ++ [false] ∧ σE.sh (sk x 1) = (out ++ e).length ∧
      σE.st (sk x 2) = List.replicate (j + 1) true := by
  have n02 : (0 : Fin 161) ≠ 2 := by decide
  have n12 : (1 : Fin 161) ≠ 2 := by decide
  rcases hok with ⟨f1, f2, ho, hoh⟩ | ⟨f1, σF, sF, i0, o1, o1h, c2, c2h⟩ | ⟨f1, f2, σF, sF, i0, o1, o1h, c2, c2h⟩
  · have hbr := Block.branch_false (rTape (ns := LNS x) (nr := LNR) r₁) P₁
      (Block.branch_false (rTape (ns := LNS x) (nr := LNR) r₂) P₂
        (ListMachine.Print.idle_step (wenc cap σD).H (wenc cap σD).A) (by rw [bit_reg]; simp [f2]))
      (by rw [bit_reg]; simp [f1])
    have si := (WExec.exec cap (CellUnit.incW_spec cap σD j hCTR hCTRh)).step
    refine ⟨_, Step.seq (Step.seq hdec (hbr.enlarge (by omega))) si, ?_, ?_, ?_, by simp⟩
    · rw [(inc_keep σD j 0 n02).1, hIN]
    · rw [(inc_keep σD j 1 n12).1, ho]
    · rw [(inc_keep σD j 1 n12).2, hoh]
  · have hbr := Block.branch_true (rTape (ns := LNS x) (nr := LNR) r₁)
      (Block.branchM (rTape (ns := LNS x) (nr := LNR) r₂) P₂ (Block.idle (LNS x + 2 + LNR))) sF
      (by rw [bit_reg]; simp [f1])
    have si := (WExec.exec cap (CellUnit.incW_spec cap σF j (c2.trans hCTR) (c2h.trans hCTRh))).step
    refine ⟨_, Step.seq (Step.seq hdec (hbr.enlarge (by omega))) si, ?_, ?_, ?_, by simp⟩
    · rw [(inc_keep σF j 0 n02).1, i0, hIN]
    · rw [(inc_keep σF j 1 n12).1, o1]
    · rw [(inc_keep σF j 1 n12).2, o1h]
  · have hbr := Block.branch_false (rTape (ns := LNS x) (nr := LNR) r₁) P₁
      (Block.branch_true (rTape (ns := LNS x) (nr := LNR) r₂) (Block.idle (LNS x + 2 + LNR)) sF
        (by rw [bit_reg]; simp [f2])) (by rw [bit_reg]; simp [f1])
    have si := (WExec.exec cap (CellUnit.incW_spec cap σF j (c2.trans hCTR) (c2h.trans hCTRh))).step
    refine ⟨_, Step.seq (Step.seq hdec (hbr.enlarge (by omega))) si, ?_, ?_, ?_, by simp⟩
    · rw [(inc_keep σF j 0 n02).1, i0, hIN]
    · rw [(inc_keep σF j 1 n12).1, o1]
    · rw [(inc_keep σF j 1 n12).2, o1h]

/-- **`Shell.UnitOK` for the two-pipe unit** from its decode's run on the unit's fresh cell to `DecOKG`, within the
budget. -/
theorem unitOK_ofG {s₀ s₁ s₂ : ℕ} (dec : Machine (TT x) s₀) (r₁ r₂ : Fin LNR) (P₁ : Machine (TT x) s₁)
    (P₂ : Machine (TT x) s₂) (nU : ℕ) (w u : List Bool) (emit : ℕ → List Bool) (j : ℕ) (out : List Bool)
    (h : ∃ (σD : WState (LNS x) LNR) (m Bp : ℕ),
      Step dec m (wenc cap (CellLoopD.blankCellD x w out j u)).H (wenc cap (CellLoopD.blankCellD x w out j u)).A
        (wenc cap σD).H (wenc cap σD).A ∧
      DecOKG cap r₁ r₂ P₁ P₂ σD out (emit j) Bp ∧ σD.st (sk x 0) = frame w ∧
      σD.st (sk x 2) = List.replicate j true ∧ σD.sh (sk x 2) = 0 ∧
      CellLoopD.cpCost u.length + 1 + (m + 1 + (Bp + 4) + 1 + (3 * j + 3)) ≤ nU) :
    PrimThrW.Shell.UnitOK cap x (unitMG dec r₁ r₂ P₁ P₂) nU w u emit j out := by
  obtain ⟨σD, m, Bp, hd, hok, hIN, hC, hCh, hn⟩ := h
  obtain ⟨σE, sU, e0, e1, e1h, e2⟩ :=
    unit_stepG cap dec r₁ r₂ P₁ P₂ (CellLoopD.blankCellD x w out j u) σD m j Bp out (emit j) w hd hok hIN hC hCh
  exact ⟨σE, _, sU, e0, e1, e1h, e2, hn⟩

end NearCubicWires.WireExponent3_5.UnionMachine.UnitG
