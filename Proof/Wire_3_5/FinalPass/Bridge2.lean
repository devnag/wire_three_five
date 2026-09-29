import Proof.Wire_3_5.FinalPass.Bridge1

/-! # BridgeT, part 2: S4 as the seeds phase on the shared bank (P3:3170-3181)

**`bridgeT X mT mC mI K0 D0 : SeedsProg4`** from S4's machine-level program `X : SeedsWS2`: the cell step, then S4
focused onto its tapes of the bank (`e4`), at the bank's register capacity `max X.Kc K0 · N^{max X.Dc D0}` (S4's run
zero-padded from its own capacity, base `Step.pad`). From the front's exit (`FrontOut`) S4's entry holds
(`SdEntry2`: the words, `Num = 0`, `Den`, blank streams, zero registers, cell `false`); its exit gives the numerator
and denominator on the number tapes, and the idle room is kept (**`bridge_run`**). The seeds phase's time is S4's plus
two steps (`ov + 2`, **`ov_le2`**).

Paper quantity of the main type: the seeds phase's printed numerator and denominator (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bridge
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other install_existing)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj rTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Br
variable {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {Sw : SymWords}
  (X : SeedsWS2 l F kclk coef A a ha Sw) (mT mC mI K0 D0 : ℕ)

/-- S4's register capacity at a request. -/
noncomputable abbrev capX (r : FReq l F kclk coef A a ha) : ℕ :=
  X.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ X.Dc

/-- The bank's register capacity at a request. -/
noncomputable abbrev capY (r : FReq l F kclk coef A a ha) : ℕ :=
  max X.Kc K0 * ((fpIn l F kclk coef A a ha r).length + 1) ^ max X.Dc D0

theorem capX_le (r : FReq l F kclk coef A a ha) : capX X r ≤ capY X K0 D0 r := by
  have hN : 1 ≤ (fpIn l F kclk coef A a ha r).length + 1 := by omega
  exact Nat.mul_le_mul (le_max_left _ _) (Nat.pow_le_pow_right hN (le_max_left _ _))

/-- S4's conclusion from an entry state `σ`. -/
def QX (r : FReq l F kclk coef A a ha) (W : ℕ) (σ τ : WState X.L.ns X.L.nr) : Prop :=
  Step X.M (seedsShape (seedCount l F kclk coef A a ha r) (X.tab r) (ptCount l F kclk coef A a ha r) (X.pt r) (X.ov r))
      (wenc (capX X r) σ).H (wenc (capX X r) σ).A (wenc (capX X r) τ).H (wenc (capX X r) τ).A ∧
    τ.st X.L.sN = frame (binary W (fpNum l F kclk coef A a ha r)) ∧
    τ.st X.L.sD = frame (binary W (fpDen l F kclk coef A a ha r)) ∧
    (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧ fpNum l F kclk coef A a ha r < 2 ^ W

/-- S4's exit state at the bank's entry (chosen). -/
noncomputable def τOf (Ab : FReq l F kclk coef A a ha → Fin (tB X.L.ns X.L.nr mT mC mI) → List Bool)
    (W : FReq l F kclk coef A a ha → ℕ) (r : FReq l F kclk coef A a ha) : WState X.L.ns X.L.nr := by
  classical
  exact if h : ∃ τ, QX X r (W r) (σIn X.L.ns X.L.nr mT mC mI (Ab r)) τ then Classical.choose h
    else σIn X.L.ns X.L.nr mT mC mI (Ab r)

/-- **The seeds phase's exit bank.** -/
noncomputable def exitB (Ab : FReq l F kclk coef A a ha → Fin (tB X.L.ns X.L.nr mT mC mI) → List Bool)
    (W : FReq l F kclk coef A a ha → ℕ) (r : FReq l F kclk coef A a ha) : Fin (tB X.L.ns X.L.nr mT mC mI) → List Bool :=
  install (e4 X.L.ns X.L.nr mT mC mI) (Function.update (Ab r) (cellB X.L.ns X.L.nr mT mC mI) [false])
    (fun j => ZeroPadding.pad (pc X.L.ns X.L.nr (capY X K0 D0 r) j) ((wenc (capX X r) (τOf X mT mC mI Ab W r)).A j))

theorem pc_s (c' : ℕ) (i : Fin (X.L.ns + 1)) : pc X.L.ns X.L.nr c' (sTape (nr := X.L.nr) i) = 0 := by
  unfold pc; rw [if_neg (by rw [PrimAsm.DockW.sTape_val]; have := i.isLt; split_ifs <;> omega)]

theorem dockH0 : dockH (e4 X.L.ns X.L.nr mT mC mI) (fun _ => 0) (fun _ => 0) = fun _ => 0 := by
  funext i
  by_cases h : ∃ j, e4 X.L.ns X.L.nr mT mC mI j = i
  · obtain ⟨j, rfl⟩ := h
    exact dockH_slot _ (e4_inj X.L.ns X.L.nr mT mC mI) _ _ j
  · exact dockH_other _ _ _ i (fun j e => h ⟨j, e⟩)

/-- **S4 as the seeds phase on the shared bank.** -/
theorem bridge_run (H : FReq l F kclk coef A a ha → Fin (tB X.L.ns X.L.nr mT mC mI) → ℕ)
    (Ab : FReq l F kclk coef A a ha → Fin (tB X.L.ns X.L.nr mT mC mI) → List Bool) (W : FReq l F kclk coef A a ha → ℕ)
    (hF : FrontOut l F kclk coef A a ha (fun k => e4 X.L.ns X.L.nr mT mC mI (sTape (X.L.wdS k)))
      ![e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN), e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD)]
      (frontWordsW2 l F kclk coef A a ha Sw) (fun r => ![0, fpDen l F kclk coef A a ha r]) W
      (fun r j => if regB X.L.ns X.L.nr mT mC mI j then
        max X.Kc K0 * ((fpIn l F kclk coef A a ha r).length + 1) ^ max X.Dc D0 + 1 else 0) H Ab)
    (hW : ∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r) (r : FReq l F kclk coef A a ha) :
    Step (Composition.machine (cellP X.L.ns X.L.nr mT mC mI).compile
        (RecoveryFocus.machine (e4 X.L.ns X.L.nr mT mC mI) X.M))
        (seedsShape (seedCount l F kclk coef A a ha r) (X.tab r) (ptCount l F kclk coef A a ha r) (X.pt r) (X.ov r + 2))
        (H r) (Ab r) (fun _ => 0) (exitB X mT mC mI K0 D0 Ab W r) ∧
      exitB X mT mC mI K0 D0 Ab W r (e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN)) =
        frame (binary (W r) (fpNum l F kclk coef A a ha r)) ∧
      exitB X mT mC mI K0 D0 Ab W r (e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD)) =
        frame (binary (W r) (fpDen l F kclk coef A a ha r)) ∧
      fpNum l F kclk coef A a ha r < 2 ^ W r ∧
      ∀ j, idleB X.L.ns X.L.nr mT mC mI j = true → exitB X mT mC mI K0 D0 Ab W r j = Ab r j := by
  have hH := hF.heads r
  have hNum : Ab r (e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN)) = frame (binary (W r) 0) := by
    simpa using hF.nums r 0
  have hDen : Ab r (e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD)) =
      frame (binary (W r) (fpDen l F kclk coef A a ha r)) := by
    simpa using hF.nums r 1
  have hnm : ∀ (j : Fin (X.L.ns + 2 + X.L.nr)), j ≠ sTape X.L.sN → j ≠ sTape X.L.sD → ∀ i : Fin 2,
      e4 X.L.ns X.L.nr mT mC mI j ≠
        ![e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN), e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD)] i := by
    intro j hN hD i e
    fin_cases i
    · exact hN (e4_inj X.L.ns X.L.nr mT mC mI (by simpa using e))
    · exact hD (e4_inj X.L.ns X.L.nr mT mC mI (by simpa using e))
  have hcellb : Ab r (cellB X.L.ns X.L.nr mT mC mI) = [] := by
    rw [hF.blank r (cellB X.L.ns X.L.nr mT mC mI) (fun k e => sTape_ne_c _ (e4_inj X.L.ns X.L.nr mT mC mI e).symm)
      (hnm _ (fun e => sTape_ne_c _ e.symm) (fun e => sTape_ne_c _ e.symm)), if_neg (by rw [regB_c]; decide)]
    rfl
  have hreg : ∀ q : Fin X.L.nr, Ab r (e4 X.L.ns X.L.nr mT mC mI (rTape q)) =
      List.replicate (capY X K0 D0 r + 1) false := by
    intro q
    rw [hF.blank r _ (fun k e => sTape_ne_r _ q (e4_inj X.L.ns X.L.nr mT mC mI e).symm)
      (hnm _ (fun e => sTape_ne_r _ q e.symm) (fun e => sTape_ne_r _ q e.symm)), if_pos (regB_r _ _ _ _ _ q)]
  have hent : SdEntry2 l F kclk coef A a ha X.L r (W r) (σIn X.L.ns X.L.nr mT mC mI (Ab r)) := by
    refine ⟨fun k => hF.words r k, hNum, hDen, fun i hw hN hD => ?_, fun _ => rfl, fun _ => rfl, rfl⟩
    show Ab r (e4 X.L.ns X.L.nr mT mC mI (sTape i)) = []
    rw [hF.blank r _ (fun k e => hw k (sTape_inj (e4_inj X.L.ns X.L.nr mT mC mI e)))
      (hnm _ (fun e => hN (sTape_inj e)) (fun e => hD (sTape_inj e))),
      if_neg (by rw [regB_s]; decide)]
    rfl
  have hQ : ∃ τ, QX X r (W r) (σIn X.L.ns X.L.nr mT mC mI (Ab r)) τ := X.run r (W r) (hW r) _ hent
  have hτ : QX X r (W r) (σIn X.L.ns X.L.nr mT mC mI (Ab r)) (τOf X mT mC mI Ab W r) := by
    unfold τOf; rw [dif_pos hQ]; exact Classical.choose_spec hQ
  obtain ⟨hstep, hN, hD, hsh, hval, hnum⟩ := hτ
  have hp := hstep.pad (pc X.L.ns X.L.nr (capY X K0 D0 r))
  rw [pad_entry X.L.ns X.L.nr mT mC mI (capX X r) (capY X K0 D0 r) (capX_le X K0 D0 r) (Ab r) hreg,
    wenc_H0 X.L.ns X.L.nr _ _ (fun _ => rfl) (fun _ => rfl), wenc_H0 X.L.ns X.L.nr _ _ hsh hval] at hp
  have hf := hp.focus (e4 X.L.ns X.L.nr mT mC mI) (e4_inj X.L.ns X.L.nr mT mC mI) (fun _ => 0)
    (Function.update (Ab r) (cellB X.L.ns X.L.nr mT mC mI) [false])
  rw [dockH0, install_existing _ _ _ (fun j => rfl)] at hf
  have hs := Step.seq (cell_step X.L.ns X.L.nr mT mC mI (Ab r) hcellb) hf
  refine ⟨?_, ?_, ?_, hnum, fun j hj => ?_⟩
  · rw [hH]
    exact hs.enlarge (by unfold seedsShape; omega)
  · show install _ _ _ _ = _
    rw [install_slot _ (e4_inj X.L.ns X.L.nr mT mC mI), pc_s, ZeroPadding.pad_zero, wenc_A_s]
    exact hN
  · show install _ _ _ _ = _
    rw [install_slot _ (e4_inj X.L.ns X.L.nr mT mC mI), pc_s, ZeroPadding.pad_zero, wenc_A_s]
    exact hD
  · have hjv : 1 + (X.L.ns + 2 + X.L.nr) + mT + mC ≤ j.val := by simpa [idleB] using hj
    have hne : ∀ q, e4 X.L.ns X.L.nr mT mC mI q ≠ j := fun q e => by
      have h1 := congrArg Fin.val e
      rw [e4_val] at h1
      have := q.isLt
      omega
    have hc : j ≠ cellB X.L.ns X.L.nr mT mC mI := fun e => by
      have h1 := congrArg Fin.val e
      rw [cellB_val] at h1
      omega
    show install _ _ _ _ = _
    rw [install_other _ _ _ _ hne, Function.update_of_ne hc]

/-- The seeds phase's overhead within its bound (two steps: the cell step and the bridge). -/
theorem ov_le2 (r : FReq l F kclk coef A a ha) :
    X.ov r + 2 ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (X.Co + 2) X.Do r := by
  have h1 := X.ov_le r
  have h2 := PrimAsm.S5Seam.one_le_s5Bound l F kclk coef A a ha 1 X.Do le_rfl r
  have e : PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (X.Co + 2) X.Do r =
      PrimAsm.S5Seam.s5Bound l F kclk coef A a ha X.Co X.Do r +
        2 * PrimAsm.S5Seam.s5Bound l F kclk coef A a ha 1 X.Do r := by
    unfold PrimAsm.S5Seam.s5Bound; ring
  omega

end Br

end NearCubicWires.WireExponent3_5.FinalPass.Bridge
