import Proof.Wire_3_5.Primitive.Writers.UnitReady

/-! # S4 (f1), the tables writer, part 1: a filter seed's table from a FILTER-ready cell (P3:2036-2101)

The unit of S4's tables writer builds the regular filter's table `tableWord (filterTable P e L)` of one seed `e` at
one mask length `L`. From C6's FILTER-ready cell state (`UnitReady.FiltReady`, established by `fsSpec` from `FsIn2`),
the first four stages of PA's FILTER pipeline run as black boxes, composed exactly as in `FiltPipe.filtPipe`: the
modulus (`modStage`), the trace mask (`PrimT.tauW_spec`), the walk (`walkStage`), the stage-6 builder
(`filtBuildStage`). **`tabPre`**: the table on stream `80` with its head at `0`, the FILTER numbers `FR` kept (so
`FR 17 = |table|`), and every stream off the stages' ports kept (the request, the output, the counter, the data).

Paper quantity of the main type: the regular filter's table `tableWord (filterTable P e L)` (P3:2036-2101). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.TabW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierWalk Theorem25Completion
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.FiltPipe NearCubicWires.WireExponent3_5.PrimAsm.UnitReady
open NearCubicWires.WireExponent3_5.FinalPass.Filt NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.PrimAsm.FiltRec
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRecW NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimT.WalkBank

variable (cap : ℕ) (W : WalkBankProducer)

/-- **The table stages' machine**: the modulus, the trace mask, the walk, the stage-6 builder. -/
noncomputable def tabPreM := Composition.machine (Composition.machine (Composition.machine (modDM W.x) (tauM W.x))
  (walkM W)) (filtBuildM W.x)

/-- The table stages' cost. -/
noncomputable def tabPreCost (P : GapParams) (L RW LW : ℕ) : ℕ :=
  PrimAsm.Modulus.modCost P.fieldBits + 1 + PrimT.tauCost P.fieldBits + 1 +
    walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW + 1 +
    (2 * (P.errExp / 4) * (bodyCost P.fieldBits P.labelBits P.prefixBits L 128 RW + 3) + 3 + 1 +
      lastCost P.fieldBits P.labelBits P.prefixBits L 128 (2 * (P.errExp / 4)))

/-- **A seed's table from a FILTER-ready cell.** -/
theorem tabPre (σ : WState (LNS W.x) LNR) (out : List Bool) (P : GapParams) (e : GapSeed P)
    (L r4 G off Mlab RW LW : ℕ)
    (sample : MargulisWalkSample (2 ^ (wOf P.fieldBits P.labelBits * 128)) (2 * (P.errExp / 4) + 1))
    (hr : FiltReady cap W σ out P e L r4 G off Mlab RW LW sample) :
    ∃ σ4 : WState (LNS W.x) LNR,
      Step (tabPreM W) (tabPreCost P L RW LW) (wenc cap σ).H (wenc cap σ).A (wenc cap σ4).H (wenc cap σ4).A ∧
      σ4.st (sk W.x 80) = tableWord (filterTable P e L) ∧ σ4.sh (sk W.x 80) = 0 ∧
      (∀ i : Fin 20, σ4.val (FR i) = σ.val (FR i)) ∧
      (∀ k : Fin 161, k.val ≠ 5 → k.val ≠ 7 → (k.val < 17 ∨ 28 < k.val) → (k.val < 80 ∨ 112 < k.val) →
        σ4.st (sk W.x k) = σ.st (sk W.x k) ∧ σ4.sh (sk W.x k) = σ.sh (sk W.x k)) := by
  have hvert := hr.hvert
  have hU := hr.hU
  have hRW := hr.hRW
  have hLW := hr.hLW
  have hcap6 := hr.hcap6
  have hO6 := hr.hO6
  have hcapT := hr.hcapT
  have hmod := hr.hmod
  have hmsc := hr.hmsc
  have hmh := hr.hmh
  have htau := hr.htau
  have htauR := hr.htauR
  have htauR4 := hr.htauR4
  have hin := hr.hin
  have hh := hr.hh
  have hsc := hr.hsc
  have hsh := hr.hsh
  have hC5 := hr.hC5
  have hC51 := hr.hC51
  have hC5r := hr.hC5r
  have hcell := hr.hcell
  have hm1 := one_le_fieldBits' P
  -- the modulus
  obtain ⟨To1, s1, m82, m82h⟩ := modStage cap σ P.fieldBits hm1 hmod hmsc hmh
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = updS (tmapM W.x) σ (fun _ => 0) To1 := ⟨_, rfl⟩
  rw [← hσ1] at s1 m82 m82h
  have h1o : ∀ k : Fin 161, (k.val ≠ 82 ∧ (k.val < 91 ∨ 107 < k.val)) →
      σ1.st (sk W.x k) = σ.st (sk W.x k) ∧ σ1.sh (sk W.x k) = σ.sh (sk W.x k) := fun k hk => by
    rw [hσ1]
    exact updM_other σ _ _ k hk
  have h1T : ∀ k : Fin W.x, σ1.st (sT W.x k) = σ.st (sT W.x k) ∧ σ1.sh (sT W.x k) = σ.sh (sT W.x k) := fun k => by
    rw [hσ1]
    exact updM_T σ _ _ k
  have h1v : σ1.val = σ.val := by rw [hσ1]; rfl
  have h1c : σ1.cell = σ.cell := by rw [hσ1]; rfl
  -- the trace mask
  have hsmv : ∀ j : Fin 7, 1 ≤ j.val → (smv j).val ≠ 82 ∧ ((smv j).val < 91 ∨ 107 < (smv j).val) := by decide
  obtain ⟨σ2, e2, t81, t81h, t82, tsh, -, -, hWF⟩ := PrimT.tauW_spec cap (SmT W.x) RgT P.fieldBits
    (GF.firstPrimitive P.fieldBits) (GF.firstPrimitive_cert _ hm1) hcapT σ1 m82 m82h
    (((h1o _ (hsmv 1 (by decide))).1).trans (htau 1 (by decide)).1)
    (((h1o _ (hsmv 1 (by decide))).2).trans (htau 1 (by decide)).2)
    (((h1o _ (hsmv 2 (by decide))).1).trans (htau 2 (by decide)).1)
    (((h1o _ (hsmv 2 (by decide))).2).trans (htau 2 (by decide)).2) 0 0 0 0
    (((h1o _ (hsmv 3 (by decide))).1).trans (htau 3 (by decide)).1)
    (((h1o _ (hsmv 3 (by decide))).2).trans (htau 3 (by decide)).2)
    (((h1o _ (hsmv 4 (by decide))).1).trans (htau 4 (by decide)).1)
    (((h1o _ (hsmv 4 (by decide))).2).trans (htau 4 (by decide)).2)
    (((h1o _ (hsmv 5 (by decide))).1).trans (htau 5 (by decide)).1)
    (((h1o _ (hsmv 5 (by decide))).2).trans (htau 5 (by decide)).2)
    (((h1o _ (hsmv 6 (by decide))).1).trans (htau 6 (by decide)).1)
    (((h1o _ (hsmv 6 (by decide))).2).trans (htau 6 (by decide)).2)
    (fun j hj => (congrFun h1v _).trans (htauR j hj)) ((congrFun h1v _).trans htauR4)
  obtain ⟨hWs, hWr, hWc⟩ := hWF
  have h2o : ∀ k : Fin 161, (k.val ≠ 81 ∧ k.val ≠ 82 ∧ (k.val < 108 ∨ 112 < k.val)) →
      σ2.st (sk W.x k) = σ1.st (sk W.x k) ∧ σ2.sh (sk W.x k) = σ1.sh (sk W.x k) :=
    fun k hk => hWs _ (fun ⟨j, hj⟩ => SmT_ne k hk j hj)
  have h2T : ∀ k : Fin W.x, σ2.st (sT W.x k) = σ1.st (sT W.x k) ∧ σ2.sh (sT W.x k) = σ1.sh (sT W.x k) :=
    fun k => hWs _ (fun ⟨j, hj⟩ => SmT_ne_T k j hj)
  have h2v : ∀ r : Fin LNR, (r.val < 219 ∨ 227 < r.val) → σ2.val r = σ1.val r :=
    fun r hr => hWr r (fun ⟨j, hj⟩ => RgT_ne r hr j hj)
  have e2s := (WExec.exec cap e2).step
  -- the walk
  have hpT : ∀ j : Fin 14, (portT j).val ≠ 82 ∧ ((portT j).val < 91 ∨ 107 < (portT j).val) ∧ (portT j).val ≠ 81 ∧
      ((portT j).val < 108 ∨ 112 < (portT j).val) := by decide
  have h12 : ∀ j : Fin 14, σ2.st (sk W.x (portT j)) = σ.st (sk W.x (portT j)) ∧
      σ2.sh (sk W.x (portT j)) = σ.sh (sk W.x (portT j)) := fun j => by
    obtain ⟨a1, a2, a3, a4⟩ := hpT j
    obtain ⟨b1, b2⟩ := h2o _ ⟨a3, a1, a4⟩
    obtain ⟨c1, c2⟩ := h1o _ ⟨a1, a2⟩
    exact ⟨b1.trans c1, b2.trans c2⟩
  obtain ⟨J, -, s3⟩ := walkStage cap W σ2 (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW sample hRW
    hLW (fun j => (h12 j).1.trans (hin j)) (fun j => (h12 j).2.trans (hh j))
    (fun k => ((h2T k).1.trans (h1T k).1).trans (hsc k)) (fun k => ((h2T k).2.trans (h1T k).2).trans (hsh k))
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = updS (tmapT W.x) σ2 (Fin.addCases (motive := fun _ => ℕ)
      (outHeads (2 * (P.errExp / 4))) (fun _ => 0)) (Fin.addCases (motive := fun _ => List Bool)
      (outPorts (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW sample) J) := ⟨_, rfl⟩
  have s3' : Step (walkM W) (walkBankCost (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW)
      (wenc cap σ2).H (wenc cap σ2).A (wenc cap σ3).H (wenc cap σ3).A := by
    rw [hσ3]
    exact s3
  have h3o : ∀ k : Fin 161, (∀ j : Fin 14, portT j ≠ k) →
      σ3.st (sk W.x k) = σ2.st (sk W.x k) ∧ σ3.sh (sk W.x k) = σ2.sh (sk W.x k) := fun k hk => by
    rw [hσ3]
    exact ⟨updT_st_other σ2 _ _ k hk, updT_sh_other σ2 _ _ k hk⟩
  have h3pst : ∀ j : Fin 14, σ3.st (sk W.x (portT j)) =
      outPorts (wOf P.fieldBits P.labelBits * 128) (2 * (P.errExp / 4)) RW LW sample j :=
    fun j => by rw [hσ3, updT_st_port, Fin.addCases_left]
  have h3psh : ∀ j : Fin 14, σ3.sh (sk W.x (portT j)) = outHeads (2 * (P.errExp / 4)) j :=
    fun j => by rw [hσ3, updT_sh_port, Fin.addCases_left]
  have h3v : σ3.val = σ2.val := by rw [hσ3]; rfl
  have h3c : σ3.cell = σ2.cell := by rw [hσ3]; rfl
  -- a stream no stage before the table touches
  have hkeep : ∀ k : Fin 161, (k.val ≠ 5 ∧ k.val ≠ 7 ∧ (k.val < 17 ∨ 28 < k.val) ∧ k.val ≠ 81 ∧ k.val ≠ 82 ∧
      (k.val < 91 ∨ 112 < k.val)) → σ3.st (sk W.x k) = σ.st (sk W.x k) ∧ σ3.sh (sk W.x k) = σ.sh (sk W.x k) :=
    fun k hk => by
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hk
      obtain ⟨b1, b2⟩ := h3o k (fun j h => by
        have := portT_le j
        have := portT_ge j
        have hj := congrArg Fin.val h
        have hT : ∀ j : Fin 14, (portT j).val = 5 ∨ (portT j).val = 7 ∨ (17 ≤ (portT j).val ∧ (portT j).val ≤ 28) := by
          decide
        rcases hT j with h' | h' | h' <;> omega)
      obtain ⟨c1, c2⟩ := h2o k ⟨a4, a5, by omega⟩
      obtain ⟨d1, d2⟩ := h1o k ⟨a5, by omega⟩
      exact ⟨b1.trans (c1.trans d1), b2.trans (c2.trans d2)⟩
  -- the table
  have hst4 : ∀ i, σ3.st (fsF W.x i) = (yFC P L RW LW sample).st i := by
    intro i
    by_cases i0 : i.val = 0
    · have : i = 0 := Fin.ext i0
      subst this
      rw [show fsF W.x 0 = sk W.x (portT 0) from congrArg (sk W.x) (Fin.ext rfl), h3pst]
      rfl
    · by_cases i1 : i.val = 1
      · have : i = 1 := Fin.ext i1
        subst this
        rw [show fsF W.x 1 = sk W.x 80 from congrArg (sk W.x) (Fin.ext rfl),
          (hkeep 80 (by decide)).1, hC51.1, yFC_st1]
      · by_cases i2 : i.val = 2
        · have : i = 2 := Fin.ext i2
          subst this
          rw [show fsF W.x 2 = sk W.x 81 from congrArg (sk W.x) (Fin.ext rfl),
            (h3o 81 (by decide)).1, show sk W.x 81 = SmT W.x 1 from rfl, t81]
          rfl
        · by_cases i3 : i.val = 3
          · have : i = 3 := Fin.ext i3
            subst this
            rw [show fsF W.x 3 = sk W.x 82 from congrArg (sk W.x) (Fin.ext rfl),
              (h3o 82 (by decide)).1, show sk W.x 82 = SmT W.x 0 from rfl, t82, show SmT W.x 0 = sk W.x 82 from rfl, m82]
            rfl
          · have hi4 : 4 ≤ i.val := by omega
            have ev : fsF W.x i = sk W.x ⟨79 + i.val, by omega⟩ :=
              congrArg (sk W.x) (Fin.ext (by show (if i.val = 0 then 5 else 79 + i.val) = 79 + i.val; rw [if_neg i0]))
            rw [ev, (hkeep _ ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega, by simp; omega,
              by simp; omega⟩).1, ← ev]
            exact (hC5 i hi4).1
  have hsh4 : ∀ i, σ3.sh (fsF W.x i) = (yFC P L RW LW sample).sh i := by
    intro i
    rw [yFC_sh]
    by_cases i0 : i.val = 0
    · have : i = 0 := Fin.ext i0
      subst this
      rw [show fsF W.x 0 = sk W.x (portT 0) from congrArg (sk W.x) (Fin.ext rfl), h3psh]
      rfl
    · by_cases i1 : i.val = 1
      · have : i = 1 := Fin.ext i1
        subst this
        rw [show fsF W.x 1 = sk W.x 80 from congrArg (sk W.x) (Fin.ext rfl), (hkeep 80 (by decide)).2, hC51.2]
      · by_cases i2 : i.val = 2
        · have : i = 2 := Fin.ext i2
          subst this
          rw [show fsF W.x 2 = sk W.x 81 from congrArg (sk W.x) (Fin.ext rfl), (h3o 81 (by decide)).2]
          exact tsh 1
        · by_cases i3 : i.val = 3
          · have : i = 3 := Fin.ext i3
            subst this
            rw [show fsF W.x 3 = sk W.x 82 from congrArg (sk W.x) (Fin.ext rfl), (h3o 82 (by decide)).2]
            exact tsh 0
          · have hi4 : 4 ≤ i.val := by omega
            have ev : fsF W.x i = sk W.x ⟨79 + i.val, by omega⟩ :=
              congrArg (sk W.x) (Fin.ext (by show (if i.val = 0 then 5 else 79 + i.val) = 79 + i.val; rw [if_neg i0]))
            rw [ev, (hkeep _ ⟨by simp; omega, by simp; omega, by simp; omega, by simp; omega, by simp; omega,
              by simp; omega⟩).2, ← ev]
            exact (hC5 i hi4).2
  have hv4 : ∀ r, σ3.val (frC r) = (yFC P L RW LW sample).val r := fun r => by
    rw [h3v, h2v _ (Or.inl (by have := r.isLt; show r.val < 219; omega)), h1v]
    exact hC5r r
  have s4 := filtBuildStage cap W.x σ3 P e L RW LW hU sample hvert hRW hLW hcap6 hO6 hsh4 hst4 hv4
    (by rw [h3c, hWc, h1c, hcell])
    (fun k => by rw [show emF W.x k = sk W.x (portT ⟨k.val + 1, by omega⟩) from rfl, h3psh, outHeads_bank1])
    (fun k => by rw [show emF W.x k = sk W.x (portT ⟨k.val + 1, by omega⟩) from rfl, h3pst, outPorts_bank1])
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = updW (fsF W.x) frC (emF W.x) σ3
      (finalW P.fieldBits P.labelBits P.prefixBits L (tauWord P) (modWord P)
        (WalkTimeLoop.A RW LW sample [] (2 * (P.errExp / 4)) 0) (tableWord (filterTable P e L)))
      (Fin.addCases (m := 7) (n := 1) (motive := fun _ => ℕ)
        (fun k => WalkTimeLoop.H (2 * (P.errExp / 4)) (2 * (P.errExp / 4)) k.succ) (fun _ => 1))
      (Fin.addCases (m := 7) (n := 1) (motive := fun _ => List Bool)
        (fun k => WalkTimeLoop.A RW LW sample [] (2 * (P.errExp / 4)) k.succ)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word (2 * (P.errExp / 4)))) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have h4o : ∀ k : Fin 161, (k.val ≠ 5 ∧ k.val ≠ 7 ∧ (k.val < 17 ∨ 23 < k.val) ∧ (k.val < 80 ∨ 90 < k.val)) →
      σ4.st (sk W.x k) = σ3.st (sk W.x k) ∧ σ4.sh (sk W.x k) = σ3.sh (sk W.x k) := fun k hk => by
    rw [hσ4]
    exact ⟨updF_st_other σ3 _ _ _ k hk, updF_sh_other σ3 _ _ _ k hk⟩
  have h4tab : σ4.st (sk W.x 80) = tableWord (filterTable P e L) ∧ σ4.sh (sk W.x 80) = 0 := by
    rw [hσ4, show sk W.x 80 = fsF W.x 1 from congrArg (sk W.x) (Fin.ext rfl), updF_st_fs, updF_sh_fs]
    exact ⟨rfl, by simp [finalW]⟩
  have hFR : ∀ i : Fin 20, σ4.val (FR i) = σ.val (FR i) := fun i => by
    have hv : (FR i).val = 230 + i.val := rfl
    rw [hσ4, updF_val_other σ3 _ _ _ _ (by rw [hv]; omega), h3v, h2v _ (Or.inr (by rw [hv]; omega)), h1v]
  refine ⟨σ4, Step.seq (Step.seq (Step.seq s1 e2s) s3') s4, h4tab.1, h4tab.2, hFR, fun k k5 k7 k17 k80 => ?_⟩
  obtain ⟨b1, b2⟩ := h4o k ⟨k5, k7, by omega, by omega⟩
  obtain ⟨c1, c2⟩ := hkeep k ⟨k5, k7, k17, by omega, by omega, by omega⟩
  exact ⟨b1.trans c1, b2.trans c2⟩

end NearCubicWires.WireExponent3_5.FinalPass.TabW
