import Lean
import Proof.Wire_3_5.Primitive.Writers.SBLay
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.SBCar
import Proof.Wire_3_5.Primitive.Writers.SBIdent
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SBRunBase


noncomputable section
set_option maxRecDepth 4096


/-! # SB, part (3b): SB's machine run and exit state

* `Pof` (the call's star parameters), `sbCost`;
* **`sb_run`**: at a request of the family, from the input frame (every other stream blank, heads, registers `0`, the
  cell `false`), at every capacity `cap ≥ sbNeed`, `sbMach` leaves `SBExit` on `sOutB` (S4's words `4 … 7` in the
  registers' shapes), the input kept, every other stream of length `≤ cap`, heads and registers `0`, within `sbCost`.

Paper quantities of the main type: S4's words `4 … 7` at a star call (`s4Core2`, P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.Data NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarS
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound
open NearCubicWires.WireExponent3_5.PrimAsm.SBNums NearCubicWires.WireExponent3_5.PrimAsm.SBTypes
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.DockW

/-- The call's star parameters (`Call`'s sixth conjunct is `StarAt`). -/
noncomputable def Pof {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
    (r : FReq l F kclk coef A a ha) : Shared.StarParams :=
  (callInputs l F kclk coef A a ha).starParams r.1.n r.2.2.2.2.2.2.1

/-- SB's step bound at a capacity. -/
noncomputable def sbCost (l : Literals) (F : GateFree l) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ) : ℕ :=
  (57600 * (DtC + 1) + 10 ^ 6) * cap ^ 2 + 1 +
    p1Cost cap wl P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg F.cr c0 c1 nc + 1 +
    SBField.fieldCost cap (ellOf P.n) ((SBField.eraseL FsB).map fun i => i.val) + 1 +
    SBInv.clearAllCost cap (List.finRange NRB).length

/-- **SB's run.** -/
theorem sb_run (l : Literals) (hR : SBIdent.StarRStmt l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) (σ : WState nsB NRB)
    (hin : σ.st sInB = frame (fpIn l F kclk coef A a ha r)) (hsh : ∀ i, σ.sh i = 0)
    (hbl : ∀ i, i ≠ sInB → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hc : σ.cell = false) (cap : ℕ)
    (hcap : sbNeed l F.cr F.filterErrDeg (Pof r) r.1.mode (fpIn l F kclk coef A a ha r).length
      (carCnt r.1.carriers 0) (carCnt r.1.carriers 1) r.1.carriers.length ≤ cap) :
    ∃ (τ : WState nsB NRB) (n : ℕ),
      n ≤ sbCost l F (Pof r) r.1.mode (fpIn l F kclk coef A a ha r).length (carCnt r.1.carriers 0)
        (carCnt r.1.carriers 1) r.1.carriers.length cap ∧
      Step (sbMach l F).2 n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      SBExit (Pof r) (capAt l r.1.mode (Pof r)) (F.filterErrDeg * Nat.clog 2 ((Pof r).n + 2))
        (carCnt r.1.carriers 0) (carCnt r.1.carriers 1) r.1.carriers.length τ.st sOutB ∧
      τ.st sInB = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ sInB → (∀ k, i ≠ sOutB k) → (τ.st i).length ≤ cap) ∧ (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  obtain ⟨hrP, -⟩ := hR F kclk coef A a ha r.1.n r.2.2.2.2.2.2.1
  have hrP' : (Pof r).r = Ledger.rowBr F.cr (Pof r).n := hrP
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, hpw, hcS, hcP, hcN, hlam, hwl, hcn, hc0, hc1, hnc, hE6, hE7, hfl, hcar⟩ :=
    need_parts l F.cr F.filterErrDeg (Pof r) r.1.mode _ _ _ _ cap hcap
  -- 1: X6's carrier pipeline, docked
  obtain ⟨τx, m1, hm1, hstep1, hcnt, h6, hkeep, hres, hτs, hτv, hτc⟩ :=
    SBCar.carRunS l F kclk coef A a ha r ⟨fun i => σ.sh (fsX i), fun i => σ.st (fsX i), fun q => σ.val (frX q), σ.cell⟩
      hin (fun i => hsh _) (fun i hi => hbl _ (fun e => hi (fsX_inj e))) (fun q => hv _) hc cap hcar
  have d1 := dockW0 cap fsX frX fsX_inj frX_inj σ _ τx hstep1 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = upd0 fsX frX σ τx := ⟨_, rfl⟩
  rw [← hσ1] at d1
  have st1 : ∀ j, σ1.st (fsX j) = τx.st j := fun j => by
    rw [hσ1]; dsimp only [upd0]; rw [install_slot fsX fsX_inj σ.st τx.st j]
  have st1o : ∀ i, (∀ j, fsX j ≠ i) → σ1.st i = σ.st i := fun i hi => by
    rw [hσ1]; dsimp only [upd0]; rw [install_other fsX σ.st τx.st i hi]
  have sh1 : ∀ i, σ1.sh i = 0 := by
    intro i; rw [hσ1]; dsimp only [upd0]
    by_cases hx : ∃ j, fsX j = i
    · obtain ⟨j, rfl⟩ := hx; rw [dockH_slot fsX fsX_inj σ.sh τx.sh j]; exact hτs j
    · rw [dockH_other fsX σ.sh τx.sh i (fun j e => hx ⟨j, e⟩)]; exact hsh i
  have v1 : ∀ q, σ1.val q = 0 := by
    intro q; rw [hσ1]; dsimp only [upd0]
    by_cases hx : ∃ j, frX j = q
    · obtain ⟨j, rfl⟩ := hx; rw [dockH_slot frX frX_inj σ.val τx.val j]; exact hτv j
    · rw [dockH_other frX σ.val τx.val q (fun j e => hx ⟨j, e⟩)]; exact hv q
  -- 2: P1
  obtain ⟨tl, hw⟩ : ∃ tl, reqW r.1.n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl = fpIn l F kclk coef A a ha r :=
    ⟨_, PrimAsm.ReqBridge.reqW_word r.1 _⟩
  have hsIn : σ1.st sInB = frame (reqW (Pof r).n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl) := by
    rw [show sInB = fsX (oS sIN) from rfl, st1, hkeep]; exact congrArg frame hw.symm
  have hw2 : reqW (Pof r).n (PrimAsm.Codec.modeBit r.1.mode) (PrimAsm.Codec.codeList r.1)
      (r.1.carriers.map Stars.Carrier.code) tl = fpIn l F kclk coef A a ha r := hw
  have hO : ∀ i, (∀ j, fsX j ≠ i) → i ≠ sInB → σ1.st i = [] := fun i hx hi => (st1o i hx).trans (hbl i hi)
  obtain ⟨τ1, e1, q6, q7, qst, qsh, q96, qhi⟩ := p1_run cap sInB cS0 cS1 cS6 o6 o7 o6_ne_o7 F.cr (gateZeta_pos l)
    (gateZeta_lt l) (gateCδ1 l) (gateCap l) r.1.mode F.filterErrDeg (Pof r) hrP (PrimAsm.Codec.codeList r.1)
    (r.1.carriers.map Stars.Carrier.code) tl (carCnt r.1.carriers 0) (carCnt r.1.carriers 1) r.1.carriers.length σ1
    hsIn (sh1 _) (by rw [show cS0 = fsX (oS (sCar 0 5)) from rfl, st1, hcnt 0]; rfl) (sh1 _)
    (by rw [show cS1 = fsX (oS (sCar 1 5)) from rfl, st1, hcnt 1]; rfl) (sh1 _)
    (by rw [show cS6 = fsX (oS Out.CarM2.s6) from rfl, st1, h6]) (sh1 _)
    (hO o6 fsX_ne_o6 (fsX_ne_o6 _).symm) (sh1 _) (hO o7 fsX_ne_o7 (fsX_ne_o7 _).symm) (sh1 _) v1
    (by rw [hw2]; exact hwl) hcn hc0 hc1 hnc hcS hcP (by rw [hrP']; exact capNeed_mode l F.cr r.1.mode _ cap hcN) hlam hpw
    t1 t2 t3 t4 t5 t6 t7 hE6 hE7
  have s2 := Exec.step (WExec.exec cap e1)
  -- 3: the field phase
  have hRb0 : RbB 0 = (96 : Fin NRB) := Fin.ext rfl
  obtain ⟨τ2, s3, f0, f1, fz, fsh, fv, fo, fvo, -⟩ := SBField.field_step cap FsB RbB (ellOf (Pof r).n)
    (by unfold ellOf; omega) τ1 hfl
    (fun k => ⟨(qst _ (FsB_ne_o6 k) (FsB_ne_o7 k)).trans (hO _ (fun j => fsX_ne_FsB j k) (fun e => fsX_ne_FsB _ k e.symm)),
      (qsh _).trans (sh1 _)⟩)
    (by rw [hRb0]; exact q96) (fun j hj => qhi _ (by rw [RbB_val]; have : j.val ≠ 0 := fun e => hj (Fin.ext e); omega))
  -- 4: the register clears
  have hle1 := SBInv.WExec.val_le cap e1 (fun q => by rw [v1 q]; omega)
  have hle : ∀ q, τ2.val q ≤ cap := by
    intro q
    by_cases hq : ∃ j, RbB j = q
    · obtain ⟨j, rfl⟩ := hq; rw [fv j]; omega
    · rw [fvo q (fun j e => hq ⟨j, e⟩)]; exact hle1 q
  obtain ⟨τ3, e4, c3in, -, c3st, c3sh, -⟩ := SBInv.clearAll_spec cap (List.finRange NRB) τ2 hle
  have s4 := Exec.step (WExec.exec cap e4)
  have hN2 : ((fpIn l F kclk coef A a ha r).length + 2) ^ DtC ≤ cap := (pow_two_mul _ _).trans hcar
  refine ⟨τ3, _, ?_, ((d1.seq s2).seq s3).seq s4, ?_, ?_, ?_, ?_, ?_⟩
  · unfold sbCost; rw [hw2]; clear * - hm1; omega
  · intro k
    fin_cases k
    · show τ3.st (sOutB 0) = _
      rw [sOutB_0, c3st, f0]; rfl
    · show τ3.st (sOutB 1) = _
      rw [sOutB_1, c3st, f1]; rfl
    · show τ3.st (sOutB 2) = _
      rw [sOutB_2, c3st, (fo o6 FsB_ne_o6).1, q6]; rfl
    · show τ3.st (sOutB 3) = _
      rw [sOutB_3, c3st, (fo o7 FsB_ne_o7).1, q7]; rfl
  · rw [c3st, (fo sInB (fun k e => fsX_ne_FsB _ k e.symm)).1, show sInB = fsX (oS sIN) from rfl,
      qst _ (fsX_ne_o6 _) (fsX_ne_o7 _), st1, hkeep]
  · intro i hi hk
    rw [c3st]
    by_cases hF : ∃ k, FsB k = i
    · obtain ⟨k, rfl⟩ := hF
      by_cases k0 : k = 0
      · exact absurd (sOutB_0.trans (congrArg FsB k0.symm)).symm (hk 0)
      by_cases k1 : k = 1
      · exact absurd (sOutB_1.trans (congrArg FsB k1.symm)).symm (hk 1)
      rw [fz k (by have := fun e => k0 (Fin.ext e); have := fun e => k1 (Fin.ext e); omega), List.length_replicate]
      exact hfl
    · rw [(fo i (fun k e => hF ⟨k, e⟩)).1, qst i (fun e => hk 2 (e.trans sOutB_2.symm))
        (fun e => hk 3 (e.trans sOutB_3.symm))]
      by_cases hX : ∃ j, fsX j = i
      · obtain ⟨j, rfl⟩ := hX
        rw [st1 j]
        by_cases hj : j = oLog
        · rw [hres j (Or.inr hj), List.length_replicate]; exact hN2
        · obtain ⟨j', rfl⟩ : ∃ j', oS j' = j := ⟨⟨j.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt)
            (fun e => hj (Fin.ext e))⟩, Fin.ext rfl⟩
          by_cases hk' : j' ∈ keepLS
          · simp only [keepLS, List.mem_cons, List.not_mem_nil, or_false] at hk'
            rcases hk' with e | e | e | e <;> subst e
            · exact absurd rfl hi
            · rw [hcnt 0, List.length_replicate]; exact (Nat.le_succ _).trans hc0
            · rw [hcnt 1, List.length_replicate]; exact (Nat.le_succ _).trans hc1
            · rw [h6, List.length_replicate]; exact (Nat.le_succ _).trans hnc
          · rw [hres _ (Or.inl ((mem_eraseOf keepLS _).mpr ⟨j', hk', rfl⟩)), List.length_replicate]; exact hN2
      · rw [st1o i (fun j e => hX ⟨j, e⟩), hbl i hi]; exact Nat.zero_le _
  · intro i
    rw [c3sh]
    by_cases hF : ∃ k, FsB k = i
    · obtain ⟨k, rfl⟩ := hF; exact fsh k
    · rw [(fo i (fun k e => hF ⟨k, e⟩)).2, qsh, sh1]
  · intro q; exact c3in q (List.mem_finRange q)

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
