import Proof.Wire_3_5.UnionMachine.RadSetupB3
import Proof.Wire_3_5.Primitive.Writers.RadPipe

/-! # The RADIX pipe at Route B's capacities — the of `RadSetupB3`

P3:2585-2623 (row:radix). The RADIX pipe `RadPipe.radPipeM` (C2's RADIX row machine docked on the cell, then the
output head back) runs, from `RadSetupB3.RadReadyB2` (the Route-B record `frame q.record` on stream `3`, the output
`out ++ [false]`, the pipe's scratch `portP 30 … 76` blank because they lie below `130`, `r.Pre`, the capacity
conditions `q.Caps`), C2's parametric row `ListMachine.Row.radRow_step` at `(q.R, q.Lg, q.cap)` and the row's specs
`radSpecs` (`RadSetupB.caps_step`), on the record `radRowRec … = q.record` (`RadSetupB.record_eq`).

* **`radRowStageB`**: the row stage at Route B: the output becomes `out ++ exprWord (radRefC …)`;
* **`radPipe_readyB`**: the pipe's run from `RadReadyB2` within `q.bound + 2` steps (output `out ++ body ++ [false]`,
  its head after the body; the request, the counter and the data kept).

Paper quantity of the main type: the RADIX row's printed reference (`radRefC`, whose value is
`[Σ_d b_0^d(t_d^+ − t_d^−) ≡ s (mod p)]`, P3:2608-2618). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadPipeB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.PopPipe
open NearCubicWires.WireExponent3_5.PrimAsm.RadPipe
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB3

variable (cap : ℕ) {x : ℕ}

/-- The Route-B row cost: C2's parametric row cost at `(q.R, q.Lg, q.cap)` and the row's specs. -/
noncomputable def radRowCostB (q : RadReqB) (hok : DigsOk q.r.digs) : ℕ :=
  radRowCost q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0) (radT q.r.digs q.r.p q.r.s) q.R q.Lg
    q.cap (radSpecs q.r.D q.r.digs hok)

/-- **The RADIX row stage at Route B**: C2's parametric row on the cell layout, from the Route-B record on the record
stream and the output `out ++ [false]` at `|out|`: the output becomes `out ++ exprWord (radRefC …)`. -/
theorem radRowStageB (σ : WState (LNS x) LNR) (q : RadReqB) (hpre : q.r.Pre) (hc : q.Caps) (out : List Bool)
    (hrec : σ.st (sk x 3) = frame q.record) (hrec0 : σ.sh (sk x 3) = 0) (hout : σ.st (sk x 1) = out ++ [false])
    (houth : σ.sh (sk x 1) = out.length)
    (hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      σ.st (tmapQ x j) = [] ∧ σ.sh (tmapQ x j) = 0) :
    ∃ Ho To, Step (radRowDM x) (radRowCostB q hpre.1)
        (wenc cap σ).H (wenc cap σ).A (wenc cap (updS (tmapQ x) σ Ho To)).H (wenc cap (updS (tmapQ x) σ Ho To)).A ∧
      (updS (tmapQ x) σ Ho To).st (sk x 1) =
        out ++ ListMachine.Rec.exprWord (radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s) ∧
      (updS (tmapQ x) σ Ho To).sh (sk x 1) =
        (out ++ ListMachine.Rec.exprWord (radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s)).length := by
  obtain ⟨hdig, hnest, hτ, hs⟩ := hpre
  haveI : NeZero q.r.p := ⟨by omega⟩
  obtain ⟨hRx, hst, hmsel⟩ := caps_step q hdig hc
  have hxlen : (radSpecs q.r.D q.r.digs hdig).length = 2 * q.r.digs.length * (q.r.D.M + 1) :=
    radSpecs_length q.r.D q.r.digs hdig
  have hmp : (radSpecs q.r.D q.r.digs hdig).map FSpec.poly = radFs q.r.D q.r.digs := by
    rw [radSpecs_poly q.r.D q.r.digs hdig []]; rfl
  obtain ⟨A', hrun, -, hA'⟩ := radRow_step (negFam F35) q.r.D.M (2 * q.r.digs.length)
    (radCs q.r.D q.r.digs q.r.p q.r.b0) (radT q.r.digs q.r.p q.r.s) (radSpecs q.r.D q.r.digs hdig) (by omega)
    (by simp [radCs]) hxlen [] [] out (out ++ [false]) q.R q.Lg q.cap hc.R2 hRx hc.RL hst hc.c1 hmsel hc.c3
  have ho : radOut q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0) (radT q.r.digs q.r.p q.r.s)
      ((radSpecs q.r.D q.r.digs hdig).map FSpec.poly) = ListMachine.Rec.exprWord (radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s) := by
    rw [hmp, radT_eq q.r.digs q.r.p q.r.s hs]
    exact radOut_eq q.r.digs.length q.r.D.M q.r.p q.r.b0 (radPp q.r.D q.r.digs) (radPm q.r.D q.r.digs) (q.r.s : ZMod q.r.p)
  rw [ho, record_eq q hdig] at hrun
  rw [ho] at hA'
  have eH : (fun i => Fin.addCases (motive := fun _ => ℕ) (qH (negFam F35).t ([] : List Bool).length
      (popH (negFam F35).t 0 ![0, 0, 0, 0, 0, 0, out.length, 0])) (fun _ : Fin 1 => 0) i) =
        fun j => σ.sh (tmapQ x j) := by
    funext i; exact congrFun (popRow_entryH σ out hrec0 houth hscr) i
  have eA : (fun i => Fin.addCases (motive := fun _ => List Bool) (qA (negFam F35).t
      ([] ++ frame q.record ++ []) (entryA (negFam F35).t out (out ++ [false])))
      (fun _ : Fin 1 => []) i) = fun j => σ.st (tmapQ x j) := by
    funext i; exact congrFun (popRow_entryA σ _ out hrec hout hscr) i
  have hs' : Step (radRowM (negFam F35)) (radRowCostB q hdig) (fun j => σ.sh (tmapQ x j))
      (fun j => σ.st (tmapQ x j))
      (fun i => Fin.addCases (motive := fun _ => ℕ) (qH (negFam F35).t (([] : List Bool).length +
        (2 * q.record.length + 1)) (popH (negFam F35).t
          ((fieldsWord (setupFieldsG (negFam F35).t q.R q.Lg (radEv q.r.D.M (2 * q.r.digs.length)
            (radCs q.r.D q.r.digs q.r.p q.r.b0) (radT q.r.digs q.r.p q.r.s) q.cap))).length +
            ((radSpecs q.r.D q.r.digs hdig).flatMap fun x => true :: x.block).length)
          ![0, 0, 0, 0, 0, 0, (out ++ ListMachine.Rec.exprWord (radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s)).length, 0]))
        (fun _ : Fin 1 => 0) i) A' := by
    rw [← eH, ← eA]
    exact hrun
  refine ⟨_, A', dockS cap (tmapQ x) tmapQ_inj σ hs', ?_, ?_⟩
  · show install (tmapQ x) σ.st A' (sk x 1) = _
    rw [← tmapQ_out (x := x), install_slot _ tmapQ_inj, hA', overlay_ext out _ (exprWord_len _)]
  · dsimp only [updS]
    rw [← tmapQ_out (x := x), dockH_slot _ tmapQ_inj, Fin.addCases_left, qH_p, popH_eI]
    rfl

/-- **The RADIX pipe at Route B, run** from `RadReadyB2`: the output `out ++ body ++ [false]` with its head after the
body (`body` the row's printed reference expression), the request, the counter and the data kept, within
`q.bound + 2` steps. -/
theorem radPipe_readyB (σ : WState (LNS x) LNR) (w out : List Bool) (j : ℕ) (u : List Bool) (q : RadReqB)
    (h : RadReadyB2 x σ w out j u q) :
    ∃ σF m, Step (radPipeM x) m (wenc cap σ).H (wenc cap σ).A (wenc cap σF).H (wenc cap σF).A ∧
      σF.st (sk x 1) = out ++ (radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s).flatMap
        (fun t => true :: ListMachine.Rec.termWord t) ++ [false] ∧
      σF.sh (sk x 1) = (out ++ (radRefC q.r.D q.r.digs q.r.p q.r.b0 q.r.s).flatMap
        (fun t => true :: ListMachine.Rec.termWord t)).length ∧
      (∀ k : Fin 161, (k.val = 0 ∨ k.val = 2 ∨ k.val = 113) →
        σF.st (sk x k) = σ.st (sk x k) ∧ σF.sh (sk x k) = σ.sh (sk x k)) ∧
      m ≤ q.bound + 2 := by
  have hscr : ∀ j : Fin (IPL (negFam F35).t + 1), j.val ≠ 0 → j.val ≠ 45 →
      σ.st (tmapQ x j) = [] ∧ σ.sh (tmapQ x j) = 0 := by
    intro j j0 j45
    have e : tmapQ x j = sk x (portP (Fin.cast IPL1 j)) := rfl
    have hj := j.isLt
    have h47 := IPL_val
    rw [e]
    apply h.blank <;> rw [portP_val, Fin.val_cast] <;> split_ifs <;> omega
  obtain ⟨Ho, To, sE, hE1, hE2⟩ := radRowStageB cap σ q h.pre h.caps out h.s3 h.h3 h.s1 h.h1 hscr
  have eF := WExec.bwd (cap := cap) (sk x 1) (updS (tmapQ x) σ Ho To)
  have sF := (WExec.exec cap eF).step
  have hcost : radRowCostB q h.pre.1 ≤ q.bound := by
    obtain ⟨hdig, hnest, hτ, hs⟩ := h.pre
    obtain ⟨hRx, hst, hmsel⟩ := caps_step q hdig h.caps
    have hb := radRowCost_bound q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0)
      (radT q.r.digs q.r.p q.r.s) q.R q.Lg q.cap (radSpecs q.r.D q.r.digs hdig) hst h.caps.c1 hmsel h.caps.c3
    rw [record_eq q hdig] at hb
    exact hb
  refine ⟨_, _, Step.seq sE sF, ?_, ?_, ?_, ?_⟩
  · simp only [WState.seth_st]
    rw [hE1, exprWord_eq, List.append_assoc]
  · simp only [WState.seth_sh, Function.update_self]
    rw [hE2, exprWord_eq]
    simp
  · intro k hk
    have n1 : sk x k ≠ sk x 1 := fun e => by
      have := congrArg Fin.val (sk_inj x e)
      rcases hk with hk | hk | hk <;> simp_all
    refine ⟨?_, ?_⟩
    · simp only [WState.seth_st]
      show install (tmapQ x) σ.st To (sk x k) = _
      rw [install_other _ _ _ _ (tmapQ_ne3 k hk)]
    · simp only [WState.seth_sh, Function.update_apply, if_neg n1]
      show dockH (tmapQ x) σ.sh Ho (sk x k) = _
      rw [dockH_other _ _ _ _ (tmapQ_ne3 k hk)]
  · unfold RadReqB.bound at hcost ⊢
    omega

end NearCubicWires.WireExponent3_5.UnionMachine.RadPipeB
