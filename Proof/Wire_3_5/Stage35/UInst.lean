import ENP.UStage
import Proof.Wire_3_5.Stage35.Bundle

-- Port of W3 Recovery3/UInst.lean with the copies schedule (Stage35.WQ).

/-!
# O7, stages 1 and 3 in the terms of the gadget transfer

The near-cubic-gates paper's uniform recovery (sec:all-lengths, E^NP paragraph): "First, a formula over the description of `B_src` with the `N`
constraints (eq:source-check) … finds the first source circuit `B*_src`, or shows that there is none … Third, a formula
over the description of `B_pf` with the `2^{ℓ_out}` constraints `B_pf(a0^{q−ℓ_out}) = O*(a)` … finds the first
`B*_pf`, or shows that there is none." `ENP.UStage.stage_run` instantiated at `d = G` (`g.degree`), `R = q`
(`g.width s ν`): stage 1 on `vals = z` decides `g.SrcExists s ν z` and returns the description of `g.firstSrc`;
stage 3 on `vals = O*` (`= List.ofFn t`, the stage-2 table) decides the small-oracle condition of `g.matchPCP` and
returns the description of its canonical oracle — `B*_pf` of `g.selectedPair` in Case 2. The cap is `g.bound s ν`
(definitionally `oracleSizeBound g.degree (g.width s ν)`).
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.UInst

open Stage35 _root_.NearCubicGates.Close

open W3.Recovery3 NearCubicGates.Close.Recovery NearCubicGates.Close.ENP

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.RecoveryChoice NearCubicWires.OuterPCPRecovery NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.Transfer NearCubicWires.SourceInterfaces NearCubicWires.ExecutableInterfaces

/-- **Stage 1** (the near-cubic-gates paper's uniform recovery): the flag is `SrcExists`, the description is that of `B*_src = firstSrc`. -/
theorem stage1_run (s : WS35) (g : WQ) (ν : ℕ) (z : BitInput (2 ^ ν)) (post : List Bool) (W : ℕ)
    (hb : 0 < g.bound s ν)
    (hW : originalWorkspace (g.width s ν) (g.bound s ν) (List.ofFn z).length (List.ofFn z).length ≤ W)
    (hsource : (DedupBytes.fields (unitPCP ν (List.ofFn z))).length ≤ W) (htwo : 2 ^ g.width s ν ≤ W) :
    ∃ c ≤ UStage.cost g.degree ν (g.width s ν) W (List.ofFn z) (g.nu_lt_width s ν).le z, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (UStage.program g.degree) c
        (initialConfiguration (UStage.program g.degree).base.machine
          (UStage.input g.degree (RepairOrdinary.frame (List.ofFn z) ++ post) (g.width s ν) W)) final ∧
      (UStage.program g.degree).base.machine.halted final.control = true ∧
      (readTapeBit (final.tapes (UStage.flagPort g.degree)) 0 = true ↔ g.SrcExists s ν z) ∧
      (∀ h : g.SrcExists s ν z, final.tapes (UStage.descPort g.degree) =
        RepairOrdinary.frame (canonicalBoundedCircuitDescription (g.bound s ν) (g.firstSrc s ν z h))) ∧
      (final.tapes (UStage.queryPort g.degree)).length ≤ c ∧ final.heads (UStage.queryPort g.degree) = 0 := by
  obtain ⟨c, hc, final, tr, hal, hflag, hdesc, hq, hqh⟩ := UStage.stage_run g.degree (List.ofFn z) post ν
    (g.width s ν) W (by simp) (g.nu_lt_width s ν).le z hb hW hsource htwo
  refine ⟨c, hc, final, tr, hal, ?_, fun h => hdesc h, hq, hqh⟩
  rw [hflag, caseTwo_true]
  rfl

/-- **Stage 3** (the near-cubic-gates paper's uniform recovery): on the first honest table `t`, the flag is the small-oracle condition of the match PCP
(Case 2 given stages 1–2), the description is that of its canonical oracle. -/
theorem stage3_run (s : WS35) (g : WQ) (ν : ℕ) (z : BitInput (2 ^ ν)) {ℓ : ℕ}
    (hℓ : ℓ ≤ g.width s ν) (t : BitInput (2 ^ ℓ)) (post : List Bool) (W : ℕ)
    (hb : 0 < g.bound s ν)
    (hW : originalWorkspace (g.width s ν) (g.bound s ν) (List.ofFn t).length (List.ofFn t).length ≤ W)
    (hsource : (DedupBytes.fields (unitPCP ℓ (boolFunctionTable (tableOracle t)))).length ≤ W)
    (htwo : 2 ^ g.width s ν ≤ W) :
    ∃ c ≤ UStage.cost g.degree ℓ (g.width s ν) W (boolFunctionTable (tableOracle t)) hℓ z, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (UStage.program g.degree) c
        (initialConfiguration (UStage.program g.degree).base.machine
          (UStage.input g.degree (RepairOrdinary.frame (List.ofFn t) ++ post) (g.width s ν) W)) final ∧
      (UStage.program g.degree).base.machine.halted final.control = true ∧
      (readTapeBit (final.tapes (UStage.flagPort g.degree)) 0 = true ↔
        SmallOracle (g.matchPCP s ν hℓ t) g.degree z) ∧
      (∀ small : SmallOracle (g.matchPCP s ν hℓ t) g.degree z, final.tapes (UStage.descPort g.degree) =
        RepairOrdinary.frame (canonicalBoundedCircuitDescription (g.bound s ν)
          (oracleSelector (g.matchPCP s ν hℓ t) g.degree z small).circuit)) ∧
      (final.tapes (UStage.queryPort g.degree)).length ≤ c ∧ final.heads (UStage.queryPort g.degree) = 0 := by
  have hv := boolFunctionTable_tableOracle t
  obtain ⟨c, hc, final, tr, hal, hflag, hdesc, hq, hqh⟩ := UStage.stage_run g.degree
    (boolFunctionTable (tableOracle t)) post ℓ (g.width s ν) W (by rw [hv]; simp) hℓ z hb (by rw [hv]; exact hW)
    hsource htwo
  rw [hv] at tr
  refine ⟨c, hc, final, tr, hal, ?_, fun small => hdesc small, hq, hqh⟩
  rw [hflag, caseTwo_true]
  rfl


end NearCubicGates.Close.Recovery3.UInst

