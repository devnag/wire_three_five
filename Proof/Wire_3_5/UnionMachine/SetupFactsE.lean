import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.SetupFacts

/-! # C6: the setup residuals at every exponent margin

`SetupFacts` and `AcceptsCall` of PlanW2 hold at every margin `e` (clock `kclk = gateDver + e`): the proofs of M6
(`Proof.Wire_3_5.UnionMachine.SetupFacts`) do not read the clock (the setup's language by unfolding `unionSetupS2`, the
width's growth, the outer error, and `hD_gate` at the gate's grid; an accepting guess's admissible call). Main
statements: **`setupFactsFE`**, **`acceptsCallFE`**. Paper quantity: the setup's language, outer error, width growth
and propagated error (P3:3490-3491), and the accepting guess's call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SetupFactsE
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.UnionMachine.Plan NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
open NearCubicWires.WireExponent3_5.UnionMachine.SetupFacts Filter

/-- **The setup facts at the pinned setup `S₂`**, both branches, at margin `e`. -/
theorem setupF_factsE (l : Literals) (e : ℕ) (F : GateFree l) (coef A : ℕ) (L : Language)
    (hL : InNTIME (fun n => n ^ (kE l e + 2)) L) : SetupFacts (SUE l F e coef A L hL) L := by
  unfold SUE setupF unionSetupS2
  split
  · exact setupFacts_of_result _ _ _ _ _ _ _ _ _ _ _ _ _
      (tendsto_atTop_mono (fun N => le_max_right _ _) (Ledger.tendsto_nativeWidth _ _)) (outer_pos l) (hD_gate l F)
  · exact setupFacts_of_result _ _ _ _ _ _ _ _ _ _ _ _ _
      (tendsto_atTop_mono (fun N => le_max_right _ _) (Ledger.tendsto_nativeWidth _ _)) (outer_pos l) (hD_gate l F)

/-- **Plan residual `SetupFactsFE`, filled** at every margin. -/
theorem setupFactsFE : ∀ (l : Literals) (e : ℕ), SetupFactsFE l e := fun l e F coef A L hL =>
  setupF_factsE l e F coef A L hL

/-- **Plan residual `AcceptsCallFE`, filled** at every margin. -/
theorem acceptsCallFE : ∀ (l : Literals) (e : ℕ), AcceptsCallFE l e := fun _ _ _ _ _ _ _ P => acceptsCall_of _ P


end NearCubicWires.WireExponent3_5.UnionMachine.SetupFactsE
