import Lean
import Proof.Wire_3_5.UnionMachine.PlanW2
import Proof.Wire_3_5.UnionMachine.SetupFacts
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.Plan
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.UnionMachine.PlanW2Base
import Proof.Wire_3_5.UnionMachine.SetupFactsBase


noncomputable section
set_option maxRecDepth 120000


/-! # C6: the setup residuals at every exponent margin

`SetupFacts` and `AcceptsCall` of PlanW2 hold at every margin `e`: the proofs of M6
(`WireExponent3_5UnionMachineSetupFacts`) do not read the clock (the setup's language by unfolding `unionSetupS2`, the
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
  · exact setupFacts_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hD_gate l F)
  · exact setupFacts_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hD_gate l F)

/-- **Plan residual `SetupFactsFE`, filled** at every margin. -/
theorem setupFactsFE : ∀ (l : Literals) (e : ℕ), SetupFactsFE l e := fun l e F coef A L hL =>
  setupF_factsE l e F coef A L hL

/-- **Plan residual `AcceptsCallFE`, filled** at every margin. -/
theorem acceptsCallFE : ∀ (l : Literals) (e : ℕ), AcceptsCallFE l e := fun _ _ _ _ _ _ _ P => acceptsCall_of _ P

end NearCubicWires.WireExponent3_5.UnionMachine.SetupFactsE

end
