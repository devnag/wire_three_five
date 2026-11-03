import Lean
import Proof.Wire_3_5.Outer35.CallCount
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.UnionMachine.UnionCheck
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.UnionMachine.Plan
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.UnionMachine.UnionCallCountBase


noncomputable section
set_option maxRecDepth 120000


/-! # The union's call count at the pinned setup (paper v2, Lemma H.7(b), (58))

At the pinned setup `S₂ = unionSetupS2` and the clock `kclk`: every guess passing the outer step's guards schedules at
most `q(N)^{unionCallDeg l}` primitive calls, eventually in `N` (`setupF_calls_le`), where `q(N)` is the ledger's width.
At the recovered language the setup is `recSetup2` (the refuter's hierarchy, `𝒱_G = gateSV`, live) and the count is the
generic `Outer35`-level `calls_le_of` at the size exponent `capExp l` (so `e_H = eH l`); off it the setup is dead
(`live = false`) and no guess passes the guards.

Paper quantity of the main type: **the number of scheduled primitive calls** against **`q(N)^{unionCallDeg l}`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.UnionCallCount
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleDepth)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open Filter

section Pinned
variable (l : Literals) (G : Split.Gate) (coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- `S₂` off the recovered language is the dead `S₁`. -/
theorem unionSetupS2_ne (kc : ℕ) (ha' : a ≤ kc + 1) (L : Language) (hL : InNTIME (fun n => n ^ (kc + 2)) L)
    (h : L ≠ recL l kc) : unionSetupS2 l G kc coef A a ha' L hL = unionSetupS1 l G kc coef A a ha' L hL := by
  unfold unionSetupS2
  rw [dif_neg h]

/-- The size exponent of the recovered setup is `e_H` (`lenG l + 3 = capExp l + 2`). -/
theorem eHS_rec : eHS (recSetup2 l G kclk coef A a ha) (capExp l) = eH l := by
  have h1 := one_le_capExp l
  unfold eHS eH eC lenG
  show (capExp l - 1 + 3) * _ + capExp l + 1 = (capExp l + 2) * _ + capExp l + 1
  rw [show capExp l - 1 + 3 = capExp l + 2 by omega]
  rfl

/-- **The union's call count at `S₂`** (Lemma H.7(b), (58)): at the gate's `A_pad`, every language of the clock,
eventually in `N`, every guess passing the outer step's guards schedules at most `q(N)^{unionCallDeg l}` primitive
calls. -/
theorem unionCalls_le (hApad : G.Apad = gateApad l) (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (unionSetupS2 l G kclk coef A a ha L hL) z),
      UnionGuards (unionSetupS2 l G kclk coef A a ha L hL) z g → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ (G.budget kclk coef A a ha).q N ^ unionCallDeg l := by
  by_cases h : L = recL l kclk
  · subst h
    rw [unionSetupS2_recL]
    have hq : Tendsto (G.budget kclk coef A a ha).q atTop atTop := tendsto_nativeWidth kclk G.Apad
    have hc := calls_le_of (recSetup2 l G kclk coef A a ha) (capExp l) (fun o w ho => oracleSize_le l w o ho)
      (G.budget kclk coef A a ha).q hq G.row.Csp G.row.sp_le
      (Filter.Eventually.of_forall (fun N => recSetup2_width l G coef A a ha hApad N))
    rw [eHS_rec] at hc
    exact hc
  · rw [unionSetupS2_ne l G coef A a kclk ha L hL h]
    refine Filter.Eventually.of_forall (fun N z g hg => ?_)
    exact absurd hg.1 (by rw [unionSetupS1_live]; decide)

/-- **The call count at the concrete gate**: at `setupF l F`, for every choice `F` of the free constants. -/
theorem setupF_calls_le (F : Split.GateFree l) (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    ∀ᶠ N in atTop, ∀ (z : BitInput N) (g : UnionGuess (Split.setupF l F kclk coef A a ha L hL) z),
      UnionGuards (Split.setupF l F kclk coef A a ha L hL) z g → ∀ tr : List ℕ,
        (g.checkData tr).schedule.length ≤ ((Split.gate0 l F).budget kclk coef A a ha).q N ^ unionCallDeg l :=
  unionCalls_le l (Split.gate0 l F) coef A a ha rfl L hL

/-- **`CallCountF`** (the residual of the union plan) from the call count. -/
theorem callCountF : UnionMachine.Plan.CallCountF l :=
  fun coef A a ha F L hL => setupF_calls_le l coef A a ha F L hL

end Pinned

end NearCubicWires.WireExponent3_5.Transfer.UnionCallCount

end
