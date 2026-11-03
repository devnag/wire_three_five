import Lean
import Proof.Wire_3_5.Primitive.Writers.HashFam
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.SeamsUni
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.BudgetIface
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.WritersJoin
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SeamsProg2Base
import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PlanBase
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface3
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase
import Proof.Wire_3_5.UnionMachine.FiltSetupIface5
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJ
import Proof.Wire_3_5.Primitive.Writers.HashLeafBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (HASH (d4)): the HASH writer's leaf

**`hashLeaf : HashLeafOf l`**: from the v3 data stage family (`ThrStage3U l`, uniform constants in StageU's order),
the walk bank, the FILTER setup, `FiltPipeLe2` and `ThrNumsPoly l`, the HASH writer's leaf `WritersJoin.HashLeafJ2 l`.
After `fe`: the floor envelope `envMax E₀ E_H` (`E₀` the floor, `E_H` with `c_ψ = E_tot`, the budget's exponent in
`Q = 2^m + 1`, a function of the exponents only) and the floor `max CD₀ 1`; after `F`: the coefficient `c_W`
(`HashFam.HB.cW`, with the `C₀`, W6's `K_t`, the cap's `capK c_r`, the dimension's `K_H`); at every clock and
source work, the machine `HashFam.hashM` (ShellH's shell at the data stage and PA's HASH unit) and its run
(`hash_fam_run`) within `c_W·classBound` (`hash_fam_cost`).

* `wbC`, `wbD`, `nwC`, `nwD` (the call word's and the `needW` polynomial bounds), `fpK`, `fpD` (`FiltPipeLe2`),
  `tnD`, `tnK` (`ThrNumsPoly`), `hbE` (the exponents), `hbF` (all constants), `hbF_Etot`;
* **`hashLeaf`**.

Paper quantity of the main type: the HASH tape `hashTape` (the auxiliary filter rows of P3:2220-2226) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.HashFam
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierPipeline

/-! ## The producers' constants -/

variable {l : Literals}

noncomputable def tnD (hT : BudgetIface.ThrNumsPoly l) : ℕ := Classical.choose (hT (CallIndexR.capZR l))
noncomputable def tnK (hT : BudgetIface.ThrNumsPoly l) (Cc : ℕ) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (hT (CallIndexR.capZR l)) Cc F)
theorem tn_spec (hT : BudgetIface.ThrNumsPoly l) (Cc : ℕ) (F : GateFree l) :
    ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) {a' : ℕ}
      (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (capT : ℕ),
      a' ≤ 4 → carriers.length ≤ 2 → (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) →
      capT ≤ Cc * (n + 1) ^ CallIndexR.capZR l →
      ∀ v ∈ ThrData.hashNums ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers (gate0 l F).alg
        (callInputs l F kclk coef A a ha).D capT, v ≤ tnK hT Cc F * (n + 1) ^ tnD hT :=
  Classical.choose_spec (Classical.choose_spec (hT (CallIndexR.capZR l)) Cc F)

/-! ## The leaf -/

end NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf

end
