import Batteries.Tactic.OpenPrivate
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Std.Tactic
import Proof.Wire_3_5.Assembly.SymStageRoot
import Proof.Wire_3_5.Assembly.SymStageStepB
set_option linter.unusedVariables false
set_option linter.defProp false
namespace PCRootPrefix_adbe25af52b1b3461da8a1b66f614fcb41ac01e370bd4f19f2053b2e92a89404
set_option maxHeartbeats 4000000 in
noncomputable def root
    (thr : (l : NearCubicWires.WireExponent3_5.Literals) →
      NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l →
        NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.ThrLeafJ2 l)
    (c4 : (l : NearCubicWires.WireExponent3_5.Literals) → NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes.C4Leaf l)
    (closureLeaf3 : NearCubicWires.WireExponent3_5.FinalPassStage1.StageT)
    (fronts : (l : NearCubicWires.WireExponent3_5.Literals) →
      @Sigma.{0, 0} Nat fun e =>
        (F : NearCubicWires.WireExponent3_5.Split.GateFree l) →
          NearCubicWires.WireExponent3_5.Split.GateFreeOK l F →
            NearCubicWires.WireExponent3_5.UnionMachine.PlanW3.FrontsFWE3 e l F)
    : NearCubicWires.WireExponent3_5.Literals → NearCubicWires.WireExponent3_5.rowB :=
  (
    (@PCRootPrefix_f093664dce31f53fa3e4d3523a15815e92fde1619ab5b318aa9b46b52ceb1016.root
    (
      (
        (@PCConstruction_09678e6d28c9d37047be4ef4.parent)
      )
    )
    (
      let closureLeaf0 : (
        NearCubicWires.WireExponent3_5.SymStage1.StageT
      ) := (
        (
          (@PCConstruction_09678e6d28c9d37047be4ef4.parent)
        )
      );
      thr
    )
    (
      let closureLeaf0 : (
        NearCubicWires.WireExponent3_5.SymStage1.StageT
      ) := (
        (
          (@PCConstruction_09678e6d28c9d37047be4ef4.parent)
        )
      );
      c4
    )
    (
      let closureLeaf0 : (
        NearCubicWires.WireExponent3_5.SymStage1.StageT
      ) := (
        (
          (@PCConstruction_09678e6d28c9d37047be4ef4.parent)
        )
      );
      closureLeaf3
    )
    (
      let closureLeaf0 : (
        NearCubicWires.WireExponent3_5.SymStage1.StageT
      ) := (
        (
          (@PCConstruction_09678e6d28c9d37047be4ef4.parent)
        )
      );
      fronts
    ))
  )
end PCRootPrefix_adbe25af52b1b3461da8a1b66f614fcb41ac01e370bd4f19f2053b2e92a89404
