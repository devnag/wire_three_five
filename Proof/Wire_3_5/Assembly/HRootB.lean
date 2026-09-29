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
import Proof.Wire_3_5.Assembly.C4Step
import Proof.Wire_3_5.Assembly.FinalPassStageStep
import Proof.Wire_3_5.Assembly.HRootA
import Proof.Wire_3_5.Assembly.HStepB
set_option linter.unusedVariables false
set_option linter.defProp false
namespace PCRootPrefix_156cc33d77aa06172477eda9b5ffea8358a77775d9dc7519bbcb1a3cf0e025d4
set_option maxHeartbeats 4000000 in
noncomputable def root
    (thr : (l : NearCubicWires.WireExponent3_5.Literals) →
      NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l →
        NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.ThrLeafJ2 l)
    (closureLeaf1 : NearCubicWires.WireExponent3_5.C4Stage1.StageT)
    (closureLeaf2 : NearCubicWires.WireExponent3_5.FinalPassStage2.StageT)
    : NearCubicWires.WireExponent3_5.Literals → NearCubicWires.WireExponent3_5.rowB :=
  (
    (@PCRootPrefix_adbe25af52b1b3461da8a1b66f614fcb41ac01e370bd4f19f2053b2e92a89404.root
    (
      thr
    )
    (
      (
        let h : (
          NearCubicWires.WireExponent3_5.C4Stage1.StageT
        ) := (
          closureLeaf1
        );
        (@PCConstruction_46ff96c04d4a39bb659376b8.parent h)
      )
    )
    (
      let c4 : (
        (l : NearCubicWires.WireExponent3_5.Literals) → NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes.C4Leaf l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.C4Stage1.StageT
          ) := (
            closureLeaf1
          );
          (@PCConstruction_46ff96c04d4a39bb659376b8.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.FinalPassStage2.StageT
        ) := (
          closureLeaf2
        );
        (@PCConstruction_2d060017f4daa86c091a9f8c.parent h)
      )
    )
    (
      let c4 : (
        (l : NearCubicWires.WireExponent3_5.Literals) → NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes.C4Leaf l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.C4Stage1.StageT
          ) := (
            closureLeaf1
          );
          (@PCConstruction_46ff96c04d4a39bb659376b8.parent h)
        )
      );
      let closureLeaf3 : (
        NearCubicWires.WireExponent3_5.FinalPassStage1.StageT
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.FinalPassStage2.StageT
          ) := (
            closureLeaf2
          );
          (@PCConstruction_2d060017f4daa86c091a9f8c.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.FrontsStage1.StageT
        ) := (
          (
            (@PCConstruction_89d1a2ea36cd1a6d6bc54fd4.parent)
          )
        );
        (@PCConstruction_068fa2fbf8d8fa52d4605891.parent h)
      )
    ))
  )
end PCRootPrefix_156cc33d77aa06172477eda9b5ffea8358a77775d9dc7519bbcb1a3cf0e025d4
