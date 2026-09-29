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
import Proof.Wire_3_5.Assembly.FinalPassStep
import Proof.Wire_3_5.Assembly.HashStage2Root
import Proof.Wire_3_5.Assembly.HashStage2StepB
import Proof.Wire_3_5.Assembly.SymStep
set_option linter.unusedVariables false
set_option linter.defProp false
namespace PCRootPrefix_f093664dce31f53fa3e4d3523a15815e92fde1619ab5b318aa9b46b52ceb1016
set_option maxHeartbeats 4000000 in
noncomputable def root
    (closureLeaf0 : NearCubicWires.WireExponent3_5.SymStage1.StageT)
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
    (@PCRootPrefix_b353c5238d2006956ce747179d7901e6119abbd855b5e69b02bf1fd6b5c71b67.root
    (
      (
        let h : (
          NearCubicWires.WireExponent3_5.SymStage1.StageT
        ) := (
          closureLeaf0
        );
        (@PCConstruction_f7e4c97fdda6e750864859b3.parent h)
      )
    )
    (
      let sym : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.SymStage1.StageT
          ) := (
            closureLeaf0
          );
          (@PCConstruction_f7e4c97fdda6e750864859b3.parent h)
        )
      );
      thr
    )
    (
      let sym : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.SymStage1.StageT
          ) := (
            closureLeaf0
          );
          (@PCConstruction_f7e4c97fdda6e750864859b3.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.HashStage1.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.HashStage2.StageT
            ) := (
              (
                (@PCConstruction_4934cec25217d8b596812df0.parent)
              )
            );
            (@PCConstruction_990907c85579f4bbb8787230.parent h)
          )
        );
        (@PCConstruction_230b3ab139509cd6eb4edffa.parent h)
      )
    )
    (
      let sym : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.SymStage1.StageT
          ) := (
            closureLeaf0
          );
          (@PCConstruction_f7e4c97fdda6e750864859b3.parent h)
        )
      );
      let hash : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.HashLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.HashStage1.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.HashStage2.StageT
              ) := (
                (
                  (@PCConstruction_4934cec25217d8b596812df0.parent)
                )
              );
              (@PCConstruction_990907c85579f4bbb8787230.parent h)
            )
          );
          (@PCConstruction_230b3ab139509cd6eb4edffa.parent h)
        )
      );
      c4
    )
    (
      let sym : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.SymStage1.StageT
          ) := (
            closureLeaf0
          );
          (@PCConstruction_f7e4c97fdda6e750864859b3.parent h)
        )
      );
      let hash : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.HashLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.HashStage1.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.HashStage2.StageT
              ) := (
                (
                  (@PCConstruction_4934cec25217d8b596812df0.parent)
                )
              );
              (@PCConstruction_990907c85579f4bbb8787230.parent h)
            )
          );
          (@PCConstruction_230b3ab139509cd6eb4edffa.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.FinalPassStage1.StageT
        ) := (
          closureLeaf3
        );
        (@PCConstruction_b0ff58edc98d546e181650fc.parent h)
      )
    )
    (
      let sym : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.SymLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.SymStage1.StageT
          ) := (
            closureLeaf0
          );
          (@PCConstruction_f7e4c97fdda6e750864859b3.parent h)
        )
      );
      let hash : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l → NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.HashLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.HashStage1.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.HashStage2.StageT
              ) := (
                (
                  (@PCConstruction_4934cec25217d8b596812df0.parent)
                )
              );
              (@PCConstruction_990907c85579f4bbb8787230.parent h)
            )
          );
          (@PCConstruction_230b3ab139509cd6eb4edffa.parent h)
        )
      );
      let s5 : (
        ∀ l : NearCubicWires.WireExponent3_5.Literals, NearCubicWires.WireExponent3_5.PrimAsm.Plan.FinalPassLeaf l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.FinalPassStage1.StageT
          ) := (
            closureLeaf3
          );
          (@PCConstruction_b0ff58edc98d546e181650fc.parent h)
        )
      );
      fronts
    ))
  )
end PCRootPrefix_f093664dce31f53fa3e4d3523a15815e92fde1619ab5b318aa9b46b52ceb1016
