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
import Proof.Wire_3_5.Assembly.HRootB
import Proof.Wire_3_5.Assembly.HStepE
import Proof.Wire_3_5.Assembly.HStepH
import Proof.Wire_3_5.Assembly.HStepK
set_option linter.unusedVariables false
set_option linter.defProp false
namespace PCRootPrefix_f471ce16a1efc30c1e4178e62864dce6551f22341ce42b8a5b1d0337e22892cd
set_option maxHeartbeats 4000000 in
noncomputable def root
    (closureLeaf0 : NearCubicWires.WireExponent3_5.ThrStage2.StageT)
    (closureLeaf1_ : NearCubicWires.WireExponent3_5.FinalPassStage4.StageT)
    : NearCubicWires.WireExponent3_5.Literals → NearCubicWires.WireExponent3_5.rowB :=
  (
    (@PCRootPrefix_156cc33d77aa06172477eda9b5ffea8358a77775d9dc7519bbcb1a3cf0e025d4.root
    (
      (
        let h : (
          NearCubicWires.WireExponent3_5.ThrStage1.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.ThrStage2.StageT
            ) := (
              closureLeaf0
            );
            (@PCConstruction_99e02282c93e6776a5f99a06.parent h)
          )
        );
        (@PCConstruction_ae1f8fec3325c7a3f3de6d54.parent h)
      )
    )
    (
      let thr : (
        (l : NearCubicWires.WireExponent3_5.Literals) →
          NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l →
            NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.ThrLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.ThrStage1.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.ThrStage2.StageT
              ) := (
                closureLeaf0
              );
              (@PCConstruction_99e02282c93e6776a5f99a06.parent h)
            )
          );
          (@PCConstruction_ae1f8fec3325c7a3f3de6d54.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.C4Stage5.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.C4Stage6.StageT
            ) := (
              (
                let h : (
                  NearCubicWires.WireExponent3_5.C4Stage7.StageT
                ) := (
                  (
                    let h : (
                      NearCubicWires.WireExponent3_5.C4Stage8.StageT
                    ) := (
                      (
                        (@PCConstruction_bbb3a001d95788fbeca5babd.parent)
                      )
                    );
                    (@PCConstruction_9960eda678f66d0bdba31710.parent h)
                  )
                );
                (@PCConstruction_12069815178817a713f68f37.parent h)
              )
            );
            (@PCConstruction_1121ae62685ed631271ec282.parent h)
          )
        );
        (@PCConstruction_0e895b75f3d9c4e662187a79.parent h)
      )
    )
    (
      let thr : (
        (l : NearCubicWires.WireExponent3_5.Literals) →
          NearCubicWires.WireExponent3_5.PrimAsm.PreLink.PreLinkT l →
            NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin.ThrLeafJ2 l
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.ThrStage1.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.ThrStage2.StageT
              ) := (
                closureLeaf0
              );
              (@PCConstruction_99e02282c93e6776a5f99a06.parent h)
            )
          );
          (@PCConstruction_ae1f8fec3325c7a3f3de6d54.parent h)
        )
      );
      let closureLeaf1 : (
        NearCubicWires.WireExponent3_5.C4Stage1.StageT
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.C4Stage5.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.C4Stage6.StageT
              ) := (
                (
                  let h : (
                    NearCubicWires.WireExponent3_5.C4Stage7.StageT
                  ) := (
                    (
                      let h : (
                        NearCubicWires.WireExponent3_5.C4Stage8.StageT
                      ) := (
                        (
                          (@PCConstruction_bbb3a001d95788fbeca5babd.parent)
                        )
                      );
                      (@PCConstruction_9960eda678f66d0bdba31710.parent h)
                    )
                  );
                  (@PCConstruction_12069815178817a713f68f37.parent h)
                )
              );
              (@PCConstruction_1121ae62685ed631271ec282.parent h)
            )
          );
          (@PCConstruction_0e895b75f3d9c4e662187a79.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.FinalPassStage3.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.FinalPassStage4.StageT
            ) := (
              closureLeaf1_
            );
            (@PCConstruction_f6ad40415f3caa237fcaa092.parent h)
          )
        );
        (@PCConstruction_fd26ecb3e0cde1616b40ebe8.parent h)
      )
    ))
  )
end PCRootPrefix_f471ce16a1efc30c1e4178e62864dce6551f22341ce42b8a5b1d0337e22892cd
