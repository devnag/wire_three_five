import Lean
import Proof.Wire_3_5.Assembly.HStepR
import Proof.Wire_3_5.Assembly.HStepM
import Proof.Wire_3_5.Assembly.HStepL
import Proof.Wire_3_5.Assembly.HStepQ
import Proof.Wire_3_5.Assembly.HStepV
import Proof.Wire_3_5.Assembly.HStepT
import Proof.Wire_3_5.Assembly.HStepP
import Proof.Wire_3_5.Assembly.HStepS
import Proof.Wire_3_5.Assembly.HStepN
import Proof.Wire_3_5.Assembly.HRootC
import Proof.Wire_3_5.Transfer.LiteralSources


/-! # Row B of Theorem 1.1 from the nine literal hypotheses, input 6 = the Murray–Williams short PCP

`rowB_closed` is the assembled proof term (Theorem 1.1, row B; `thm:tradeoff`): row B (the unchanged statement
`NearCubicWires.WireExponent3_5.rowB`) from the nine literal hypotheses bundled as `Literals` (whose sixth field is the
Murray–Williams oracle-circuit short PCP, §H.1 item 1; the eighth and ninth are CLW20 Theorem 1.13 at the clocks
`n^(k+2)` and CLW20 Lemma 3.9 at `S(n) ≥ n^c`). **`rowB_from_literature`** states it with the nine hypotheses as
separate arguments, in order. -/

set_option autoImplicit false
set_option maxRecDepth 120000
set_option linter.unusedVariables false


namespace NearCubicWires.WireExponent3_5.Assembly
set_option maxHeartbeats 4000000 in
theorem rowB_closed

    : NearCubicWires.WireExponent3_5.Literals → NearCubicWires.WireExponent3_5.rowB :=
  (
    let closureLeaf0_ : (
      NearCubicWires.WireExponent3_5.FinalPassStage6.StageT
    ) := (
      (
        let h : (
          NearCubicWires.WireExponent3_5.FinalPassStage7.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.FinalPassStage8.StageT
            ) := (
              (
                let h : (
                  NearCubicWires.WireExponent3_5.FinalPassStage9.StageT
                ) := (
                  (
                    (@PCConstruction_72c4e7537bea7089f1c0c980.parent)
                  )
                );
                (@PCConstruction_d5a6e176280158e74b5c9609.parent h)
              )
            );
            (@PCConstruction_f003eb8ff1958ebf3d8565c5.parent h)
          )
        );
        (@PCConstruction_023d29483e1a57ed3493626f.parent h)
      )
    );
    (@PCRootPrefix_f471ce16a1efc30c1e4178e62864dce6551f22341ce42b8a5b1d0337e22892cd.root
    (
      (
        let h : (
          NearCubicWires.WireExponent3_5.ThrStage3.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.ThrStage4.StageT
            ) := (
              (
                (@PCConstruction_5ec303f0da0b4c065f5c9859.parent)
              )
            );
            (@PCConstruction_f22d311b47920332b4fee78d.parent h)
          )
        );
        (@PCConstruction_24abd5ebc04c86fc6298b76a.parent h)
      )
    )
    (
      let closureLeaf0 : (
        NearCubicWires.WireExponent3_5.ThrStage2.StageT
      ) := (
        (
          let h : (
            NearCubicWires.WireExponent3_5.ThrStage3.StageT
          ) := (
            (
              let h : (
                NearCubicWires.WireExponent3_5.ThrStage4.StageT
              ) := (
                (
                  (@PCConstruction_5ec303f0da0b4c065f5c9859.parent)
                )
              );
              (@PCConstruction_f22d311b47920332b4fee78d.parent h)
            )
          );
          (@PCConstruction_24abd5ebc04c86fc6298b76a.parent h)
        )
      );
      (
        let h : (
          NearCubicWires.WireExponent3_5.FinalPassStage5.StageT
        ) := (
          (
            let h : (
              NearCubicWires.WireExponent3_5.FinalPassStage6.StageT
            ) := (
              closureLeaf0_
            );
            (@PCConstruction_e94fb8c233ba2586c141c2ff.parent h)
          )
        );
        (@PCConstruction_0e5eb99feeb25a1b9e58782b.parent h)
      )
    ))
  )
end NearCubicWires.WireExponent3_5.Assembly

namespace NearCubicWires.WireExponent3_5

end NearCubicWires.WireExponent3_5

