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
import Proof.Wire_3_5.Assembly.HStepV

/-! # The assembled proof of row B

`rowB_closed` is the assembled proof term: row B from the nine literal hypotheses, bundled as `Literals`.
`MainTheorem_Wire_3_5.lean` states it with the nine hypotheses as separate arguments. -/

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
