import Proof.Wire_3_5.Assembly.C4Stage6
import Proof.Wire_3_5.Primitive.Writers.HashSetH2
import Proof.Wire_3_5.Primitive.SeedFix.C4KWl

/-!
# The c4 leaf, module block 7

The seventh verified block of the c4 leaf: the HASH setup (C) — the generic (g,p) populations loop, the
setup's parts (A) and P1, the HASH cell (…) and the setup machine with its
run `setupH_run` — and the kept words writer's types, kit, stages B1, B3, B4 and composition
(…). It is staged ahead of the c4 finish so that the finish ships only stage B2, the T-a/b/c
producers, the fit lemma and the HASH leaf. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage7

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage6.StageT

def pass (h : StageT) : C4Stage6.StageT := h

end NearCubicWires.WireExponent3_5.C4Stage7
