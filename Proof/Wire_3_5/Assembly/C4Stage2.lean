import Lean
import Proof.Wire_3_5.Assembly.C4Stage1
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB2
import Proof.Wire_3_5.Primitive.Writers.ThrStage2
import Proof.Wire_3_5.FinalPass.FreeGen5
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface
import Proof.Wire_3_5.Primitive.SeedFix.C4KLeafBase
import Proof.Wire_3_5.Primitive.SeedFix.C4SymWE
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase


noncomputable section
set_option maxRecDepth 4096


/-!
# The c4 leaf, module stage 2

This module collects the c4 leaf's second verified block: the SYM numbers machine at the computed capacity and the SYM
stage's dock on it with the links, the THR stage on the big bank with its numbers, family and finisher, and the generic
free-number program. It proves nothing new: the target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `C4Leaf l`, the seed-fixing stage of `lem:primitive` (P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4Stage2

open NearCubicWires.WireExponent3_5

/-- The c4 leaf, unchanged (an alias). -/
abbrev StageT : Type := C4Stage1.StageT

end NearCubicWires.WireExponent3_5.C4Stage2

end
