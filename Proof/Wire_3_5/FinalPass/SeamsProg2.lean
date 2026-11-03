import Lean
import Proof.Wire_3_5.FinalPass.SeamsPt2
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.SeamsProg2Base


noncomputable section
set_option maxRecDepth 4096


/-! # The seeds phase's type over the SYM evaluator's WORDS, with its cost bounds

`SeedsProg` takes the SYM evaluator as a `SymPtEval` and leaves its cost functions `tab`, `pt`, `ov` free.
Since #103 the SYM evaluator is a `SymPtEval2`, and `FitsRes` needs the seeds phase's cost bounded. The front (S5)
needs only the SYM evaluator's call words and numbers, so the phases now meet at those (`SymWords`), not at the
evaluator:

* **`SymWords`** (`nw`, `nn`, `words`, `nums`), `SymPtEval2.toWords`, `symToWords` (from a `SymPtEval`);
* **`frontWordsOfW`** / `frontWordsW`: `frontWordsOf`'s slots with the SYM words of a `SymWords`
  (`frontWordsOf_toWords`: the `frontWordsOf` is the case `symToWords E3`);
* **`SeedsProg2`**: `SeedsProg` over `frontWordsW`, with its costs bounded: per point `pt r ≤ Cp·(n+1)^{Dp}`
  (polynomial in the request's width, P3:3175-3178 "This takes polynomial time"; NOT in `|fpIn|`, which carries the
  `Q = 2^{3k/4}n^{O(1)}` sampled pairs), per filter seed and overall in the preprocessing form of the `s5Bound`
  (`C·2^{D·ψ}·(|fpIn|+1)^D`);
* `SeedsProg2.cost_le`: `|E|·tab + (|centers|·|E|·Q)·pt + ov` at the bounds.

Paper quantities: the printed numerator and denominator (`NumDenOut`), the seeds phase's cost (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split

section Req2

end Req2

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- The front's words at a request of the family (over the SYM words). -/
noncomputable abbrev frontWordsW (r : FReq l F kclk coef A a ha) : Fin (17 + Sw.nw) → List Bool :=
  frontWordsOfW (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw r.1

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams

end
