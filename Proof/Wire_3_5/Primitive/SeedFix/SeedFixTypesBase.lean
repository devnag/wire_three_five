import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase

/-! # SEEDFIX: the C4 part's type 

Paper: "There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173); for the hash, "Greedily choose a child with no larger value, using at most two printer
calls per hash bit" (P3:2331-2333).

PA's residual `SeedFixLeaf l` (`WireExponent3_5PrimAsmPlan`) is split along the verified writer interface v2
(`WireExponent3_5PrimAsmWriterIfaceJ`): PA's writers print the batches (`WriterLeafJ l`), and the C4 part is four
stages on their own tapes, each within `c₄·seedClasses E₄` at the ledger's `(n, kOf n, psiOf n)`:
* `front`: `frame req.word ↦ [modeBit req]` (the request's class mode);
* `sym`: `frame req.word`, `symTape ↦ seedWord` (SYM: the greedy sample, `samp:printable`);
* `hash`: `frame req.word`, `hashTape ↦ frame (thrIn …)`, the THR writer's input word `req.word ++ frame hashBits`
  (`filt:soft`'s fixed hash, P3:2253-2336);
* `thr`: `frame (thrIn …)`, `thrTape ↦ seedWord` (THR: the greedy sample, then the hash bits).
A stage's run (`Stage3Run`) is the bounded-residue form of: ports `0` (the framed word) and `1` (the tape
word) kept, the output on port `2`, residues of length at most the budget on the scratch tapes, every head at `0`.

`C4Leaf l` has `SeedFixLeaf`'s order of choice (`fe`, then `E₄`, `CD₄`, then `F`, then `c₄`). The cost inequality of
is explicit in the type: every stage's time is at most `c₄·seedClasses E₄ n (kOf n) (psiOf n)`.

Paper quantities of the main type: the fixed seeds `seedWord` (`samp:printable`, `filt:soft`) and the hash bits
`thrHashBits`, through `sym_run`, `hash_run`, `thr_run`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-! ## Stages -/

/-- **A C4 stage**: one machine on `3 + x` tapes; port `0` a framed word, port `1` a tape word, port `2` the output,
then `x` scratch tapes. -/
structure Stage3 where
  x : ℕ
  s : ℕ
  M : Machine (3 + x) s

/-- A stage's entry bank: `frame w`, `v`, the output and the scratch blank. -/
def stageIn (x : ℕ) (w v : List Bool) : Fin (3 + x) → List Bool :=
  Fin.addCases (m := 3) (n := x) (motive := fun _ => List Bool) ![frame w, v, []] (fun _ => [])

/-- A stage's exit bank: the ports kept, `y` on the output, the residues `J` on the scratch. -/
def stageOut (x : ℕ) (w v y : List Bool) (J : Fin x → List Bool) : Fin (3 + x) → List Bool :=
  Fin.addCases (m := 3) (n := x) (motive := fun _ => List Bool) ![frame w, v, y] J

/-- **A stage's run** within `B` steps (bounded residues, every head at `0` at both ends). -/
def Stage3Run (S : Stage3) (B : ℕ) (w v y : List Bool) : Prop :=
  ∃ J : Fin S.x → List Bool, (∀ j, (J j).length ≤ B) ∧
    ClockJoin.ReadyRun S.M B (stageIn S.x w v) (stageOut S.x w v y J)

/-- The request's class mode as a bit (`true` for `THR`), the bit after `natWord n` in `PrimRequest.word`. -/
def modeBit (req : PrimRequest) : Bool :=
  match req.mode with
  | .thr => true
  | .sym => false

/-! ## The C4 part at one call family -/

section At

end At

end NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes
