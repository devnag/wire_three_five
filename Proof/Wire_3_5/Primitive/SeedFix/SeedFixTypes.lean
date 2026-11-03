import Lean
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase


noncomputable section
set_option maxRecDepth 4096


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

/-! ## The C4 part at one call family -/

section At
variable (l : Literals) (F : GateFree l) (E₄ : Envelope) (c₄ kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The seed-fixing budget at length `n`: `c₄·seedClasses E₄` at the ledger's `(n, kOf n, psiOf n)`. -/
noncomputable abbrev seedBudget (n : ℕ) : ℕ :=
  c₄ * seedClasses E₄ n (((gate0 l F).budget kclk coef A a ha).kOf n) (((gate0 l F).budget kclk coef A a ha).psiOf n)

/-- **The THR writer's input word**: the request, then the framed bits of the fixed hash. -/
noncomputable abbrev thrIn (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
    (translation : List ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) : List Bool :=
  (thrReq n a' ha' Cs carriers translation).word ++
    frame (List.ofFn (FinalPass.thrHashBits ((callInputs l F kclk coef A a ha).starParams n hs)
      (((callInputs l F kclk coef A a ha).starParams n hs).translationOfCodes translation) Cs carriers
      ((callInputs l F kclk coef A a ha).filterParams .thr n) (gate0 l F).alg
      (thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs)
      (thrCallE (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallT (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
      (thrCallJ (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)))

/-- **The C4 part at one call family**: the four stages, each within the seed-fixing budget. -/
structure C4At where
  front : Stage3
  front_run : ∀ req : PrimRequest, (callInputs l F kclk coef A a ha).Call req →
    Stage3Run front (seedBudget l F E₄ c₄ kclk coef A a ha req.n) req.word [] [modeBit req]
  sym : Stage3
  sym_run : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Stage3Run sym (seedBudget l F E₄ c₄ kclk coef A a ha n) (symReq n a' ha' Cs carriers translation).word
        (symTape (callInputs l F kclk coef A a ha) hs Cs carriers)
        (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (symReq n a' ha' Cs carriers translation))
  hash : Stage3
  hash_run : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Stage3Run hash (seedBudget l F E₄ c₄ kclk coef A a ha n) (thrReq n a' ha' Cs carriers translation).word
        (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
        (frame (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs))
  thr : Stage3
  thr_run : ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Stage3Run thr (seedBudget l F E₄ c₄ kclk coef A a ha n) (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs)
        (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (thrReq n a' ha' Cs carriers translation))

end At

/-- **The C4 part** (the seedfix child besides PA's writers), in `SeedFixLeaf`'s order of choice. -/
def C4Leaf (l : Literals) : Type :=
  ∀ fe : ℕ, Σ E₄ : Envelope, Σ CD₄ : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE E₄ F.E → CD₄ ≤ F.CD →
    Σ c₄ : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), C4At l F E₄ c₄ kclk coef A a ha

end NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes

end
