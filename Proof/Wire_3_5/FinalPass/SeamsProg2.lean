import Proof.Wire_3_5.FinalPass.SeamsPt2
import Proof.Wire_3_5.Primitive.Writers.S5SeamB

/-! # The seeds phase's type over the SYM evaluator's WORDS, with its cost bounds

`SeedsProg` takes the SYM evaluator as a `SymPtEval` and leaves its cost functions `tab`, `pt`, `ov` free.
Since the SYM evaluator is a `SymPtEval2`, and `FitsRes` needs the seeds phase's cost bounded. The front (S5)
needs only the SYM evaluator's call words and numbers, so the phases now meet at those (`SymWords`), not at the
evaluator:

* **`SymWords`** (`nw`, `nn`, `words`, `nums`), `SymPtEval2.toWords`, `symToWords` (from a `SymPtEval`);
* **`frontWordsOfW`** / `frontWordsW`: `frontWordsOf`'s slots with the SYM words of a `SymWords`
  (`frontWordsOf_toWords`: the `frontWordsOf` is the case `symToWords E3`);
* **`SeedsProg2`**: `SeedsProg` over `frontWordsW`, with its costs bounded: per point `pt r ≤ Cp·(n+1)^{Dp}`
  (polynomial in the request's width, P3:3175-3178 "This takes polynomial time"; NOT in `|fpIn|`, which carries the
  `Q = 2^{3k/4}n^{O(1)}` sampled pairs), per filter seed and overall in the preprocessing form of `s5Bound`
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

/-- **The SYM evaluator's words**: what the front writes for a SYM request (S5 needs nothing else). -/
structure SymWords where
  nw : ℕ
  nn : ℕ
  words : SymCall → Fin nw → List Bool
  nums : SymCall → Fin nn → ℕ

/-- A blank-cell SYM evaluator's words. -/
def SymPtEval2.toWords (E : SymPtEval2) : SymWords := ⟨E.nw, E.nn, E.words, E.nums⟩

section Req2
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (Sw : SymWords)

/-- **The front's words at a request, over the SYM words**: `frontWordsOf`'s slots (S4's 8 words; the THR
evaluator's 7 words and its numbers; the SYM words and numbers). -/
def frontWordsOfW : PrimRequest → Fin (17 + Sw.nw) → List Bool
  | ⟨n, .sym, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).symS Cs carriers translation hs) carriers (I.filterParams .sym n) ⟨i.val, h8⟩
        else if i.val < 16 then []
        else if h : i.val - 16 < Sw.nw then Sw.words (symCallOf I hs ha Cs carriers) ⟨i.val - 16, h⟩
        else PrimAsm.Data.unaryList (List.ofFn (Sw.nums (symCallOf I hs ha Cs carriers)))
      else []
  | ⟨n, .thr, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs) carriers (I.filterParams .thr n) ⟨i.val, h8⟩
        else if h15 : i.val < 15 then thrWords (thrCallOf I alg hs ha Cs carriers translation) ⟨i.val - 8, by omega⟩
        else if i.val = 15 then
          PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf I alg hs ha Cs carriers translation)))
        else []
      else []

end Req2

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- The front's words at a request of the family (over the SYM words). -/
noncomputable abbrev frontWordsW (r : FReq l F kclk coef A a ha) : Fin (17 + Sw.nw) → List Bool :=
  frontWordsOfW (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw r.1

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
