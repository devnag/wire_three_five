import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB2

/-! # C4.K SYM, the free numbers' contract, v4 (ruling, the findings 4 and 5)

"`alg:compiler`" (P3:1886-1906) keeps a request's coefficient bits (`h`) and its degree bound `d` separate; the pool's
coefficient width is `poly(n)` bits (P3:1596-1615). Changes from `SymEAt2`/`SymFreeOk2` and `SymFreeOk3`:
* **`SymEAt3 … fr dg …`**: the child requests carry the degree bound `dg` (was `fr 3 = h`); `d` is read by no machine
  (`C3ReqIface.preW_irrel`), so it is a number of the specification (`dF x`), not a slot of the free program;
* **`SymFreeOk4 … K3 D3`**: the field `dF`; `c3_le` in the form `h + Q' + m + pr ≤ K₃·(ψ(n)+1)·(n+1)^{D₃}` under
  `1 ≤ F.CD`, with `K₃`, `D₃` parameters (fixed before `F` by the leaf); `side` at `SymEAt3 … (dF (symX …))`.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a SYM call and its degree bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : I.StarAt n)

/-- **The free numbers' side conditions at one SYM call**, v3 (the (e); the family `C4Sym.symFam` at `fr`, the
requests' degree bound `dg`). -/
def SymEAt3 (fr : Fin 7 → ℕ) (dg K Kch : ℕ) (E3 : Envelope) : Prop :=
  ∃ (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      C4Dock.EnumOk (C4Val.symSP I hs Cs carriers) (symEnts I hs Cs carriers) (fr 0) (fr 1)
        (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K (symExprs I hs Cs carriers) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
        (symExprs I hs Cs carriers) (p ++ [b])).Pre alg)
    (hQp : fr 2 ≤ fr 5)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (fr 5 + 1)
        (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) (fr 3)
          (fr 5) 0) (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a)
          (symExprs I hs Cs carriers) (p ++ [b]))) →
      C4Child.coreCost wa alg (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (C4Val.symSP I hs Cs carriers) (fr 0) (fr 1) (PrimAsm.Enum.symNT I hs Cs carriers) (carriers.length + 2 * a) K
        (symExprs I hs Cs carriers) (p ++ [b]) r ≤ Kch),
    (∀ p' : List Bool, p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ (fr 4 - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ fr 2) ∧
    (C4Sym.symFam I hs Cs carriers translation wa alg E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0 (symEnts I hs Cs carriers)
      (fr 0) (fr 1) K Kch hok hpre hQp hcost).cellCost + 1 ≤ 2 ^ fr 6 ∧
    CompilerMachine.Pool.CoefFit alg
      (C4Geo.poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        (Records.symPool Cs carriers) (fr 3) (fr 2) 0) ∧
    1 ≤ fr 3

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
