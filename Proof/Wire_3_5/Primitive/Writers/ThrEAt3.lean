import Proof.Wire_3_5.FinalPass.FreeGen
import Proof.Wire_3_5.Primitive.SeedFix.C4KIface
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB4
import Proof.Wire_3_5.Primitive.Writers.ThrFam2

/-! # c4 THR block, the free numbers' side conditions at one THR call (`ThrEAt3`, v3)

The THR twin of `C4SymW.SymEAt3` (C4SymKB4, v6 agreed by and; held since M52 as pa-1027's, now shipped
with its producer `ThrSide.thrEAt`): at one THR call, the family `thrFam` at the free numbers `fr` with the child
requests' degree bound `dg` (read by no machine): the enumeration's conditions (`hok`), the compiler's precondition
(`hpre`), `Q' ≤ pr`, the child's step bound (`hcost`, at the printer's request word), the exact recovery range, the pad
(`cellCost + 1 ≤ 2^ρ`), the THR pool's coefficients within `h` bits (`CoefFit`), `1 ≤ h`.

Paper quantity of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a THR call and its degree bound
(P3:2929-2941, 2994-3000, 3011-3016, 3034-3036, 3094-3107). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : I.StarAt n)

/-- **The free numbers' side conditions at one THR call**, v3 (the family `thrFam` at `fr`, the child requests' degree
bound `dg`). -/
def ThrEAt3 (fr : Fin 7 → ℕ) (dg K Kch : ℕ) (E3 : Envelope) : Prop :=
  ∃ (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      C4Dock.EnumOk (thrSP alg I hs Cs) (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1)
        (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K (thrExprs alg I hs Cs carriers translation)
        (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (thrSP alg I hs Cs).ell →
      (C4Child.chR (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
        (thrExprs alg I hs Cs carriers translation) (p ++ [b])).Pre alg)
    (hQp : fr 2 ≤ fr 5)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (thrSP alg I hs Cs).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (fr 5 + 1)
        (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg
          (fr 5) 0) (thrSP alg I hs Cs) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1)
          (thrExprs alg I hs Cs carriers translation) (p ++ [b]))) →
      C4Child.coreCost wa alg (thrR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (thrSP alg I hs Cs) (fr 0) (fr 1) (PrimAsm.Enum.thrNT alg I hs Cs) (carriers.length + 1) K
        (thrExprs alg I hs Cs carriers translation) (p ++ [b]) r ≤ Kch),
    (∀ p' : List Bool, p'.length ≤ 8 * (thrSP alg I hs Cs).ell → ∀ z,
      (2 : ℤ) ^ (fr 4 - 1) * SeedFix.sampElim (thrSP alg I hs Cs)
        (SeedFix.thrStateBits alg I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ fr 2) ∧
    (thrFam alg I hs Cs carriers translation wa E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0
      (thrEnts alg I hs Cs carriers translation) (fr 0) (fr 1) K Kch hok hpre hQp hcost).cellCost + 1 ≤ 2 ^ fr 6 ∧
    CompilerMachine.Pool.CoefFit alg
      (C4Geo.poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        (Records.thrPool (I.starParams n hs) Cs carriers) (fr 3) (fr 2) 0) ∧
    1 ≤ fr 3

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
