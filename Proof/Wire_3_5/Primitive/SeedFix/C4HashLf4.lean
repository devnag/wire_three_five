import Proof.Wire_3_5.Primitive.SeedFix.C4HashLf3

/-! # The HASH part of C4Leaf: the two call facts from `HashEAt`

`HashSideAt2`'s conjuncts `1 ≤ fr 3` (the pool's `h`) and `CoefFit` (the pool request's coefficients fit) at a THR call,
from the HASH builder's side conditions (`HashFreeOk2.side`: `HashEAt`'s last two clauses, at `thrR0 … (fr 3) (fr 2) 0 …`
whose pool request is `poolReq … (fr 3) (fr 2) 0`). The construction packages `HashObl2` with them.
* **`hash_h1`**, **`hash_hcf`**.

Paper quantity of the main type: the HASH child's compiler request (its pool's precision `h ≥ 1`, its coefficients'
fit), P3:2291-2296. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4HL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.HashCell NearCubicWires.WireExponent3_5.PrimAsm.HashSetH
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (wrapM wrapCost)

section Call
variable (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ)
  (H : FinalPass.HashFr.HashFreeOk2 l F wa K3 D3 Kp Dp) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
  {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n))
  (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (thrReq n a ha Cs carriers translation))
  (hs : (callInputs l F kclk coef A a0 ha0).StarAt n)
include ha hcall

/-- **`HashSideAt2`'s `h1`** at a THR call: the HASH child's pool precision is at least `1`. -/
theorem hash_h1 : 1 ≤ (H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3 :=
  (H.side kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs).2.2.2.2.2.2.2

/-- **`HashSideAt2`'s `hcf`** at a THR call: the HASH child's pool request's coefficients fit. -/
theorem hash_hcf : CompilerMachine.Pool.CoefFit ((gate0 l F).alg) (PrimT.C4Geo.poolReq ((callInputs l F kclk coef A a0 ha0).starParams n hs) (((callInputs l F kclk coef A a0 ha0).starParams n hs).translationOfCodes translation)
      (Records.thrPool ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs carriers) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 3) ((H.Fp.val (FinalPass.HashFr.hashX (callInputs l F kclk coef A a0 ha0) (gate0 l F).alg Cs carriers hs)) 2) 0) :=
  (H.side kclk coef A a0 ha0 n a ha Cs carriers translation hcall hs).2.2.2.2.2.2.1

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4HL
