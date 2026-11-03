import Proof.Wire_3_5.Primitive.Writers.ThrCap1

/-! # PA2 c4 THR block, piece 3 part 2: the THR call's sizes below `2^{e(B+1)²}`

P3:3105-3115 (every size at an on-star call is `2^{O(k)}·poly(n)`), P3:1189 (`k = O((B+1)²)`), P3:2987-2988 (`Q`),
P3:2543-2558 (the THR numbers, W6's `ThrNumsPoly`): at a THR call of the gate, the star width, the THR filter's cap,
the data word's entries, the THR count, the THR filter's seed space, the request's word and `needW` are below
`2^{e·(B+1)²}` for constants `e` of the gate (`l`, `F`) and the words' polynomial bounds.

* `eCap`, `eTn`, `eQt`, `eSb`; **`thr_sizes`**; `thrX_small`.

Paper quantities of the main type: the THR call's sizes against `2^{(B+1)²}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires.WireExponent3_5.PrimT

section Small
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n)

/-- The THR call's `FreeIn` is small once each of its twelve fields is. -/
theorem thrX_small (Ds : ℕ)
    (h1 : n ≤ 2 ^ (Ds * C4Cap.bsq n)) (h2 : SeedFix.callKh (I.starParams n hs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h3 : Ledger.Lq n ≤ 2 ^ (Ds * C4Cap.bsq n)) (h4 : B.capOf .thr n ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h5 : a ≤ 2 ^ (Ds * C4Cap.bsq n)) (h6 : carriers.length ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h7 : thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h8 : SeedFix.thrCount alg I hs Cs ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h9 : max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h10 : Enum.thrNT alg I hs Cs ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h11 : wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h12 : C4Geo.dRow (I.starParams n hs) ≤ 2 ^ (Ds * C4Cap.bsq n)) :
    C4SymW.FreeSmall Ds (thrX I alg Cs carriers hs) :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

end Small

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
