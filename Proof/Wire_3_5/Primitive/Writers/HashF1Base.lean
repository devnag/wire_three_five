import Proof.Wire_3_5.Primitive.Writers.ThrCap4Base
import Proof.Wire_3_5.FinalPass.HashFreeBase

/-! # HASH setup (A), part 3: the HASH free numbers' fits at the capacity v2

The HASH stage's free numbers are the `Fp` on `hashX = {thrX with a := t}`. `thr_fits2` (M54) gives the numbers
machine's call-only fits (`ThrFitAt`'s fields that do not read the free program's input); **`HashFitX`** collects the
five that do (`ok`, `fv`, `fd0`, `fd1`, `fd3`) at `hashX`, and **`hash_fitsX`** proves them once `C_c ≥ C₀`
(`thr_fits2`'s proof at `hashX`: `t = thrCallT` is the data word's entry `12`, `hn12`, `hashX_small`).

Paper quantity of the main type: the HASH stage's free numbers `h, Q', m, pr, ρ` against the capacity. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

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

/-- The data word's entry `12` is the moment count `t`. -/
theorem hn12 : (hnC I alg Cs carriers hs).getD 12 0 = thrCallT alg I hs Cs carriers := by
  rw [show (12 : ℕ) = 10 + 2 from rfl, hn_get I alg Cs carriers hs 10 (by norm_num), thrCallT_tt]
  rfl

/-- The HASH call's `FreeIn` is small once each of its twelve fields is. -/
theorem hashX_small (Ds : ℕ)
    (h1 : n ≤ 2 ^ (Ds * C4Cap.bsq n)) (h2 : SeedFix.callKh (I.starParams n hs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h3 : Ledger.Lq n ≤ 2 ^ (Ds * C4Cap.bsq n)) (h4 : B.capOf .thr n ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h5 : thrCallT alg I hs Cs carriers ≤ 2 ^ (Ds * C4Cap.bsq n)) (h6 : carriers.length ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h7 : thrDigits (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h8 : SeedFix.thrCount alg I hs Cs ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h9 : max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h10 : Enum.thrNT alg I hs Cs ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h11 : wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) ≤ 2 ^ (Ds * C4Cap.bsq n))
    (h12 : C4Geo.dRow (I.starParams n hs) ≤ 2 ^ (Ds * C4Cap.bsq n)) :
    C4SymW.FreeSmall Ds (FinalPass.HashFr.hashX I alg Cs carriers hs) :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

end Small

/-- **The HASH free numbers' fits at `M`** (the five of `ThrFitAt` that read the free program's input, at
`hashX`). -/
structure HashFitX (Fp : FreeProg) (M : ℕ) {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
    (I : PrimitiveInputs B) (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ}
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n) : Prop where
  ok : Fp.ok (2 * M + 2) (FinalPass.HashFr.hashX I alg Cs carriers hs)
  fv : ∀ j, Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs) j + 1 ≤ M
  fd0 : SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs) +
    Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs) 0 + 1 ≤ M
  fd1 : max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) * 8 *
    (max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) +
      max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
        (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)) + 1) + Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs) 1 + 1 ≤ M
  fd3 : wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs) + 1 +
    Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs) 0 + 1 ≤ M

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
