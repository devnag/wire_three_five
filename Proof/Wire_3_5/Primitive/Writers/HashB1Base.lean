import Proof.Wire_3_5.Primitive.Writers.ThrCap4Base
import Proof.Wire_3_5.Primitive.Writers.HashN2
import Proof.Wire_3_5.Primitive.Writers.HashF1Base

/-! # HASH setup (A), part 4: the HASH numbers machine's run and the hash bits at one call

The HASH twins of the `thr_big_at`/`thr_hxe_at`: at a THR call, from `thr_fits2`'s call fits (`ThrFitAt`) and
`hash_fitsX`'s free-number fits at `hashX` (`HashFitX`), the HASH numbers machine `bigWTH` runs at capacity `2M + 2`
on the THR request word (the HASH stage's input, no hash suffix) (**`hash_big_at`**, `HashBig`), and the hash bits'
program runs there with an empty suffix (**`hash_hxe_at`**; the THR setup's chain is reused unchanged).
* `hashX_eq`, `HashBig`, **`hash_big_at`**, **`hash_hxe_at`**.

Paper quantity of the main type: the HASH stage's free numbers on the loop-entry words. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Small
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n)

/-- **The HASH call's `FreeIn`** in the numbers machine's register form (`thrX_eq` with `a := t`, entry `12`). -/
theorem hashX_eq (hcd : I.carrierDeg = 26) :
    FinalPass.HashFr.hashX I alg Cs carriers hs =
      ⟨(I.starParams n hs).n, (I.starParams n hs).s * ((I.starParams n hs).r / 2),
        Nat.clog 2 ((I.starParams n hs).n + 2), (hnC I alg Cs carriers hs).getD 1 0, (hnC I alg Cs carriers hs).getD 12 0,
        (carriers.map Carrier.code).length, (hnC I alg Cs carriers hs).getD 7 0, SeedFix.thrCount alg I hs Cs,
        max ((I.starParams n hs).s * ((I.starParams n hs).r / 2) + (I.starParams n hs).s * ((I.starParams n hs).r / 2))
          (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)),
        2 ^ (SymDec.gP n (B.capOf .thr n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
          Fintype.card (ThrEq (I.starParams n hs) Cs alg) *
          ThrQ.primeSum (thrCutoff (I.starParams n hs) Cs alg (thrCallDen alg I hs Cs)),
        wOf ((I.starParams n hs).s * ((I.starParams n hs).r / 2)) (SeedFix.thrCount alg I hs Cs),
        ((I.starParams n hs).n - (I.starParams n hs).r * (I.starParams n hs).b + 1) / 2 +
          ((I.starParams n hs).b - (I.starParams n hs).s) * ((I.starParams n hs).r / 2)⟩ := by
  rw [hn1 I alg Cs carriers hs, hn7 I alg Cs carriers hs, ← thrNT_link I alg Cs hs hcd, PrimT.C4SymL.dRow_link,
    List.length_map, hn12 I alg Cs carriers hs]
  rfl

end Small

/-- **The HASH numbers machine's run at one call**: from the THR cell's entry on the request word (no hash suffix),
within `cost` at capacity `cap`, the request stays on stream `0` and the thirty-nine words hold the HASH call's numbers
(`ThrBig` at `hashX`). -/
def HashBig (Fp : FreeProg) (cr fe cap cost : ℕ) {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E}
    (I : PrimitiveInputs B) (alg : RepairRepresentation.DecompositionAlgorithm) {n a : ℕ} (ha : a ≤ 4)
    (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
    (hs : I.StarAt n) (cs : List ℕ) : Prop :=
  ∃ (τ : WState (LNS 0) LNR) (c : ℕ),
    WExec cap (ThrNums.bigWTH Fp cr fe)
      (CellLoopD.blankCellD 0 (thrReq n a ha Cs carriers translation).word [] 0 (Data.unaryList cs)) τ c ∧
    c ≤ cost ∧ τ.st (sk 0 0) = frame (thrReq n a ha Cs carriers translation).word ∧
    ∀ j : Fin 39, τ.st (sk 0 (symO j)) = symClean (SeedFix.thrCount alg I hs Cs)
      (SeedFix.callKh (I.starParams n hs))
      (max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
        (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)))
      (Enum.thrNT alg I hs Cs * 2 ^ wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs))
      (0 + C4Geo.dRow (I.starParams n hs) + C4Geo.dRow (I.starParams n hs))
      (Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs))
      (derVals (SeedFix.thrCount alg I hs Cs) (SeedFix.callKh (I.starParams n hs))
        (Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs) 0) (Fp.val (FinalPass.HashFr.hashX I alg Cs carriers hs) 1)) j

section At

end At

end NearCubicWires.WireExponent3_5.PrimAsm.ThrCap
