import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB
import Proof.Wire_3_5.Primitive.Writers.SymQM

/-! # C4.K SYM item (c), part 1: the numbers machine's values are the call's

P3:2987-2988, 3154-3162 (`samp:q`: the SYM sample count `Q = symCount`), P3:3011-3016 (the SYM tape's `n_T` states),
P3:1200 (`dRow`, the left center's bits `r/2·(b−s) + ⌈(n−rb)/2⌉`): the numbers the SYM numbers machine
(`C4Set.bigS_spec`) leaves in its registers are the call's own `Q`, `n_T`, `dRow`, so its `FreeIn` is `symX`.

* `symQ_link` (`Q`), `symNT_link` (`n_T = |GapSeed|·|FlatSeed|·Π(m_j+1)²`), `dRow_link`, **`symX_eq`**.

Paper quantities of the main type: the SYM call's `Q`, `n_T`, `dRow`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymL
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Stars NearCubicWires.SupplierPipeline

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n)

/-- **`Q` link**: the numbers machine's count is the call's sample count `symCount`. -/
theorem symQ_link (ha : a ≤ 4) (hD : I.D = 1) (hcd : I.carrierDeg = 26) :
    (symInOf (B.capOf .sym n) n (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs))
      carriers.length a (SymDec.cyOf Cs)).Q = SeedFix.symCount I hs Cs carriers := by
  have hP : (symInOf (B.capOf .sym n) n (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh (I.starParams n hs)) carriers.length a (SymDec.cyOf Cs)).Padded (SymDec.cyOf Cs) :=
    ⟨(SymDec.cyOf_length Cs).symm, ha, fun _ => rfl⟩
  have e1 : SymDec.cyOf Cs = List.ofFn fun i => (Cs i).bottomCount := by
    unfold SymDec.cyOf; congr 1; funext i; exact length_symGates (Cs i)
  have e2 : (SymDec.cyOf Cs).sum = ∑ i, (Cs i).bottomCount := by rw [e1, List.sum_ofFn]
  rw [SymQM.SymIn.Q_eq _ _ hP, SymQ.symCount_eq I hs Cs carriers, hD,
    SymDec.filterParams_eq I (B.capOf .sym n) hcd rfl, SymQM.SymIn.Mv_eq _ _ hP, e2, e1]
  rfl

/-- **`n_T` link**: the seed block's product is the SYM tape's state count `symNT`. -/
theorem symNT_link (ha : a ≤ 4) (hD : I.D = 1) (hcd : I.carrierDeg = 26) :
    2 ^ (SymDec.gP n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
        2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) *
        SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0)
          ((SymDec.cyOf Cs).getD 3 0) = Enum.symNT I hs Cs carriers := by
  rw [SymDec.seed_eq_nGap I _ hcd rfl, SymDec.fbv_eq_nFlat I Cs carriers _ hD rfl, SymDec.stV_eq_nSt I hs Cs ha,
    SymDecEnum.symNT_eq]

end Call

/-- **`dRow` link**: the seed block's `dRow` is the left center's bit count. -/
theorem dRow_link (P : StarParams) : (P.n - P.r * P.b + 1) / 2 + (P.b - P.s) * (P.r / 2) = C4Geo.dRow P := by
  show _ = P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2
  rw [Nat.add_comm, Nat.mul_comm]

section Call2
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (hs : I.StarAt n)

/-- **The numbers machine's `FreeIn` is the call's `symX`** (at the machine's own `Q`, block product and `dRow`). -/
theorem symX_eq (ha : a ≤ 4) (hD : I.D = 1) (hcd : I.carrierDeg = 26) :
    C4SymW.symX I Cs carriers hs =
      ⟨(I.starParams n hs).n, (I.starParams n hs).s * ((I.starParams n hs).r / 2), Ledger.Lq n, B.capOf .sym n,
        (Data.symCodes a Cs).length, carriers.length, (SymDec.cyOf Cs).sum,
        (symInOf (B.capOf .sym n) n (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs))
          carriers.length a (SymDec.cyOf Cs)).Q,
        max ((I.starParams n hs).s * ((I.starParams n hs).r / 2) + (I.starParams n hs).s * ((I.starParams n hs).r / 2))
          (Nat.clog 2 (symInOf (B.capOf .sym n) n (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
            (SeedFix.callKh (I.starParams n hs)) carriers.length a (SymDec.cyOf Cs)).Q),
        2 ^ (SymDec.gP n (B.capOf .sym n) (I.filterErrDeg * Ledger.Lq n)).seedBits *
          2 ^ FlatNums.fbv (SymDec.cyOf Cs).sum (SymDec.bV carriers.length (B.capOf .sym n)) (Ledger.Lq n + 5) *
          SymDec.stV ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0)
            ((SymDec.cyOf Cs).getD 3 0),
        wOf ((I.starParams n hs).s * ((I.starParams n hs).r / 2))
          (symInOf (B.capOf .sym n) n (I.filterErrDeg * Ledger.Lq n) (Ledger.Lq n) (SeedFix.callKh (I.starParams n hs))
            carriers.length a (SymDec.cyOf Cs)).Q,
        ((I.starParams n hs).n - (I.starParams n hs).r * (I.starParams n hs).b + 1) / 2 +
          ((I.starParams n hs).b - (I.starParams n hs).s) * ((I.starParams n hs).r / 2)⟩ := by
  rw [symQ_link I Cs carriers hs ha hD hcd, symNT_link I Cs carriers hs ha hD hcd, dRow_link,
    show (Data.symCodes a Cs).length = a by unfold Data.symCodes; simp]
  rfl

end Call2

end NearCubicWires.WireExponent3_5.PrimT.C4SymL
