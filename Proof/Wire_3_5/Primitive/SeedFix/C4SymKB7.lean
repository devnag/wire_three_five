import Lean
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB4
import Proof.Wire_3_5.Primitive.SeedFix.C4PadA
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7Base


noncomputable section
set_option maxRecDepth 4096


/-! # C4.K SYM, the free numbers' contract, v7: the degenerate call at the padded batch

P3:3011-3016 (the SYM tape's entries and the printed objective), P3:1882-1900 (alg:compiler's precondition, `1 ≤ m`,
every term padded to `m` factors), #146 (c′): at a SYM call with no rows (`a′ = 0`, no carriers, `R = 0`) the child
request's precondition fails at the call's own batch, so v6's `side` is unsatisfiable there. v7 = v6 (kept)
with `side` under `1 ≤ |carriers| + 2a′`, and **`side_pad`** at the degenerate calls: the same eight parts at the
**padded batch** (`C4Pad.padBatch`, the constant row per entry, `R′ = 1`; its entries `chunk N n_T 1 padBatch` are
`padEnts` of the empty entries, the `chunk_pad`), the child family `padFam`.

* `padB`, `padE`, `padFam`, **`SymPadEAt`**, **`SymFreeOk7`**.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a SYM call and its degree bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Call

end Call

/-- **The free numbers of the SYM stage**, v7 (the deliverable (e) + (g)): C4.K's program `Fp` (the `FreeProg`),
the requests' degree bound `dF`, the bounds `K`, `Kch`, the compiler's envelope `E3`, the global bounds (the C3 load
at the constants `K3`, `D3` fixed before `F`; the pad at `Kp`, `Dp`), and the side conditions at every SYM call of every call family of `F`. -/
structure SymFreeOk7 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ) :
    Type where
  Fp : FreeProg
  /-- The requests' degree bound (a number of the specification; no machine reads it). -/
  dF : FreeIn → ℕ
  K : ℕ → ℕ
  Kch : ℕ → ℕ
  E3 : Envelope
  /-- The program runs at every capacity above `K·2^{⌊n/8⌋}`, on every small `x`. -/
  ok_le : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), FreeSmall Ds x →
    Ko * 2 ^ (x.n / 8) ≤ cap → Fp.ok cap x
  /-- Its steps are quadratic in the capacity. -/
  cost_le : ∃ Kc : ℕ, ∀ (cap : ℕ) (x : FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2
  /-- Its values (but the pad's exponent) are at most `K·2^{⌊n/8⌋}` on every small `x`. -/
  val_le : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), FreeSmall Ds x → j.val ≠ 6 →
    Fp.val x j ≤ Kv * 2 ^ (x.n / 8)
  /-- The pad's exponent is polynomial in `n`. -/
  rho_le : ∃ Kr Dr : ℕ, ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr
  /-- The pad `2^ρ` is within the table and selection classes (P3:3098-3100), at the constants `Kp`, `Dp` fixed before
      `F` (the envelope's table degree covers `Dp`). -/
  pad_le : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      2 ^ Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs) 6 ≤
        Kp * (2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) * (n + 1) ^ Dp +
          2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2))
  /-- The compiler request's numbers are within the load times a polynomial (for the C3 writer, `C3ReqIface3`), at a
      load constant `C_D ≥ 1`. -/
  c3_le : 1 ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs) 3 +
        Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs) 2 +
        Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs) 4 +
        Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs) 5 ≤
        K3 * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ D3
  /-- **The side conditions at every SYM call with rows** (`R = |carriers| + 2a′ ≥ 1`). -/
  side : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n, 1 ≤ carriers.length + 2 * a' →
      SymEAt3 (callInputs l F kclk coef A a ha) (gate0 l F).alg wa Cs carriers translation hs
        (Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs))
        (dF (symX (callInputs l F kclk coef A a ha) Cs carriers hs)) (K n) (Kch n) E3
  /-- **The side conditions at every degenerate SYM call** (`R = 0`, #146 (c′)): at the padded batch, `R′ = 1`. -/
  side_pad : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n, carriers.length + 2 * a' = 0 →
      SymPadEAt (callInputs l F kclk coef A a ha) (gate0 l F).alg wa Cs carriers translation hs
        (Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs))
        (dF (symX (callInputs l F kclk coef A a ha) Cs carriers hs)) (K n) (Kch n) E3

end NearCubicWires.WireExponent3_5.PrimT.C4SymW

end
