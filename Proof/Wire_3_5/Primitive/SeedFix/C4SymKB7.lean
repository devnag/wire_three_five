import Proof.Wire_3_5.Primitive.SeedFix.C4PadA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB4

/-! # C4.K SYM, the free numbers' contract, v7: the degenerate call at the padded batch

P3:3011-3016 (the SYM tape's entries and the printed objective), P3:1882-1900 (alg:compiler's precondition, `1 ≤ m`,
every term padded to `m` factors): at a SYM call with no rows (`a′ = 0`, no carriers, `R = 0`) the child
request's precondition fails at the call's own batch, so v6's `side` is unsatisfiable there. v7 = v6 (kept)
with `side` under `1 ≤ |carriers| + 2a′`, and **`side_pad`** at the degenerate calls: the same eight parts at the
**padded batch** (`C4Pad.padBatch`, the constant row per entry, `R′ = 1`; its entries `chunk N n_T 1 padBatch` are
`padEnts` of the empty entries, `chunk_pad`), the child family `padFam`.

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
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : I.StarAt n)

/-- **The degenerate call's padded batch**: the constant row per entry (`R′ = 1`). -/
abbrev padB : List SeedFix.SExpr :=
  C4Pad.padBatch (2 ^ SeedFix.callKh (I.starParams n hs)) (PrimAsm.Enum.symNT I hs Cs carriers)

/-- The padded batch's entries (`padEnts` of the empty entries, `chunk_pad`). -/
abbrev padE : List (List SeedFix.SExpr) :=
  SeedFix.JLink.chunk (2 ^ SeedFix.callKh (I.starParams n hs)) (PrimAsm.Enum.symNT I hs Cs carriers) 1
    (padB I Cs carriers hs)

/-- **The padded child family**: C4Child's, with C6's assembler and the padded batch. -/
noncomputable def padFam (E3 : Envelope) (h Q psi m d pr k TWd Cap K Kch : ℕ)
    (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      C4Dock.EnumOk (C4Val.symSP I hs Cs carriers) (padE I Cs carriers hs) TWd Cap (PrimAsm.Enum.symNT I hs Cs carriers)
        1 K (padB I Cs carriers hs) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
        (PrimAsm.Enum.symNT I hs Cs carriers) 1 (padB I Cs carriers hs) (p ++ [b])).Pre alg)
    (hQp : Q ≤ pr)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (pr + 1)
        (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k).P.width (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k)
          (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) 1 (padB I Cs carriers hs) (p ++ [b]))) →
      C4Child.coreCost wa alg (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k) (C4Val.symSP I hs Cs carriers)
        TWd Cap (PrimAsm.Enum.symNT I hs Cs carriers) 1 K (padB I Cs carriers hs) (p ++ [b]) r ≤ Kch) :
    C4Loop.ChildFam :=
  C4Child.chFam UnionMachine.TailAsm.asmStage wa alg (C4Sym.symR0 I hs Cs carriers translation h Q psi m d pr k)
    (C4Val.symSP I hs Cs carriers) (padE I Cs carriers hs) TWd Cap (PrimAsm.Enum.symNT I hs Cs carriers) 1 K
    (padB I Cs carriers hs) E3 Kch hok hpre hQp hcost

/-- **The free numbers' side conditions at one degenerate SYM call**, v7: `SymEAt3`'s eight parts at the padded
batch (`padB`, `padE`, `R′ = 1`) and the padded family `padFam`. -/
def SymPadEAt (fr : Fin 7 → ℕ) (dg K Kch : ℕ) (E3 : Envelope) : Prop :=
  ∃ (hok : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      C4Dock.EnumOk (C4Val.symSP I hs Cs carriers) (padE I Cs carriers hs) (fr 0) (fr 1)
        (PrimAsm.Enum.symNT I hs Cs carriers) 1 K (padB I Cs carriers hs) (p ++ [b]))
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) 1
        (padB I Cs carriers hs) (p ++ [b])).Pre alg)
    (hQp : fr 2 ≤ fr 5)
    (hcost : ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request),
      p.length < 8 * (C4Val.symSP I hs Cs carriers).ell →
      MatrixScoreBatch.word r = CompilerMachine.Req.reqWord (C4Geo.dRow (I.starParams n hs)) (fr 5 + 1)
        (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0).P.width
        (C4Geo.cols (I.starParams n hs))
        (CompilerMachine.Req.c3v2Ref alg (C4Child.chR (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg
          (fr 5) 0) (C4Val.symSP I hs Cs carriers) (PrimAsm.Enum.symNT I hs Cs carriers) 1
          (padB I Cs carriers hs) (p ++ [b]))) →
      C4Child.coreCost wa alg (C4Sym.symR0 I hs Cs carriers translation (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0)
        (C4Val.symSP I hs Cs carriers) (fr 0) (fr 1) (PrimAsm.Enum.symNT I hs Cs carriers) 1 K
        (padB I Cs carriers hs) (p ++ [b]) r ≤ Kch),
    (∀ p' : List Bool, p'.length ≤ 8 * (C4Val.symSP I hs Cs carriers).ell → ∀ z,
      (2 : ℤ) ^ (fr 4 - 1) * SeedFix.sampElim (C4Val.symSP I hs Cs carriers)
        (SeedFix.symStateBits I hs Cs carriers translation z) p'.length (SeedFix.listNum p') < 2 ^ fr 2) ∧
    (padFam I alg wa Cs carriers translation hs E3 (fr 3) (fr 2) 0 (fr 4) dg (fr 5) 0 (fr 0) (fr 1) K Kch hok hpre hQp
      hcost).cellCost + 1 ≤ 2 ^ fr 6 ∧
    CompilerMachine.Pool.CoefFit alg
      (C4Geo.poolReq (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
        (Records.symPool Cs carriers) (fr 3) (fr 2) 0) ∧
    1 ≤ fr 3

end Call

/-- **The free numbers of the SYM stage**, v7 (the deliverable (e) + (g)): C4.K's program `Fp` (`FreeProg`),
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
  /-- **The side conditions at every degenerate SYM call** (`R = 0`): at the padded batch, `R′ = 1`. -/
  side_pad : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n, carriers.length + 2 * a' = 0 →
      SymPadEAt (callInputs l F kclk coef A a ha) (gate0 l F).alg wa Cs carriers translation hs
        (Fp.val (symX (callInputs l F kclk coef A a ha) Cs carriers hs))
        (dF (symX (callInputs l F kclk coef A a ha) Cs carriers hs)) (K n) (Kch n) E3

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
