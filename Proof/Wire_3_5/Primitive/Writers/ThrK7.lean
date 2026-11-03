import Lean
import Proof.Wire_3_5.Primitive.Writers.ThrEAt3
import Proof.Wire_3_5.Primitive.Writers.ThrCap3Base
import Proof.Wire_3_5.Primitive.Writers.CallSizeBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.ThrK7Base


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 c4 THR block, piece 7 part 1: the THR free numbers' contract, v7 (v6 + the strip's premises)

The THR twin of the `C4SymW.SymFreeOk6` (the v6 shapes, root's ruling to build ThrEAt/ThrFreeOk at them) with the
per-call strip field approved in #162: the THR stage's C3 sub-stage (`ThrStrip.thrC3`, M53) runs the strip
(`stripW_spec`) at the capacity `2·pr + 2` of the free program's `pr`, so its premises (`thr_hc3`'s `c1`–`c7`, `cw`,
with the code bound `Kb = kbT n`) are a field of the contract, discharged by the builder at `pr = d_P(n+1)^{e_P}`.
* `kbT` (the codes' bit bound at the gate's description degree 26), **`ThrStripAt`** (the strip's premises at one
  call), **`ThrFreeOk7`**, **`ThrFreeOkB7`** (the builder: for every `fe`, the load floor and the constants before `F`).

Paper quantities of the main types: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of the THR stage (P3:2929-2941,
3011-3016, 3094-3107) and the THR request word with the fixed hash's framed bits (P3:2238-2251). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

/-- **The free numbers of the THR stage**, v7: v6's fields (the twin of `C4SymW.SymFreeOk6`) and the strip's
premises at every THR call. -/
structure ThrFreeOk7 (l : Literals) (F : GateFree l) (wa : RepairRepresentation.WilliamsAlgorithm) (K3 D3 Kp Dp : ℕ) :
    Type where
  Fp : FreeProg
  /-- The requests' degree bound (a number of the specification; no machine reads it). -/
  dF : FreeIn → ℕ
  K : ℕ → ℕ
  Kch : ℕ → ℕ
  E3 : Envelope
  /-- The program runs at every capacity above `K·2^{⌊n/8⌋}`, on every small `x`. -/
  ok_le : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), C4SymW.FreeSmall Ds x →
    Ko * 2 ^ (x.n / 8) ≤ cap → Fp.ok cap x
  /-- Its steps are quadratic in the capacity. -/
  cost_le : ∃ Kc : ℕ, ∀ (cap : ℕ) (x : FreeIn), Fp.cost cap x ≤ Kc * (cap + 1) ^ 2
  /-- Its values (but the pad's exponent) are at most `K·2^{⌊n/8⌋}` on every small `x`. -/
  val_le : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), C4SymW.FreeSmall Ds x → j.val ≠ 6 →
    Fp.val x j ≤ Kv * 2 ^ (x.n / 8)
  /-- The pad's exponent is polynomial in `n`. -/
  rho_le : ∃ Kr Dr : ℕ, ∀ x : FreeIn, Fp.val x 6 ≤ Kr * (x.n + 1) ^ Dr
  /-- The pad `2^ρ` is within the table and selection classes (P3:3098-3100), at `Kp`, `Dp` fixed before `F`. -/
  pad_le : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      2 ^ Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 6 ≤
        Kp * (2 ^ (n - ((gate0 l F).budget kclk coef A a ha).kOf n) * (n + 1) ^ Dp +
          2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2))
  /-- The compiler request's numbers are within the load times a polynomial (`C3ReqIface3`), at a load constant
      `C_D ≥ 1`. -/
  c3_le : 1 ≤ F.CD → ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 3 +
        Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 2 +
        Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 4 +
        Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5 ≤
        K3 * (((gate0 l F).budget kclk coef A a ha).psiOf n + 1) * (n + 1) ^ D3
  /-- **The side conditions at every THR call.** -/
  side : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ThrEAt3 (callInputs l F kclk coef A a ha) (gate0 l F).alg wa Cs carriers translation hs
        (Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs))
        (dF (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs)) (K n) (Kch n) E3

  /-- **The strip's premises at every THR call**, at the capacity `2·pr + 2` of the free program's `pr`. -/
  strip : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      ThrStripAt (Fp.val (thrX (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers hs) 5) ha' Cs carriers
        translation (ThrCap.hbC (callInputs l F kclk coef A a ha) (gate0 l F).alg Cs carriers translation hs)

/-- **The THR free numbers' builder**, v7: for every `fe`, the load floor `CDt` and the constants
`K3 D3 Kp Dp` before `F`, then `ThrFreeOk7` at every admissible `F` above the floor with `1 ≤ F.E.cpsi`. -/
def ThrFreeOkB7 (l : Literals) (wa : RepairRepresentation.WilliamsAlgorithm) : Type :=
  ∀ fe : ℕ, Σ CDt : ℕ, Σ K3 : ℕ, Σ D3 : ℕ, Σ Kp : ℕ, Σ Dp : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe →
    CDt ≤ F.CD → 1 ≤ F.E.cpsi → ThrFreeOk7 l F wa K3 D3 Kp Dp

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFam

end
