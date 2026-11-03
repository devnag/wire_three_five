import Proof.Wire_3_5.Primitive.Writers.SBIdentBase
import Proof.Wire_3_5.Primitive.Writers.SBParse2
import Proof.Wire_3_5.Primitive.Writers.SBCarBase
import Proof.Wire_3_5.Primitive.Writers.SBFieldE

/-! # SB: the assembly's types — exit shape, `sb_outs`, P1's cost shape, the capacity target

SB (`S4WordsMBJ l`) is split. This module fixes the types between the parts:

* (a) **`sbWords`** (S4's words `4 … 7` in the shapes SB's registers compute: the field width `ellOf`, the label width
  `lbOf`, the seed width `swOf`, the threshold `e/4 + 1`, the small numbers `sbList`) and **`SBExit`** (the exit
  state's output streams hold them);
* (b) **`SBOutsStmt l`**: given `SBIdentStmts l`, at every request of the family (a star call, `Call`'s sixth
  conjunct) `sbWords` at the call's numbers is `frontWordsW2 … (s4SlotB k)`;
* (c) P1's capacity sums `tB1 … tC3` (the phases' `hT`), **`sbNeed`** (every capacity need of SB: P1, the carrier
  pipeline, the field phase), P1's cost shape **`p1Cost`**, and the two arithmetic targets **`SBCostStmt l`**
  (`p1Cost ≤ Cc·cap^E` whenever `sbNeed ≤ cap`) and **`SBCapStmt l`** (`sbNeed ≤ Kc F·(|fpIn r|+1)^{Dk fe}` at every
  request), their constants existential.

Paper quantities of the main types: S4's words `4 … 7` (`s4Core2`, P3:3170-3181; `filt:gap`'s field, P3:2039-2055;
the walk's threshold; `s4Small2`) and SB's budget (`prim:runtime`, P3:3105-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBTypes
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SBNums
open NearCubicWires.WireExponent3_5.PrimAsm.SBParse

/-! ## (a) The words in the registers' shapes -/

/-- The field width `ℓ = natBitLength (len − 1) + 4`, `len = (n+1)^26·2`. -/
def ellOf (n : ℕ) : ℕ := natBitLength ((n + 1) ^ 26 * 2 - 1) + 4

/-- The label width `max (natBitLength (32·cap − 1)) (natBitLength (len − 1))`. -/
def lbOf (n CAP : ℕ) : ℕ := max (natBitLength (CAP * 32 - 1)) (natBitLength ((n + 1) ^ 26 * 2 - 1))

/-- The seed width `e/4·320 + wOf·256`, `wOf = 2ℓ + lb + (lb − 1) + lb`. -/
def swOf (n CAP e : ℕ) : ℕ := e / 4 * 320 + (((ellOf n + ellOf n) + lbOf n CAP) + (lbOf n CAP - 1) + lbOf n CAP) * 256

/-- S4's small numbers in the registers' shapes (the emission order of slot `7`). -/
def sbList (P : Shared.StarParams) (CAP e c0 c1 nc : ℕ) : List ℕ :=
  [1, P.b, P.s, P.r / 2, (P.n - P.r * P.b + 1) / 2, (P.n - P.r * P.b) / 2, P.n - P.r * P.b,
    (P.b - P.s) * (P.r / 2) + (P.n - P.r * P.b + 1) / 2, (P.b - P.s) * (P.r / 2) + (P.n - P.r * P.b) / 2,
    c0 * 2, c1 * 2, swOf P.n CAP e, nc, (P.n + 1) ^ 26 * 2, CAP, e]

/-- **SB's four words in the registers' shapes**: the trace mask, the modulus, `1^{e/4+1} 0`, the small numbers. -/
def sbWords (P : Shared.StarParams) (CAP e c0 c1 nc : ℕ) : Fin 4 → List Bool :=
  ![frame (binary (ellOf P.n) (GF2.tau (GF.firstPrimitive (ellOf P.n)) (ellOf P.n))),
    frame (binary (ellOf P.n) (GF.firstPrimitive (ellOf P.n))), ListEval.unary (e / 4 + 1),
    PrimAsm.Data.unaryList (sbList P CAP e c0 c1 nc)]

/-- **SB's exit shape**: the output streams hold `sbWords`. -/
def SBExit {ns : ℕ} (P : Shared.StarParams) (CAP e c0 c1 nc : ℕ) (st : Fin (ns + 1) → List Bool)
    (sOut : Fin 4 → Fin (ns + 1)) : Prop :=
  ∀ k : Fin 4, st (sOut k) = sbWords P CAP e c0 c1 nc k

/-! ## (b) The words are S4's -/

/-! ## (c) Capacity and cost -/

/-- `b1_run`'s capacity sum. -/
def tB1 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + ((P.n) + (1)) + (((P.n) + (1)) ^ 26) + ((((P.n) + (1)) ^ 26) * (2)) + (((((P.n) + (1)) ^ 26) * (2)) - 1) + (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + ((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) + (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1) + (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) + 40

/-- `b2a_run`'s capacity sum. -/
def tB2a (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + (Nat.clog 2 (P.n + 2)) + (P.r) + (P.s) + (P.b) + (P.r / 2) + (P.n - P.r * P.b) + (P.s * (P.r / 2)) + (P.k) + (fe * Nat.clog 2 (P.n + 2)) + (mb) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (nc) + (c0) + (c1) + ((((P.n) + (1)) ^ 26) * (2)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + (((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + ((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + (((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) + (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) + 400

/-- `b2b_run`'s capacity sum. -/
def tB2b (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + (Nat.clog 2 (P.n + 2)) + (P.r) + (P.s) + (P.b) + (P.r / 2) + (P.n - P.r * P.b) + (P.s * (P.r / 2)) + (P.k) + (fe * Nat.clog 2 (P.n + 2)) + (mb) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (nc) + (c0) + (c1) + ((((P.n) + (1)) ^ 26) * (2)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((fe * Nat.clog 2 (P.n + 2)) / (4)) + (((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1)) + ((fe * Nat.clog 2 (P.n + 2)) % (4)) + (4) + 400

/-- `b2c_run`'s capacity sum. -/
def tB2c (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + (Nat.clog 2 (P.n + 2)) + (P.r) + (P.s) + (P.b) + (P.r / 2) + (P.n - P.r * P.b) + (P.s * (P.r / 2)) + (P.k) + (fe * Nat.clog 2 (P.n + 2)) + (mb) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (nc) + (c0) + (c1) + ((((P.n) + (1)) ^ 26) * (2)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + (((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1)) + ((((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256))) + (((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256)) + ((fe * Nat.clog 2 (P.n + 2)) / (4)) + ((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + (320) + (256) + 400

/-- `c1_run`'s capacity sum. -/
def tC1 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + (Nat.clog 2 (P.n + 2)) + (P.r) + (P.s) + (P.b) + (P.r / 2) + (P.n - P.r * P.b) + (P.s * (P.r / 2)) + (P.k) + (fe * Nat.clog 2 (P.n + 2)) + (mb) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (nc) + (c0) + (c1) + ((((P.n) + (1)) ^ 26) * (2)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + (((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1)) + ((((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256))) + (((P.n - P.r * P.b) + (1)) / (2)) + ((P.n - P.r * P.b) / (2)) + ((P.n - P.r * P.b) + (1)) + (((P.n - P.r * P.b) + (1)) % (2)) + ((P.n - P.r * P.b) % (2)) + (2) + 400

/-- `c2_run`'s capacity sum. -/
def tC2 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + (Nat.clog 2 (P.n + 2)) + (P.r) + (P.s) + (P.b) + (P.r / 2) + (P.n - P.r * P.b) + (P.s * (P.r / 2)) + (P.k) + (fe * Nat.clog 2 (P.n + 2)) + (mb) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (nc) + (c0) + (c1) + ((((P.n) + (1)) ^ 26) * (2)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + (((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1)) + ((((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256))) + (((P.n - P.r * P.b) + (1)) / (2)) + ((P.n - P.r * P.b) / (2)) + ((((P.b) - (P.s)) * (P.r / 2)) + (((P.n - P.r * P.b) + (1)) / (2))) + ((((P.b) - (P.s)) * (P.r / 2)) + ((P.n - P.r * P.b) / (2))) + ((P.b) - (P.s)) + (((P.b) - (P.s)) * (P.r / 2)) + 400

/-- `c3_run`'s capacity sum. -/
def tC3 (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (mb nc c0 c1 : ℕ) : ℕ :=
  (P.n) + (Nat.clog 2 (P.n + 2)) + (P.r) + (P.s) + (P.b) + (P.r / 2) + (P.n - P.r * P.b) + (P.s * (P.r / 2)) + (P.k) + (fe * Nat.clog 2 (P.n + 2)) + (mb) + (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) + (nc) + ((((P.n) + (1)) ^ 26) * (2)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + (((fe * Nat.clog 2 (P.n + 2)) / (4)) + (1)) + ((((fe * Nat.clog 2 (P.n + 2)) / (4)) * (320)) + (((((((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4)) + ((natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)) + (4))) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) + ((max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1))) - 1)) + (max (natBitLength (((Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n) * (32)) - 1)) (natBitLength (((((P.n) + (1)) ^ 26) * (2)) - 1)))) * (256))) + (((P.n - P.r * P.b) + (1)) / (2)) + ((P.n - P.r * P.b) / (2)) + ((((P.b) - (P.s)) * (P.r / 2)) + (((P.n - P.r * P.b) + (1)) / (2))) + ((((P.b) - (P.s)) * (P.r / 2)) + ((P.n - P.r * P.b) / (2))) + ((c0) * (2)) + ((c1) * (2)) + (1) + (c0) + (c1) + (2) + 400

/-- The mode bit's register value. -/
def mbOf (m : Mode) : ℕ := if Codec.modeBit m then 1 else 0

/-- **P1's cost shape** (parse, three counts, the eight phases, the two emissions with their rewinds, the seams). -/
noncomputable def p1Cost (cap wl : ℕ) (P : Shared.StarParams) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) (m : Mode) (fe : ℕ) (cr c0 c1 nc : ℕ) : ℕ :=
  parseCost cap wl P.n + (16 * c0 + 14) + (16 * c1 + 14) + (16 * nc + 14) + aCost cap P h0 h1 Cδ C m fe cr +
  b1Cost cap P h0 h1 Cδ C m fe + b2aCost cap P h0 h1 Cδ C m fe + b2bCost cap P h0 h1 Cδ C m fe +
  b2cCost cap P h0 h1 Cδ C m fe + c1Cost cap P h0 h1 Cδ C m fe + c2Cost cap P h0 h1 Cδ C m fe +
  c3Cost cap P h0 h1 Cδ C m fe + 16 * (fe * Nat.clog 2 (P.n + 2) / 4 + 1) + 15 +
  SBEmit.emitListCost (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc) +
  5 * (PrimAsm.Data.unaryList (sbList P (Ledger.rowBCap C m P.r (Ledger.rowBSparse h0 h1 2 Cδ P.n) P.n)
    (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length + 64

end NearCubicWires.WireExponent3_5.PrimAsm.SBTypes
