import Lean
import Proof.Wire_3_5.Primitive.Writers.SBIdent
import Proof.Wire_3_5.Primitive.Writers.SBParse2
import Proof.Wire_3_5.Primitive.Writers.SBCarBase
import Proof.Wire_3_5.Primitive.Writers.SBFieldE
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SBTypesBase


noncomputable section
set_option maxRecDepth 4096


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

/-! ## (b) The words are S4's -/

/-- The call's cap `B_m(n)` at the gate. -/
noncomputable def capAt (l : Literals) (m : Mode) (P : Shared.StarParams) : ℕ :=
  Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n) P.n

/-- **`sb_outs`, stated**: from `SBIdentStmts l`, at a star call the register-shaped words are S4's words `4 … 7`. -/
def SBOutsStmt (l : Literals) : Prop :=
  SBIdent.SBIdentStmts l → ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) (hs : (callInputs l F kclk coef A a ha).StarAt r.1.n) (k : Fin 4),
    sbWords ((callInputs l F kclk coef A a ha).starParams r.1.n hs)
      (capAt l r.1.mode ((callInputs l F kclk coef A a ha).starParams r.1.n hs))
      (F.filterErrDeg * Nat.clog 2 (r.1.n + 2)) (Out.Car.carCnt r.1.carriers 0) (Out.Car.carCnt r.1.carriers 1)
      r.1.carriers.length k =
    Seams.frontWordsW2 l F kclk coef A a ha Finish.Sw0 r (Finish.s4SlotB k)

/-! ## (c) Capacity and cost -/

/-- **Every capacity need of SB** at a call (`cr`, `fe` the gate's, `wl = |fpIn r|`, the counts `c0 c1 nc`): P1's
phase sums, phase A's needs (the star numbers, the sparse count, `capNeed_of`'s bound, `λ`, `t`), the parse and count
reads, the two emissions, the field phase (`4ℓ + 6`), the carrier pipeline (`2^{DtC}·(wl+1)^{DtC}`). -/
noncomputable def sbNeed (l : Literals) (cr fe : ℕ) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc : ℕ) : ℕ :=
  tB1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  tB2a P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  tB2b P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  tB2c P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  tC1 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  tC2 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  tC3 P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m fe (mbOf m) nc c0 c1 +
  (P.n + 1) ^ 26 + ((fe + 4) * (P.n + 3) + 2 * cr + 20) +
  SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq P.n) (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n - 1) +
  (2 ^ 40 * (CallIndexR.capK cr * (P.n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
    CapNum.cMain (gateCap l) m) +
  Ledger.rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 P.n + Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) P.n +
  2 * wl + 2 ^ (natBitLength P.n + 1) + (c0 + c1 + nc + 3) +
  (fe * Nat.clog 2 (P.n + 2) / 4 + 2) +
  (PrimAsm.Data.unaryList (sbList P (Ledger.rowBCap (gateCap l) m P.r (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) P.n) P.n)
    (fe * Nat.clog 2 (P.n + 2)) c0 c1 nc)).length +
  (4 * ellOf P.n + 6) + 2 ^ Out.CarBound.DtC * (wl + 1) ^ Out.CarBound.DtC

/-- **The cost target**: P1's cost is polynomial in the capacity once `sbNeed ≤ cap`. -/
def SBCostStmt (l : Literals) : Prop :=
  ∃ Cc E : ℕ, ∀ (F : GateFree l) (P : Shared.StarParams) (m : Mode) (wl c0 c1 nc cap : ℕ),
    sbNeed l F.cr F.filterErrDeg P m wl c0 c1 nc ≤ cap →
      p1Cost cap wl P (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) m F.filterErrDeg F.cr c0 c1 nc ≤ Cc * cap ^ E

/-- **The capacity target**: at every request of the family (a star call), SB's need at the
call's numbers is within `Kc F·(|fpIn r|+1)^{Dk fe}`. -/
def SBCapStmt (l : Literals) : Prop :=
  ∃ (Kc : GateFree l → ℕ) (Dk : ℕ → ℕ), ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) (hs : (callInputs l F kclk coef A a ha).StarAt r.1.n),
    sbNeed l F.cr F.filterErrDeg ((callInputs l F kclk coef A a ha).starParams r.1.n hs) r.1.mode
        (fpIn l F kclk coef A a ha r).length (Out.Car.carCnt r.1.carriers 0) (Out.Car.carCnt r.1.carriers 1)
        r.1.carriers.length ≤
      Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg

end NearCubicWires.WireExponent3_5.PrimAsm.SBTypes

end
