import Lean
import Proof.Wire_3_5.Primitive.Writers.SBNumsF
import Proof.Wire_3_5.FinalPass.CoreIfaceBase
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.SBIdentBase


noncomputable section
set_option maxRecDepth 4096


/-! # SB: the value identifications, statements only

SB's registers (`SBNums`) hold S4's small numbers in the shapes the register programs compute. These are the
statements that identify them with the paper's definitions: the filter's parameters `filterParams` (P3:2019-2025), its
field, label and walk widths (`GapParams.fieldBits`, `labelBits`, `walkLen`, P3:2039-2100), the seed width, the
majority threshold, the star geometry (`hL`, `dRow`, `dR`, P3:1195-1215), and S4's four words `4 … 7` at a star call
(`s4Core2`, P3:3170-3181). They are proved separately; the S4WordsMBJ assembly takes `SBIdentStmts` as its hypothesis.

* `FieldBitsStmt`, `LabelBitsStmt`, `ThrStmt`, `SeedWidthStmt`, `GeoStmt`, `FilterParamsStmt`, `StarRStmt`,
  `SlotsStmt`; **`SBIdentStmts l`**.

Paper quantity of the main type: S4's words `4 … 7` (`s4Core2`: the field words, the threshold, `s4Small2`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBIdent
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

/-- The call's filter parameters at the gate. -/
def FilterParamsStmt (l : Literals) : Prop := ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (m : Mode)
    (n : ℕ),
  (callInputs l F kclk coef A a ha).filterParams m n =
    ⟨2 * (n + 1) ^ 26, Ledger.rowBCap (gateCap l) m (Ledger.rowBr F.cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n, F.filterErrDeg * Nat.clog 2 (n + 2)⟩

/-- The call's star parameters at the gate. -/
def StarRStmt (l : Literals) : Prop := ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ)
    (hs : (callInputs l F kclk coef A a ha).StarAt n),
  ((callInputs l F kclk coef A a ha).starParams n hs).r = Ledger.rowBr F.cr n ∧
    ((callInputs l F kclk coef A a ha).starParams n hs).n = n

/-- **S4's words `4 … 7` at a star call** (either mode). -/
def SlotsStmt (l : Literals) : Prop := ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (r : FReq l F kclk coef A a ha) (hs : (callInputs l F kclk coef A a ha).StarAt r.1.n) (k : Fin 4),
  Seams.frontWordsW2 l F kclk coef A a ha Finish.Sw0 r (Finish.s4SlotB k) =
    (![Filt.tauWord ((callInputs l F kclk coef A a ha).filterParams r.1.mode r.1.n),
      Filt.modWord ((callInputs l F kclk coef A a ha).filterParams r.1.mode r.1.n),
      ListEval.unary (SupplierWalk.majorityThreshold
        ((callInputs l F kclk coef A a ha).filterParams r.1.mode r.1.n).walkLen),
      PrimAsm.Data.unaryList (Seams.s4Small2 ((callInputs l F kclk coef A a ha).starParams r.1.n hs) r.1.carriers
        ((callInputs l F kclk coef A a ha).filterParams r.1.mode r.1.n))] : Fin 4 → List Bool) k

/-- **The identifications the S4WordsMBJ assembly uses.** -/
structure SBIdentStmts (l : Literals) : Prop where
  fieldBits : FieldBitsStmt
  labelBits : LabelBitsStmt
  thr : ThrStmt
  seedWidth : SeedWidthStmt
  geo : GeoStmt
  filterParams : FilterParamsStmt l
  starR : StarRStmt l
  slots : SlotsStmt l

end NearCubicWires.WireExponent3_5.PrimAsm.SBIdent

end
