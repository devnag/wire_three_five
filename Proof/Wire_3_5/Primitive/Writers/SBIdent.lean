import Proof.Wire_3_5.Primitive.Writers.SBNumsF
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ

/-! # SB: the value identifications, statements only

SB's registers (`SBNums`) hold S4's small numbers in the shapes the register programs compute. These are the
statements that identify them with the paper's definitions: the filter's parameters `filterParams` (P3:2019-2025), its
field, label and walk widths (`GapParams.fieldBits`, `labelBits`, `walkLen`, P3:2039-2100), the seed width, the
majority threshold, the star geometry (`hL`, `dRow`, `dR`, P3:1195-1215), and S4's four words `4 … 7` at a star call
(`s4Core2`, P3:3170-3181). A free component proves them; the S4WordsMBJ assembly takes `SBIdentStmts` as its hypothesis.

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

/-- The field width from the registers: `ℓ = natBitLength (len − 1) + 4`, `len = (n+1)^26·2`. -/
def FieldBitsStmt : Prop := ∀ n cap e : ℕ,
  Filters.GapParams.fieldBits ⟨2 * (n + 1) ^ 26, cap, e⟩ = natBitLength ((n + 1) ^ 26 * 2 - 1) + 4

/-- The label width from the registers. -/
def LabelBitsStmt : Prop := ∀ n cap e : ℕ, 1 ≤ cap →
  Filters.GapParams.labelBits ⟨2 * (n + 1) ^ 26, cap, e⟩ =
    max (natBitLength (cap * 32 - 1)) (natBitLength ((n + 1) ^ 26 * 2 - 1))

/-- The majority threshold of the walk: `e/4 + 1`. -/
def ThrStmt : Prop := ∀ n cap e : ℕ,
  SupplierWalk.majorityThreshold (Filters.GapParams.walkLen ⟨2 * (n + 1) ^ 26, cap, e⟩) = e / 4 + 1

/-- The seed width in the registers' shape (`wOf ℓ lb = ((ℓ + ℓ) + lb) + (lb − 1) + lb`). -/
def SeedWidthStmt : Prop := ∀ n cap e : ℕ, 1 ≤ cap →
  Seams.seedWidth ⟨2 * (n + 1) ^ 26, cap, e⟩ =
    e / 4 * 320 +
      ((((natBitLength ((n + 1) ^ 26 * 2 - 1) + 4) + (natBitLength ((n + 1) ^ 26 * 2 - 1) + 4)) +
        max (natBitLength (cap * 32 - 1)) (natBitLength ((n + 1) ^ 26 * 2 - 1))) +
        (max (natBitLength (cap * 32 - 1)) (natBitLength ((n + 1) ^ 26 * 2 - 1)) - 1) +
        max (natBitLength (cap * 32 - 1)) (natBitLength ((n + 1) ^ 26 * 2 - 1))) * 256

/-- The star geometry of S4's small numbers. -/
def GeoStmt : Prop := ∀ P : Shared.StarParams,
  PrimT.C4Geo.hL P = (P.n - P.r * P.b + 1) / 2 ∧
    P.n - P.r * P.b - PrimT.C4Geo.hL P = (P.n - P.r * P.b) / 2 ∧
    PrimT.C4Geo.dRow P = (P.b - P.s) * (P.r / 2) + (P.n - P.r * P.b + 1) / 2 ∧
    PrimT.C4Geo.dR P = (P.b - P.s) * (P.r / 2) + (P.n - P.r * P.b) / 2

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
