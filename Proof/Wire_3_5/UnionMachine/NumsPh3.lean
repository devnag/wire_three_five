import Lean
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh3Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW: the phase interface v3 over the relaxed contract `NumsMJ` (types only)

The `CoreWordsMJ` lets a writer's scratch residue hold ANY content, of length at most
`C_s F·(|fpIn|+1)^{D_s fe}`. v3 keeps v2's bank, roles, values (`NumsPh2.eOf`, `mOf`, `vOf`, `DenSplit`) and phase
shapes, and changes the residue:

* **`ResidJ σ B`**: every stream but `sIn`, `sW0`, `sW1` of length `≤ B` (any content);
* **`AfterC`** (c)'s exit: every stream but `sIn` exactly `[]` (phase (c) never writes a stream), so (a) and (b) dock
  raw machines (`dataDock`) on fresh streams; **`AfterV`**, **`DBank`**, **`Final`**: the word streams `[]` until (d)
  (tapes never shrink), the rest `ResidJ`;
* **`PhC`**, **`PhA`**, **`PhB`**, **`PhD`** (as v2, residues as above) and **`NumsOfPhases x l : PhC x l → PhA x l →
  PhB x l → PhD x → NumsMJ l`**.

Paper quantity of the main types: the final pass's denominator `Den` in `T_f`-bit binary (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsPh3
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (x : ℕ)

section Bank
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **After (c)**: `n`, the mode bit, `e`, `T_f` in registers, every other register `0`, every stream but `sIn` blank. -/
structure AfterC (r : FReq l F kclk coef A a ha) (σ : St x) : Prop where
  hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha r)
  clean : ∀ i, i ≠ sIn x → σ.st i = []
  heads : ∀ i, σ.sh i = 0
  cell : σ.cell = false
  hn : σ.val rN = r.1.n
  hm : σ.val rM = mOf l F kclk coef A a ha r
  he : σ.val rE = eOf l F kclk coef A a ha r
  ht : σ.val rT = FinalPass.Sd.R.Tf l F kclk coef A a ha r
  regs : ∀ q, q ≠ rN → q ≠ rM → q ≠ rE → q ≠ rT → σ.val q = 0

/-- **After (a) or (b)**: `AfterC`'s registers and `V` in `rV`, the word streams blank, residue `B`. -/
structure AfterV (r : FReq l F kclk coef A a ha) (B : ℕ) (σ : St x) : Prop where
  hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha r)
  hw0 : σ.st (sW0 x) = []
  hw1 : σ.st (sW1 x) = []
  heads : ∀ i, σ.sh i = 0
  cell : σ.cell = false
  resid : ResidJ x σ B
  hn : σ.val rN = r.1.n
  hm : σ.val rM = mOf l F kclk coef A a ha r
  he : σ.val rE = eOf l F kclk coef A a ha r
  ht : σ.val rT = FinalPass.Sd.R.Tf l F kclk coef A a ha r
  hv : σ.val rV = vOf l F kclk coef A a ha r
  regs : ∀ q, q ≠ rN → q ≠ rM → q ≠ rE → q ≠ rT → q ≠ rV → σ.val q = 0

end Bank

section Phases
variable (l : Literals)

/-- **(c)**: `n`, the mode bit, `e = n − k`, `T_f` (per gate), no stream written. -/
structure PhC where
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (LNS x + 2 + LNR) (s F)
  Kn : GateFree l → ℕ
  Dn : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (cap : ℕ),
    Kn F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dn F.filterErrDeg ≤ cap → ∀ σ : St x,
      Entry x l F kclk coef A a ha r σ →
      ∃ (τ : St x) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
        AfterC x l F kclk coef A a ha r τ

/-- **(a)**: `V` at the SYM requests (per gate). -/
structure PhA where
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (LNS x + 2 + LNR) (s F)
  Kn : GateFree l → ℕ
  Dn : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (cap : ℕ),
    r.1.mode = .sym → Kn F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dn F.filterErrDeg ≤ cap → ∀ σ : St x,
      AfterC x l F kclk coef A a ha r σ →
      ∃ (τ : St x) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
        AfterV x l F kclk coef A a ha r (Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg) τ

/-- **(b)**: `V` at the THR requests (per gate). -/
structure PhB where
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (LNS x + 2 + LNR) (s F)
  Kn : GateFree l → ℕ
  Dn : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (cap : ℕ),
    r.1.mode = .thr → Kn F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dn F.filterErrDeg ≤ cap → ∀ σ : St x,
      AfterC x l F kclk coef A a ha r σ →
      ∃ (τ : St x) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
        AfterV x l F kclk coef A a ha r (Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg) τ

end Phases

end NearCubicWires.WireExponent3_5.UnionMachine.NumsPh3

end
