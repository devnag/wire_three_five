import Lean
import Proof.Wire_3_5.UnionMachine.RadSetupB
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.RadSpecBase


noncomputable section
set_option maxRecDepth 4096


/-! # RADIX, Route B: the split's specs — the block writer (stage 5b, C1b) and the row's capacities and
admissibility (stage 7, C1b)

P3:2585-2623 (row:radix). The RADIX setup (`RadSetupB.RadSetupSpecB`, C6b) writes `frame q.record`; its store is, per
digit `d` of row `(g, p)` and per `t ≤ M` and sign, the factor block `marks (true :: blockC D L_d t sgn false labs_d)`
with `L_d = |gis_d|`, `labs_d = labsOf G row gis_d` (P3:2598-2599, `Records.thrDigs`). The per-digit loop calls the
block writer `2(M+1)` times per digit, with the digit's pool indices on a stream and the digit list's table word
`levelWord M J W (rowsOf D L_d)` (stage 4's builder) on another.

* `gisWord`: one digit's pool indices in `DigsW`'s format (`FinalPass.Digs.digsWord ls = ls.flatMap gisWord` by `rfl`);
* `radBlkK`, `blkSize`; **`RadBlockW`** (stage 5b's deliverable): one word program per layout, from the table word,
  the indices and seven registers, APPENDING `marks (true :: blockC …)` to the output stream and changing nothing else;
* `radX`, `radU`, `radRB`, `radCapB` (Route B's capacities: `R = U^40`, `Lg = R + 1`, `cap = U^45` at
  `U = 2^20·((8L+2)^{3·lb+1} + M + τ + L + Mlab + lb + lw + p + b₀ + 2)`);
* **`RadCapsStmt`**, **`RadPreStmt`** (stage 7's deliverables, as propositions).

Paper quantity of the main types: the RADIX row's factor blocks and its capacities (row:radix, P3:2585-2623). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSpec
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB

/-! ## The block writer (stage 5b) -/

/-! ## The row's capacities (stage 7) -/

/-- **Stage 7 (b), admissibility** (C1b): at every THR call of the gate, every selection, prime, residue and star
row, the RADIX row's request is admissible. -/
def RadPreStmt (l : Literals) (F : GateFree l) : Prop :=
  ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (g : ThrEq ((callInputs l F kclk coef A a ha).starParams n hs) Cs (gate0 l F).alg)
      (pr : SupplierPrime.PrimeIndex (Enum.thrC (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))
      (s : ZMod pr.val) (row : ℕ),
    row < (2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) ^ 2 →
    (radReqOf l F kclk coef A a ha hs Cs carriers translation g pr s row).Pre

end NearCubicWires.WireExponent3_5.UnionMachine.RadSpec

end
