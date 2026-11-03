import Proof.Wire_3_5.UnionMachine.RadSetupB

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

/-- **One digit's pool indices**, `DigsW`'s format: each index `gi` as `true :: 1^gi 0`, then the closing `false`. -/
def gisWord (gis : List ℕ) : List Bool := gis.flatMap (fun gi => true :: (List.replicate gi true ++ [false])) ++ [false]

/-- The block writer's register count (inputs in `0 … 6`, scratch `7 …`). -/
abbrev radBlkK : ℕ := 64

/-- The block writer's size measure: the output's length, the block, the table word, the indices' word, the labels'
bound, `t`, `3·listBound D` and `capC D L`. -/
def blkSize (D : ListData) (gis : List ℕ) (G row t : ℕ) (sgn : Bool) (olen : ℕ) : ℕ :=
  olen + (Streaming.marks (true :: blockC D gis.length t sgn false (CompilerMachine.Pool.labsOf G row gis))).length +
    (FinalPass.ListEval.levelWord D.M D.J D.W (FinalPass.ListEval.rowsOf D gis.length)).length + (gisWord gis).length +
    (G + 1) * (4 * row + 4) + t + 3 * ListMachine.listBound D + capC D gis.length

/-! ## The row's capacities (stage 7) -/

/-- Route B's size measure: the digit lists' counting capacity `(8L+2)^{3·lb+1}` and the row's numbers. -/
def radX (M τ Lmax Mlab lb lw p b0 : ℕ) : ℕ :=
  (8 * Lmax + 2) ^ (3 * lb + 1) + M + τ + Lmax + Mlab + lb + lw + p + b0 + 2

/-- The power scale `U = 2^20·radX`. -/
def radU (M τ Lmax Mlab lb lw p b0 : ℕ) : ℕ := 2 ^ 20 * radX M τ Lmax Mlab lb lw p b0

/-- Route B's scrub capacity `R = U^40` (its log capacity is `R + 1`). -/
def radRB (U : ℕ) : ℕ := U ^ 40

/-- Route B's loop capacity `cap = U^45`. -/
def radCapB (U : ℕ) : ℕ := U ^ 45

/-- The Route-B request at the measure's numbers. -/
def reqB (r : RadReq) (Lmax Mlab lb lw : ℕ) : RadReqB :=
  ⟨r, radRB (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0),
    radRB (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0) + 1,
    radCapB (radU r.D.M r.digs.length Lmax Mlab lb lw r.p r.b0)⟩

/-- **Stage 7 (a), the capacities** (C1b): at an admissible request whose digit lists have at most `Lmax`
occurrences, exactly four labels per occurrence, labels at most `Mlab`, `listBound D ≤ lb` and table word at `Lmax` of
length at most `lw`, Route B's capacities meet the row's conditions. -/
def RadCapsStmt : Prop :=
  ∀ (r : RadReq) (Lmax Mlab lb lw : ℕ), r.Pre → ListMachine.listBound r.D ≤ lb →
    (∀ dg ∈ r.digs, dg.1 ≤ Lmax ∧ dg.2.length = 4 * dg.1 ∧ ∀ lab ∈ dg.2, lab ≤ Mlab) →
    (FinalPass.ListEval.levelWord r.D.M r.D.J r.D.W (FinalPass.ListEval.rowsOf r.D Lmax)).length ≤ lw →
    (reqB r Lmax Mlab lb lw).Caps

end NearCubicWires.WireExponent3_5.UnionMachine.RadSpec
