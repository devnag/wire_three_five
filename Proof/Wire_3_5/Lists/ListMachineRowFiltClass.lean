import Proof.Wire_3_5.Lists.ListMachineRowFiltInst

/-! # C2 rows, part 29: the FILTER row's machine contract

The per-row contract of FILTER rows (the factor `E_G` of SYM entries, and of THR entries) in the seed's `c2` shape:

* `Req`: the fixed filter seed `(P, e)` (`filt:gap`, P3:2016-2104), the population (sign, `L` occurrences, corner labels)
  and the call width `n`;
* `input`: the computable row record `filtRecC` — the factor block with C5's table word
  `tableWord (filterTable P e L)` as the evaluator's data (C5's `stage6_step` builds it,
  `tableBits_eq`);
* `pre`: the labels cover the corners, `n ≥ 1`, and the LOAD CONDITION: the row's explicit cost bound `filtCostC` is
  within the preprocessing class at `(n, B.kOf n, B.psiOf n)`;
* `ref`/`encode`: the computable one-term, one-factor reference `filtRefC` and `exprWord`;
* `errSpec`: at EVERY assignment of the corner pool the reference takes the value of the seed's regular filter
  `gapFilter P e` at the population point `Z^± = popBits sgn X` (P3:2653-2676).

**`filtBlocks`**: the `ClassBlocks` of the contract; **`filtCertified`**: `Certified filtContract`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.ListMachine.Ref Finset
open NearCubicWires.WireExponent3_5.ListMachine (Poly Expr)
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.BlockPlatform NearCubicWires.SupplierWalk

/-- A FILTER row's population and call width. -/
structure FiltPop where
  L : ℕ
  sgn : Bool
  labs : List ℕ
  n : ℕ

/-- A FILTER row request: the fixed filter seed `(P, e)`, the population, the call width. -/
def FiltReq : Type := Σ P : GapParams, GapSeed P × FiltPop

def FiltReq.P (r : FiltReq) : GapParams := r.1
def FiltReq.e (r : FiltReq) : GapSeed r.P := r.2.1
def FiltReq.L (r : FiltReq) : ℕ := r.2.2.L
def FiltReq.sgn (r : FiltReq) : Bool := r.2.2.sgn
def FiltReq.labs (r : FiltReq) : List ℕ := r.2.2.labs

/-- The request's table and threshold. -/
def FiltReq.tbl (r : FiltReq) : List (List (List Bool)) := Filt.filterTable r.P r.e r.L
def FiltReq.thr (r : FiltReq) : ℕ := majorityThreshold r.P.walkLen

theorem FiltReq.hlen (r : FiltReq) : ∀ vs ∈ r.tbl, ∀ cs ∈ vs, cs.length ≤ r.L :=
  fun vs hvs cs hcs => (Filt.filterTable_lengths r.P r.e r.L vs hvs cs hcs).le

/-- **The FILTER row's value is the seed's regular filter** at the population point, at every assignment. -/
theorem filtRow_value (r : FiltReq) (σ : ℕ → Bool) :
    IntExpression.eval (filtRefC r.tbl r.thr r.L r.sgn r.labs) σ =
      bitInt (gapFilter r.P r.e (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ))) := by
  have hX : (readX (4 * r.L) r.labs σ).length = 4 * r.L := by simp [readX]
  have hZ := Pop.popBits_length r.sgn r.L _ hX
  have hv := filtPoly_eval r.thr r.tbl r.L r.hlen r.sgn r.labs σ
  rw [gapFilter_eq_filterBits, Filt.filterBits_eq_tab, hZ]
  simp only [filtRefC, IntExpression.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    List.sum_cons, List.sum_nil]
  rw [hv]
  have e1 : Filt.tabEval (majorityThreshold r.P.walkLen) (Filt.filterTable r.P r.e r.L)
      (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) = Filt.tabEval r.thr r.tbl (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) :=
    rfl
  rw [e1]
  cases Filt.tabEval r.thr r.tbl (Pop.popBits r.sgn (readX (4 * r.L) r.labs σ)) <;> simp [bitZ, bitInt]

/-! ## The word-function run -/

/-! ## The class blocks and the certificate -/


end NearCubicWires.WireExponent3_5.ListMachine.Row
