import Proof.Wire_3_5.Compiler.MachinePoolLabels

/-! # C3a, the pool builder: the contract (P3:1596-1664)

Paper: alg:disjoint (P3:1596-1621) "There is an explicitly constructible list of at most `max(1, fℓ)` integer affine
equations `E_j(x) = 0` such that `H(x) = Σ_j 1[E_j(x) = 0]` on the Boolean cube, with the sum always in `{0,1}`", and
alg:pullback (P3:1624-1650) "Every child becomes an equation `E_{j,y}(z) = a_{j,y}(z_L) + b_{j,y}(z_R) = 0` [...] The
children remain disjoint and represent the pulled-back threshold exactly", in the star instance (P3:1655-1664).

The five-field unit (`Machine.MachineContract`) of the pool builder, approved as (with the P/N encoding of): the request is the carrier gates, the side of every original coordinate, the dense width and the flip patterns
(corners of star rows); the reference is `densePool` (each child as its dense weights and target); the output words
are the pool stream (`poolRecs`, word (1)) and the children table (word (2)); the class is preprocessing. The error
field is the paper's exactness at every center assignment: the number of holding children of atom `i·G + gi` is the
value of gate `gi` at the pulled-back point of flip pattern `i`.

Main declarations: `PoolReq`, `PoolReq.Pre`, `holdsL`, `eval_eq_holdsL`, `denseRef`, **`c3a`**, **`c3a_err`**,
**`c3a_not_nil`** (the empty pool fails the error field). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.Machine NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary (frame)

/-- The pool builder's request: the carrier gates of the call, the side of each original coordinate,
the dense width, the flip patterns (`4·rowIdx + k`), the P/N field width `h`, the lift precision `Q'`, the load. -/
structure PoolReq where
  n : ℕ
  gates : List (SupportedNormalizedGate n)
  side : List Bool
  width : ℕ
  flips : List (List Bool)
  h : ℕ
  Q : ℕ
  psi : ℕ

/-- The admissible requests: sides and flips of length `n`, both sides fit the width. -/
def PoolReq.Pre (R : PoolReq) : Prop :=
  R.side.length = R.n ∧ (∀ f ∈ R.flips, f.length = R.n) ∧ nLeft R.side R.n ≤ R.width ∧ nRight R.side R.n ≤ R.width

theorem getD_map_map {α β : Type} (f : α → β) (l : List (List α)) (i : ℕ) :
    (l.map (List.map f)).getD i [] = (l.getD i []).map f := by
  by_cases h : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    rfl


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
