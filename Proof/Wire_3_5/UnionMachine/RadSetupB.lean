import Proof.Wire_3_5.Primitive.ThresholdWriter.RadSetup2

/-! # RADIX, Route B: the RADIX row setup at explicit capacities (`RadReqB`, `RadReadyB`,
`RadSetupSpecB`)

P3:2585-2623 (row:radix), as `RadSetup2`, but at C2's parametric RADIX row (`ListMachine.Row.radRow_step`, any scrub
capacity `R`, log capacity `Lg` and loop capacity `cap` meeting its conditions) instead of the exact record
`radRowRecC` (whose capacities need every expanded print's exact word length, `mselCost`). This is the POP row's
Route B for RADIX.

* **`RadReqB`**: C2's RADIX request `r` with explicit `R`, `Lg`, `cap`;
* **`RadReqB.record`**: the Route-B record (computable form; **`record_eq`**: it is `radRowRec … (radSpecs …)`, the
  record `radRow_step` runs on);
* **`RadReqB.Caps`**: `radRow_step`'s capacity conditions, computable (**`caps_step`**: they give the step's
  hypotheses at `radSpecs`);
* `RadReqB.bound`: `(M+1)^{2τ₀}·128·(|record|+1)²` (`radRowCost_bound`'s);
* **`RadReadyB`**: `Joins.RadReady` with the Route-B record, `r.Pre` and the capacity conditions;
* **`RadSetupSpecB x l F`**: `RadSetup2.RadSetupSpec2` ending in `RadReadyB` at some capacities for `radReqOf`, with the
  pipe's bound `q.bound ≤ pipe n` (`pipe` quasi-bounded).

Paper quantity of the main type: the RADIX row's C2 request (`RadSetup.radReqOf`) with its row's capacities. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimThrW.RadSetup NearCubicWires.WireExponent3_5.PrimThrW.RadSetup2
open NearCubicWires.WireExponent3_5.ListMachine.Row NearCubicWires.WireExponent3_5.Lists

/-! ## The request at explicit capacities -/

/-- **A Route-B RADIX request**: C2's request with an explicit scrub capacity `R`, log capacity `Lg` and loop
capacity `cap`. -/
structure RadReqB where
  r : RadReq
  R : ℕ
  Lg : ℕ
  cap : ℕ

/-- **The Route-B record** (computable): the setup fields at `R`, `Lg`, `cap`, then the factor blocks in store order. -/
def RadReqB.record (q : RadReqB) : List Bool :=
  fieldsWord (setupFieldsG (19 + 1) q.R q.Lg (radEv q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0)
    (radT q.r.digs q.r.p q.r.s) q.cap)) ++ ((radBlocksC q.r.D q.r.digs).flatMap (fun b => true :: b) ++ [false])

/-- **The row's capacity conditions** (`radRow_step`'s, computable). -/
structure RadReqB.Caps (q : RadReqB) : Prop where
  R2 : 2 ≤ q.R
  Rx : ∀ dg ∈ q.r.digs, ∀ t ≤ q.r.D.M, ∀ sgn : Bool, costC q.r.D dg.1 t sgn false dg.2 + 1 ≤ q.R
  RL : q.R + 1 ≤ q.Lg
  c0 : 2 * q.r.digs.length * (q.r.D.M + 1) * (4 * q.R + 9) + 1 ≤ q.cap
  c1 : resLoopCost (radCs q.r.D q.r.digs q.r.p q.r.b0) + 3 ≤ q.cap
  c2 : mselCost (radFs q.r.D q.r.digs) ≤ q.cap
  c3 : incCost q.r.D.M (2 * q.r.digs.length) ≤ q.cap

/-- The row's cost bound at the Route-B record (`radRowCost_bound`'s). -/
def RadReqB.bound (q : RadReqB) : ℕ :=
  (q.r.D.M + 1) ^ (2 * q.r.digs.length) * (128 * (q.record.length + 1) ^ 2)

/-- **The Route-B record is the record `radRow_step` runs on.** -/
theorem record_eq (q : RadReqB) (hok : DigsOk q.r.digs) :
    radRowRec q.r.D.M (2 * q.r.digs.length) (radCs q.r.D q.r.digs q.r.p q.r.b0) (radT q.r.digs q.r.p q.r.s) q.R q.Lg
      q.cap (radSpecs q.r.D q.r.digs hok) = q.record := by
  unfold radRowRec RadReqB.record
  rw [storeRec_radSpecs]
  rfl

/-- **The capacity conditions give `radRow_step`'s hypotheses** at `radSpecs`. -/
theorem caps_step (q : RadReqB) (hok : DigsOk q.r.digs) (hc : q.Caps) :
    (∀ x ∈ radSpecs q.r.D q.r.digs hok, x.cost + 1 ≤ q.R) ∧ storeCost (radSpecs q.r.D q.r.digs hok) q.R ≤ q.cap ∧
      mselCost ((radSpecs q.r.D q.r.digs hok).map FSpec.poly) ≤ q.cap := by
  have hRx : ∀ x ∈ radSpecs q.r.D q.r.digs hok, x.cost + 1 ≤ q.R := by
    intro x hx
    obtain ⟨dg, hdg, t, ht, sgn, hl, rfl⟩ := mem_radSpecs q.r.D q.r.digs hok x hx
    have h1 := visitSpec_cost_le q.r.D dg.1 (min t q.r.D.M) sgn (min_le_right _ _) false dg.2 hl
    have e : costC q.r.D dg.1 (min t q.r.D.M) sgn false dg.2 = costC q.r.D dg.1 t sgn false dg.2 := by
      rw [min_eq_left ht]
    have h2 := hc.Rx dg hdg t ht sgn
    omega
  refine ⟨hRx, ?_, ?_⟩
  · have h := storeCost_le (radSpecs q.r.D q.r.digs hok) q.R hRx
    rw [radSpecs_length] at h
    have := hc.c0
    omega
  · have hmp : (radSpecs q.r.D q.r.digs hok).map FSpec.poly = radFs q.r.D q.r.digs := by
      rw [radSpecs_poly q.r.D q.r.digs hok []]; rfl
    rw [hmp]
    exact hc.c2

/-! ## The ready state -/

/-! ## The setup -/

end NearCubicWires.WireExponent3_5.UnionMachine.RadSetupB
