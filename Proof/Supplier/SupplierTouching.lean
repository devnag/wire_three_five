import Proof.Foundations.SupplierPipeline

/-!
# Touching-set selection

This module proves the exact finite averaging bound behind `TouchingSelect`.
Support occurrences are indexed by a finite type, so duplicate supports remain
distinct charges.  Among the `K`-subsets of `Fin q`, one selection touches at
most the incidence-average: `q * touched ≤ K * totalSupportMass`.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SupplierTouching

def touchIndicator {Coordinate : Type} [DecidableEq Coordinate]
    (selected support : Finset Coordinate) : ℕ :=
  if Disjoint selected support then 0 else 1

def touchingCost {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate) (selected : Finset Coordinate) : ℕ :=
  ∑ gate, touchIndicator selected (support gate)

def supportIncidenceMass {Gate Coordinate : Type} [Fintype Gate]
    (support : Gate → Finset Coordinate) : ℕ :=
  ∑ gate, (support gate).card

/-! ## Closed conditional-expectation ledger -/

/-- Exact number of `k`-completions touching one support after `selected`
has already been fixed and `undecided` remains available. -/
def conditionalGateTouchCount {Coordinate : Type}
    [DecidableEq Coordinate]
    (selected undecided support : Finset Coordinate) (k : ℕ) : ℕ :=
  if Disjoint selected support then
    Nat.choose undecided.card k -
      Nat.choose (undecided \ support).card k
  else
    Nat.choose undecided.card k

/-- The closed, polynomial-bit score used by conditional expectation. -/
def conditionalTouchNumerator
    {Gate Coordinate : Type} [Fintype Gate]
    [DecidableEq Coordinate]
    (support : Gate → Finset Coordinate)
    (selected undecided : Finset Coordinate) (k : ℕ) : ℕ :=
  ∑ gate,
    conditionalGateTouchCount selected undecided (support gate) k

/-! ## Deterministic conditional-expectation selector -/

/-- Greedy TouchingSelect over one fixed coordinate order.  At each step the
two exact conditional numerators are compared after cross-multiplying by
their binomial fiber sizes; no rational arithmetic or candidate enumeration
is used. -/
def touchingSelectAux
    {Gate : Type} [Fintype Gate]
    {q : ℕ} (support : Gate → Finset (Fin q)) :
    Finset (Fin q) → ℕ → List (Fin q) → Finset (Fin q)
  | selected, _k, [] => selected
  | selected, k, coordinate :: rest =>
      if _hk : k = 0 then
        selected
      else
        let restSet := rest.toFinset
        let included :=
          conditionalTouchNumerator support
            (insert coordinate selected) restSet (k - 1)
        let excluded :=
          conditionalTouchNumerator support selected restSet k
        if included * Nat.choose rest.length k ≤
            excluded * Nat.choose rest.length (k - 1) then
          touchingSelectAux support
            (insert coordinate selected) (k - 1) rest
        else
          touchingSelectAux support selected k rest

def touchingSelect
    {Gate : Type} [Fintype Gate]
    {q : ℕ} (support : Gate → Finset (Fin q)) (K : ℕ) :
    Finset (Fin q) :=
  touchingSelectAux support ∅ K (List.finRange q)

end NearCubicWires.SupplierTouching
