import Proof.Wire_3_5.Selection.GateDefs
import Proof.Wire_3_5.Selection.SortPlan

/-! # C1.4 plan: one gate's row counts at one coset, in the word layer (P3:1337-1358)

Paper: "Enumerate its `2^k` error rows. For each gate and row, the four threshold predicates have integer scores of
the form `a_j(z_L) + b_j(z_R)` [...] Enumerate each half's score vectors. For each of the sixteen corner patterns,
count pairs satisfying its four weak inequalities [...] The pattern determines whether the mixed residual is nonzero.
Sum its exact count" (P3:1339-1358).

This module states C1.4's interface as a type, for the coset loop (C1.5) to consume: **`GateSpec`**. A gate routine
reads the coset counter `N` (stream `NS`, the `k`-bit word of `N`), the gate record in coordinate order (stream `GA`:
each weight's sign cell and framed width-`W` magnitude, then the threshold's, `gateRec`), the key offset `2^V` (stream
`OF`) and the partition's shape in unary registers (`h`, `b`, `s`, the free counts, `V + 1`), and adds the gate's row
counts at the coset (`gateRows P σ g`, `σ = translationOfCodes (codesOfIdx s r N)`) to the width-`W` number `TX`.
Its scratch streams start empty or at their working length (`sl`) and end at their working length, so the caller
keeps one invariant across calls without knowing the lengths. Paper quantity: a gate's row counts at a coset. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SelectionMachine.Math NearCubicWires.WireExponent3_5.SelectionMachine.Sort

/-- A signed number's record: its sign cell, then its framed width-`W` magnitude. -/
def wRec (W : ℕ) (w : ℤ) : List Bool := decide (w < 0) :: frame (binary W w.natAbs)

/-- **The gate record**: the weights in coordinate order, then the threshold. -/
def gateRec (W : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  (List.ofFn fun i : Fin n => wRec W (g.weight i)).flatten ++ wRec W g.threshold

variable {ns nr : ℕ}

/-- The gate routine's streams and registers. -/
structure GateLayout (ns nr : ℕ) where
  /-- the coset counter, the gate record, the key offset `2^V`, the accumulator -/
  NS : Fin (ns + 1)
  GA : Fin (ns + 1)
  OF : Fin (ns + 1)
  TX : Fin (ns + 1)
  /-- the partition's shape: `h`, `b`, `s`, the free counts, `V + 1` -/
  Rh : Fin nr
  Rb : Fin nr
  Rs : Fin nr
  RfL : Fin nr
  RfR : Fin nr
  RV : Fin nr
  /-- the scratch streams and registers -/
  scS : List (Fin (ns + 1))
  scR : List (Fin nr)

/-- **The caller's side of a gate call.** -/
def GateReady (L : GateLayout ns nr) (sl : Fin (ns + 1) → ℕ) (σ : WState ns nr) (P : StarParams) (N W V : ℕ)
    (g : NormalizedThresholdGate P.n) : Prop :=
  σ.st L.NS = frame (binary (P.r * P.s) N) ∧ σ.sh L.NS = 0 ∧ σ.st L.GA = gateRec W g ∧ σ.sh L.GA = 0 ∧
    NumOn σ L.OF W (2 ^ V) ∧ σ.val L.Rh = hh P ∧ σ.val L.Rb = P.b ∧ σ.val L.Rs = P.s ∧ σ.val L.RfL = fL P ∧
    σ.val L.RfR = fR P ∧ σ.val L.RV = V + 1 ∧
    (∀ i ∈ L.scS, (σ.st i = [] ∨ (σ.st i).length = sl i) ∧ σ.sh i = 0) ∧ (∀ r ∈ L.scR, σ.val r = 0)

/-- **The gate routine** (the interface C1.5 consumes): at a coset `N < 2^k`, with the key width `V` meeting the gate's
`KeyBound` and the word width `W` large enough (`2V + 3 ≤ W`, `n + k + 4 ≤ W`), `TX` gains `gateRows P σ g`; every
other stream keeps its contents, the scratch streams end at their working lengths `sl P W`, and the heads, the
registers and the cell come back. -/
def GateSpec (cap : ℕ) (P0 : WM ns nr) (L : GateLayout ns nr) (sl : StarParams → ℕ → Fin (ns + 1) → ℕ)
    (capNeed cost : StarParams → ℕ → ℕ → ℕ) : Prop :=
  ∀ (σ : WState ns nr) (P : StarParams) (N W V : ℕ) (g : NormalizedThresholdGate P.n) (tx : ℕ),
    N < 2 ^ (P.r * P.s) → GateReady L (sl P W) σ P N W V g → NumOn σ L.TX W tx → KeyBound g V →
    2 * V + 3 ≤ W → P.n + P.k + 4 ≤ W →
    tx + gateRows P (P.translationOfCodes (codesOfIdx P.s P.r N)) g < 2 ^ W → capNeed P W V ≤ cap →
    ∃ τ : WState ns nr, WExec cap P0 σ τ (cost P W V) ∧
      τ.st L.TX = frame (binary W (tx + gateRows P (P.translationOfCodes (codesOfIdx P.s P.r N)) g)) ∧
      (∀ i, i ≠ L.TX → i ∉ L.scS → τ.st i = σ.st i) ∧ (∀ i ∈ L.scS, (τ.st i).length = sl P W i) ∧
      τ.sh = σ.sh ∧ τ.val = σ.val ∧ τ.cell = σ.cell

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
