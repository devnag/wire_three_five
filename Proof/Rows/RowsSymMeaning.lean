import Proof.Rows.NativeFamilyFlags

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.SymMeaning
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open scoped BigOperators
noncomputable section

/-! ## 1. The SYM circuits in the flag traversal's shape -/

def symGates {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List (NormalizedThresholdGate q) :=
  List.ofFn (fun i => (c.bottom i).gate)

def symTop {q : Nat} (c : NormalizedSymmetricThresholdCircuit q) : List Bool := List.ofFn c.top

def circuits (r : FourfoldRequest NormalizedSymmetricThresholdCircuit) :=
  r.circuits.map (fun c => (symGates c, symTop c))

/-! ## 2. The flag word -/

/-! ## 3. Prefix counts -/

/-! ## 4. Cumulative equality is per-block equality -/

/-! ## 5. The per-slot numbers and the SYM verdict -/

variable (r : FourfoldRequest NormalizedSymmetricThresholdCircuit)

/-- Number of bottom gates of circuit `c` (0 past the last circuit): request-only, cell-free. -/
def gateCount (c : Nat) : Nat := (r.circuits.map (fun k => (symGates k).length)).getD c 0

/-- Driver length for slot `c`: the flag position just after circuit `c`'s last gate flag. -/
def driverLen (c : Nat) : Nat :=
  if c < r.circuits.length then (∑ i ∈ Finset.range c, (gateCount r i + 1)) + gateCount r c else 0

/-- The offset tuple, extended by `0`. -/
def offsetN (offset : Fin r.circuits.length → Nat) (c : Nat) : Nat :=
  if h : c < r.circuits.length then offset ⟨c, h⟩ else 0

/-- Target for slot `c`: the cumulative target count. -/
def targetCount (offset : Fin r.circuits.length → Nat) (c : Nat) : Nat :=
  if c < r.circuits.length then (∑ i ∈ Finset.range c, (offsetN r offset i + 1)) + offsetN r offset c
  else 0

end
end RowsConstruction.SymMeaning
