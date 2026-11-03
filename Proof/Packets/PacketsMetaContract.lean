import Proof.Packets.PacketsCursorOrder

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## The values (each pinned by an accepted definition) -/

/-- The family's occurrence list. -/
abbrev occ (a : DecompositionAlgorithm) (r : Request) := (r.family a).occurrences
/-- The live set (the cyclic-choice mask; it is IN the input, part 3). -/
abbrev live (a : DecompositionAlgorithm) (r : Request) := Packets.live (r.family a)

/-- `pop`: the number of occurrences. -/
def pop (a : DecompositionAlgorithm) (r : Request) : ℕ := (occ a r).length
/-- `B = touchingCost`: occurrences whose support meets the live set. -/
def touch (a : DecompositionAlgorithm) (r : Request) : ℕ := LiveRows.bound (occ a r) (live a r)
/-- `depth = canonicalGradedDepth B = clog₂ (256·B)`. -/
def depth (a : DecompositionAlgorithm) (r : Request) : ℕ := canonicalGradedDepth (touch a r)
/-- `rank = max depth (clog₂ pop)`. -/
def rank (a : DecompositionAlgorithm) (r : Request) : ℕ := canonicalGradedRank (pop a r) (touch a r)
/-- The walk length `canonicalWalkLength (Request.denominator a r)`. -/
def walkLength (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  canonicalWalkLength (Request.denominator a r)
/-- The request degree (max row degree). -/
def degree (a : DecompositionAlgorithm) (r : Request) : ℕ := Request.degree a r
/-- The seed count (the cursor's field-5 bound). -/
def seedCount (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (Packets.seedList (occ a r) (live a r) (Request.denominator a r)).length

/-! ## The stage shapes -/

/-- **One scalar, one fixed machine.** Entry: the framed input on tape 0, every other tape empty,
all heads 0. Exit: tape 0 and its head unchanged; tape 1 = `replicate (v r) true`, head 0; the private
tapes `2..` are existential. Cost a fixed power of `smallSize`. -/
structure UnaryStage (a : DecompositionAlgorithm) (v : Request → ℕ) where
  extra : ℕ
  states : ℕ
  machine : Machine (2 + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ r, ∃ (H' : Fin (2 + extra) → ℕ) (A' : Fin (2 + extra) → List Bool),
    Step machine (cost r) (fun _ => 0) (inBank (2 + extra) (Request.input a r)) H' A' ∧
    A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
    A' ⟨1, by omega⟩ = List.replicate (v r) true ∧ H' ⟨1, by omega⟩ = 0

/-! ## Facts the consumers use -/

end
end NearCubicWires.PacketsGlue.RequestMeta

