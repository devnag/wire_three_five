import Proof.MachineModel.OrdinaryMemoryInitialLoop

/-! Apply the physical framed loop at the exact chronological initialization
events used in the verifier soundness theorem and memory-checker input. -/
namespace NearCubicWires.RepairOrdinary.MemoryInitialEmission
open LocalBitMultitape MemoryLog MemorySort
open MemoryInitialCell (config)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (I K W serial : ℕ) (events : List Event) : List Bool :=
  StablePartition.recordsBits ((events.zipIdx serial).map (fun p => encoded I K W p.2 p.1))

theorem writes_fields (I K W serial tape address : ℕ) (bits : List Bool) :
    MemoryInitialPair.records I K serial (cellCode W (tape,address)) bits =
      fields I K W serial (MemoryInitialization.writes tape address bits) := by
  induction bits generalizing serial address with
  | nil => simp [MemoryInitialPair.records, fields, MemoryInitialization.writes,
      StablePartition.recordsBits]
  | cons b bs ih =>
    have hcell : cellCode W (tape,address)+1 = cellCode W (tape,address+1) := by
      simp only [cellCode]
      omega
    simp only [MemoryInitialPair.records, hcell, ih, MemoryInitialization.writes,
      fields, List.zipIdx_cons, List.map_cons, StablePartition.recordsBits, List.flatMap_cons]
    rfl

theorem fields_append (I K W serial : ℕ) (xs ys : List Event) :
    fields I K W serial (xs++ys) =
      fields I K W serial xs ++ fields I K W (serial+xs.length) ys := by
  induction xs generalizing serial with
  | nil => simp [fields, StablePartition.recordsBits]
  | cons e es ih =>
    have hs : serial+1+es.length = serial+(es.length+1) := by omega
    change StablePartition.recordBits (encoded I K W serial e) ++
      fields I K W (serial+1) (es++ys) = _
    rw [ih]
    simp only [fields, List.zipIdx_cons, List.map_cons, StablePartition.recordsBits,
      List.flatMap_cons, List.length_cons, List.append_assoc, hs]

theorem initialization_fields (I K W : ℕ) (input witness : List Bool) :
    fields I K W 0 (MemoryInitialization.events input witness) =
      MemoryInitialPair.records I K 0 0 (frame input) ++
      MemoryInitialPair.records I K (frame input).length (2^W) (frame witness) := by
  rw [MemoryInitialization.events, fields_append, ← writes_fields, ← writes_fields]
  simp only [MemoryInitialization.writes_length, cellCode, Nat.zero_mul, Nat.zero_add,
    Nat.one_mul, Nat.add_zero]

end NearCubicWires.RepairOrdinary.MemoryInitialEmission
