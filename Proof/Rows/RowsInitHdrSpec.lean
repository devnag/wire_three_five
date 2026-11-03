import Proof.Rows.RowsPartsStep

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.Hdr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

variable (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (printer : WilliamsAlgorithm)

/-- The Header writer's entry bank. -/
def hdrIn (needH : ℕ) (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps) :
    Fin (440 + 4 + needH) → List Bool := fun i =>
  if i.val = 0 then exactListWord (Packets.pool a (r.family a) (geometryOf selector a r))
  else if i.val = 262 then r.raw selector a
  else if i.val = 440 then frame (r.input a)
  else if i.val = 441 then rowMetadataWord layout.w layout.degree layout.C caps
  else if i.val = 442 then List.replicate (2 * caps.headerFuel) true
  else if i.val = 443 then List.replicate (2 * caps.headerFuel + 1) false
  else []

/-- The Header writer's exit heads: `1` on Header 277, `0` elsewhere. -/
def hdrOutH (needH : ℕ) : Fin (440 + 4 + needH) → ℕ := fun i => if i.val = 277 then 1 else 0

/-- **The Header writer, typed.** -/
structure HdrSpec where
  needH : ℕ
  states : ℕ
  machine : Machine (440 + 4 + needH) states
  cost : (r : Request) → Packets.Layout a (r.family a) (geometryOf selector a r) → RowCaps → ℕ
  coefficient : ℕ
  degree : ℕ
  run : ∀ (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) (caps : RowCaps),
    RowCaps.Good selector a printer r layout facts caps → (r.family a).rows ≠ [] →
    ∃ A' : Fin (440 + 4 + needH) → List Bool,
      Step machine (cost r layout caps) (fun _ => 0) (hdrIn selector a needH r layout caps) (hdrOutH needH) A' ∧
      (∀ k : Fin 440, A' ⟨k.val, by omega⟩ = ZeroPadding.pad (RowsConstruction.PartsStep.reserveOf caps k)
        (PCJ45bee56da9f34d5a_RowState.commonHeader a (r.family a) (geometryOf selector a r) layout k)) ∧
      A' ⟨440, by omega⟩ = frame (r.input a) ∧
      A' ⟨441, by omega⟩ = rowMetadataWord layout.w layout.degree layout.C caps ∧
      A' ⟨442, by omega⟩ = List.replicate (2 * caps.headerFuel) true ∧
      A' ⟨443, by omega⟩ = List.replicate (2 * caps.headerFuel + 1) false
  cost_le : ∀ (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (caps : RowCaps),
    cost r layout caps ≤ coefficient * ((r.smallSize a) ^ degree + caps.headerFuel + layout.C + caps.copyCap +
      (rowMetadataWord layout.w layout.degree layout.C caps).length + 1)

end
end RowsInit.Hdr
