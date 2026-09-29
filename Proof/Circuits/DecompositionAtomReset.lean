import Proof.Circuits.DecompositionMagnitudeSerializer

/-! The complete signed atom in a finite reusable bank. Only the original
native source cursor stays live; every local head is physically rewound. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtomReset
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem pad_trailing (capacity : ℕ) (bits : List Bool) (n : ℕ)
    (hb : bits.length+n ≤ capacity) :
    ZeroPadding.pad capacity (bits++List.replicate n false)=ZeroPadding.pad capacity bits := by
  simp only [ZeroPadding.pad,List.length_append,List.length_replicate,List.append_assoc,
    ←List.replicate_add]
  congr 2
  omega

end NearCubicWires.RepairOrdinary.DecompositionAtomReset
