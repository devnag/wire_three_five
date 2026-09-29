import Proof.MachineModel.BlockLoop

/-! # Block v3 (S5): typed port maps and the "only these ports moved" calculus

Paper: every component of the primitive is a multitape program. `prim:runtime` (P3:3105-3108) sums
their running times, and each runs "without recomputing" the retained fields of its caller (e.g. the
final pass, P3:3046-3048: "At each of `2^{n−k}` columns, evaluate the reported lookup at these `Q`
pairs"). The column, the reported lookup and the samples stay on their tapes while each stage works
on its own ports.

The paper quantity of this module is the tape layout of such a program, i.e. which tapes each stage
reads and writes. A `PortMap t u` places a `t`-tape worker among `u` ambient tapes. `Moves b M` says
the block `b` changed at most the tapes marked `M` (heads and contents). Four facts compose it:
- a docked worker moves only its ports (`moves_dock`);
- sequencing unions the moved sets (`moves_seq`);
- embedding and the paid masked reset move no extra tape (`moves_embedded`, `moves_masked`);
- the value on an unmoved tape is read through a whole chain in one step (`Moves.exitA`,
  `seq_exitA_right`).

This replaces the per-tape `fin_cases`/`pick = none` chains that every Theorem 2.5 composition
re-proved. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform

/-! ## Port maps -/

/-- A typed port map: a worker's `t` tapes placed injectively among `u` ambient tapes. -/
structure PortMap (t u : ℕ) where
  slot : Fin t → Fin u
  inj : Function.Injective slot

namespace PortMap
variable {t u v : ℕ}

/-- A concrete layout from a vector, with injectivity checked by `decide`. -/
def ofVec (s : Fin t → Fin u) (h : Function.Injective s) : PortMap t u := ⟨s, h⟩

end PortMap

/-! ## Moves -/

namespace Moves

end Moves

/-! ## The generators -/

section
variable {t u e : ℕ}

/-- Docking along a port map. -/
noncomputable def dock (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) : Block u :=
  focusedInto b P.slot P.inj H A hH hA

@[simp] theorem dock_cost (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    (dock b P H A hH hA).cost = b.cost := rfl

@[simp] theorem dock_entryH (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    (dock b P H A hH hA).entryH = H := rfl

@[simp] theorem dock_entryA (b : Block t) (P : PortMap t u) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (P.slot j) = b.entryH j) (hA : ∀ j, A (P.slot j) = b.entryA j) :
    (dock b P H A hH hA).entryA = A := rfl

end

/-! ## A tiny executable check of a concrete layout -/



end NearCubicWires.WireExponent3_5.Block
