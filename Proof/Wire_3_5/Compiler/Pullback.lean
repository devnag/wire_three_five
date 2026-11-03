import Proof.Wire_3_5.Compiler.Substitute
import Proof.Wire_3_5.Stars.StarSelection

/-! # `alg:pullback`: pullback of the disjoint exact children to two column halves (P3:1623-1676)

Realizes: "Partition a column variable `z` as `(z_L, z_R)`. For every fixed row `y`, suppose each original input
coordinate has the form `x_i = φ_{i,y}(z_L)` (`i ∈ I_L`), `x_i = φ_{i,y}(z_R)` (`i ∈ I_R`) [...] Decompose an
original-coordinate threshold using Lemma alg:disjoint, and then substitute these coordinate functions. Every child
becomes an equation `E_{j,y}(z) = a_{j,y}(z_L) + b_{j,y}(z_R) = 0` [...] The children remain disjoint and represent the
pulled-back threshold exactly, both over the integers and over `𝔽₂`" (P3:1627-1641), by the paper's proof "Write an
original child as `c_j + Σ_i d_{j,i}x_i = 0`. Put its constant in the left half, sum the terms indexed by `I_L` in
`a_{j,y}`, and sum the remaining terms in `b_{j,y}`" (P3:1645-1648); and its star instance: "In the product-star
parametrization, keep each entire code block on one column side. Each coordinate of its center, including the subsequent
exclusive-or with a fixed error row, then depends on that column side alone" (P3:1655-1658).

The disjoint exact children are the base's `ExactDecomposition` (the imported `alg:disjoint` interface, P3:1596-1621).

Main declarations: `HalfCoords` (coordinates read from one column half), `pullChild` (the pulled-back child, a
`SeparatedEquation`), **`pullChild_holds`** (it holds exactly where the original child holds), **`pullbackChildren`** (the
ref) with **`pullback_exact`** (the children stay disjoint and exact for the pulled-back threshold); `labelChildren` (the
children of a list of atoms numbered as one pool, in the compiler's `ExactChildren` form) with `labelChildren_exact`;
`starCoords` (the star instance: the corner points `c+u+v`, `c+u`, `c+v`, `c` from the center halves) with
**`starCoords_point`** and **`starCoords_corners`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

variable {n : ℕ} {ZL ZR : Type}

/-- Every original coordinate is read from one column half (P3:1627-1631): `side i` says which. -/
structure HalfCoords (n : ℕ) (ZL ZR : Type) where
  side : Fin n → Bool
  φL : ZL → Fin n → Bool
  φR : ZR → Fin n → Bool

/-- **The pulled-back child** (P3:1645-1648): the constant and the left terms in `a(z_L)`, the right terms in `b(z_R)`. -/
def pullChild (C : HalfCoords n ZL ZR) (e : ExactThresholdGate n) : SeparatedEquation ZL ZR :=
  ⟨fun zl => -e.target + ∑ i, if C.side i then e.weight i * bitZ (C.φL zl i) else 0,
   fun zr => ∑ i, if C.side i then 0 else e.weight i * bitZ (C.φR zr i)⟩

/-- **The pulled-back children** of an exact decomposition (the ref, P3:1636-1641). -/
def pullbackChildren (C : HalfCoords n ZL ZR) {g : NormalizedThresholdGate n} (D : ExactDecomposition g) :
    List (SeparatedEquation ZL ZR) :=
  D.children.map (pullChild C)

/-! ## Numbering the children of a list of atoms as one pool -/

theorem sum_map_eq_range_getD {β : Type} (l : List β) (d : β) (g : β → ℤ) :
    (l.map g).sum = ((List.range l.length).map fun j => g (l.getD j d)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.getD_cons_zero]
    rw [ih]
    congr 1

/-! ## The star instance (P3:1655-1664) -/

end NearCubicWires.WireExponent3_5.Compiler
