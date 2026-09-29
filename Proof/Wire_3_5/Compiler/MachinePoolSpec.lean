import Proof.Wire_3_5.Compiler.MachinePoolRef
import Proof.Wire_3_5.Compiler.MachineMasksAll

/-! # C3a, the pool builder: the reference pool, its numbering, and its three output words (P3:1636-1664)

Paper: "For every fixed row `y` [...] Decompose an original-coordinate threshold using Lemma alg:disjoint, and then
substitute these coordinate functions. Every child becomes an equation `E_{j,y}(z) = a_{j,y}(z_L) + b_{j,y}(z_R) = 0`
[...] For `P` original atoms across the fixed rows, the child pool has size `P_ex ≤ P n^{O(1)}`" (P3:1627-1642), and
"For a common pool over all `2^k` rows and polynomially many original atoms, it gives `P_ex ≤ 2^k n^{O(1)}`"
(P3:1661-1664). The atoms are the carrier gates at the four corners `c+u+v, c+u, c+v, c` of every star row `(u,v)`:
a corner's flip pattern is the exclusive-or with the error row (P3:1656-1658), and a population bit is a polynomial of
the four corner atoms (`zPlusF2`, P3:2782-2783).

Reference: the pool is `densePool`, flip-major. Atom `i·G + gi` is gate `gi` of the `G` carrier gates
under flip pattern `i`, where pattern `i = 4·rowIdx + k` is corner `k` of star row `rowIdx`. Its children are the gate's
disjoint exact children (the literal's `DecompositionAlgorithm`) pulled back to dense center form (`pullDense`).
The three output words:
* `poolTable h`: the dense children's fields, FIELD-MAJOR (the stacking stage reads one field of every label per
  pass). Each field is a P/N pair `binary h P ++ binary h N` of naturals with `P − N` the field's value. The target's
  pair is `(T⁺ + Σ_{flipped, w<0}|w|, T⁻ + Σ_{flipped, w>0}|w|)` (`splitTarget`), so no subtraction is needed.
* `childTable Q' (shapeOf pool)`: each atom's child labels as size-`0` mask entries, C3.3's table.
* `labelWord (labsOf G rowIdx gis)`: the label table C2 prints from (4 corner atoms per gate occurrence).

The paper quantity of the main theorem is the exactness of the pool: **`densePool_exact`** (at every center
assignment, the number of holding children of atom `i·G + gi` is the value of gate `gi` at the pulled-back point of
pattern `i`), with `fieldPN_value` (the P/N pairs carry the dense child's fields). Main declarations: `pn`,
`splitTarget`, `denseWeights`, `fieldPN`, `poolChildren`, `densePool`, `poolIndex`, `labsOf`, `labelWord`, `shapeOf`,
`poolTable`, **`densePool_exact`**, `fieldPN_value`, `densePool_length`, `densePool_getD`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## P/N fields -/

/-- The canonical P/N parts of a signed value. -/
def pn (z : ℤ) : ℕ × ℕ := (z.toNat, (-z).toNat)

theorem pn_value (z : ℤ) : ((pn z).1 : ℤ) - (pn z).2 = z := by
  simp only [pn]; omega

/-- The split target of a pulled-back child: the flipped weights are added on opposite sides of the target's P/N
pair (P3:1645-1648 with the flips of P3:1656-1658). -/
def splitTarget (cs : List Coord) (t : ℤ) : ℕ × ℕ :=
  (t.toNat + (cs.map fun c => if c.2.1 then (-c.2.2).toNat else 0).sum,
   (-t).toNat + (cs.map fun c => if c.2.1 then c.2.2.toNat else 0).sum)

theorem splitTarget_value (cs : List Coord) (t : ℤ) :
    ((splitTarget cs t).1 : ℤ) - (splitTarget cs t).2 = t - flipSum cs := by
  unfold splitTarget flipSum
  have h0 := Int.toNat_sub_toNat_neg t
  induction cs with
  | nil => simp only [List.map_nil, List.sum_nil, Nat.add_zero, sub_zero]; exact h0
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    have h1 := Int.toNat_sub_toNat_neg c.2.2
    split_ifs <;> (try simp only [Nat.cast_zero, zero_add] at ih ⊢) <;> linarith

/-- The dense child's weights, left center coordinates then right center coordinates. -/
def denseWeights {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) : List ℤ :=
  padTo width (routeL (coords side f e)) ++ padTo width (routeR (coords side f e))

/-- Field `p` of the dense child as a P/N pair: a weight for `p < 2·width`, the split target for `p = 2·width`. -/
def fieldPN {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) (p : ℕ) : ℕ × ℕ :=
  if p < width + width then pn ((denseWeights side f width e).getD p 0)
  else splitTarget (coords side f e) e.target

/-- **The P/N pairs carry the dense child** (weights and target). -/
theorem fieldPN_value {n : ℕ} (side f : List Bool) (width : ℕ) (e : ExactThresholdGate n) (p : ℕ) :
    ((fieldPN side f width e p).1 : ℤ) - (fieldPN side f width e p).2 =
      if h : p < width + width then (pullDense side f width e).weight ⟨p, h⟩ else (pullDense side f width e).target := by
  unfold fieldPN
  split_ifs with h
  · rw [pn_value]; rfl
  · rw [splitTarget_value]; rfl

/-! ## The pool, its numbering and its words -/

variable (a : DecompositionAlgorithm)

/-- The pool's children with their flip patterns, in label order (flip-major, then gate, then child). -/
def poolChildren {n : ℕ} (gates : List (SupportedNormalizedGate n)) (flips : List (List Bool)) :
    List (List Bool × ExactThresholdGate n) :=
  flips.flatMap fun f => gates.flatMap fun g => (children a g).map fun e => (f, e)

/-- **The reference pool**: atom `i·G + gi` holds the dense children of gate `gi` under flip `i`. -/
def densePool {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) : List (List (ExactThresholdGate (width + width))) :=
  flips.flatMap fun f => gates.map fun g => (children a g).map (pullDense side f width)

/-- The pool index of corner `k` of star row `rowIdx` for carrier gate `gi`. -/
def poolIndex (G rowIdx k gi : ℕ) : ℕ := (4 * rowIdx + k) * G + gi

/-- The labels of a population of gate occurrences `gis` at star row `rowIdx`: four corner atoms per occurrence,
corner-major inside each gate (the order of `zPlusF2`'s corners). -/
def labsOf (G rowIdx : ℕ) (gis : List ℕ) : List ℕ :=
  gis.flatMap fun gi => (List.range 4).map fun k => poolIndex G rowIdx k gi

/-- A pool's shape as a pool of trivial syntactic equations (C3.3's table depends on the shape only). -/
def shapeOf {α : Type} (D : List (List α)) : List (List SynEq) := D.map (List.map fun _ => zeroSyn)

/-! ## Shape and exactness -/

theorem densePool_length {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) : (densePool a gates side width flips).length = flips.length * gates.length := by
  unfold densePool
  rw [List.length_flatMap]
  simp only [List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul]

theorem densePool_getD {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) (i gi : ℕ) (hi : i < flips.length) (hg : gi < gates.length) :
    (densePool a gates side width flips).getD (i * gates.length + gi) [] =
      (children a gates[gi]).map (pullDense side flips[i] width) := by
  induction flips generalizing i with
  | nil => simp at hi
  | cons f fs ih =>
    unfold densePool at ih ⊢
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by simpa using hg)]
      simp [List.getD_eq_getElem?_getD, hg]
    | succ i =>
      rw [List.getD_append_right _ _ _ _ (by simp; nlinarith)]
      have e : (i + 1) * gates.length + gi - (gates.map fun g => (children a g).map (pullDense side f width)).length =
          i * gates.length + gi := by simp; ring_nf; omega
      rw [e, ih i (by simpa using hi)]
      rfl

/-- **The pool is exact at every center assignment** (P3:1636-1641): the number of holding dense
children of atom `i·G + gi` is the value of gate `gi` at the pulled-back point of flip pattern `i`. -/
theorem densePool_exact {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) (aL aR : ℕ)
    (hL : ((List.ofFn fun j : Fin n => side.getD j false).filter id).length ≤ width)
    (hR : ((List.ofFn fun j : Fin n => side.getD j false).filter (fun b => !b)).length ≤ width)
    (i gi : ℕ) (hi : i < flips.length) (hg : gi < gates.length) :
    (if gates[gi].gate.eval (pullPoint side flips[i] aL aR) then (1 : ℤ) else 0) =
      (((densePool a gates side width flips).getD (i * gates.length + gi) []).map fun e =>
        if e.eval (centerInput width aL aR) then (1 : ℤ) else 0).sum := by
  rw [densePool_getD a gates side width flips i gi hi hg, List.map_map]
  exact atom_exact a gates[gi] side flips[i] width aL aR hL hR


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
