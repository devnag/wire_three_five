import Proof.Wire_3_5.MachineModel.BlockOfRun
import Proof.Wire_3_5.MachineModel.BlockCost
import Proof.MachineModel.OrdinaryAdd
import Proof.MachineModel.OrdinaryCompare
import Proof.MachineModel.OrdinaryBoundedCounter
import Proof.Hierarchy.HierarchyBinaryMultiply

/-! # Block v3 (S5): fixed-width binary arithmetic as blocks

Paper: the final pass evaluates each sample with "an `n+log Q+O(1)`-bit accumulator" (P3:1971-1972),
and every stage of the primitive works on `O(n)`-bit binary words (P3:1353-1354: "All stored counts use
`O(n)` bits"). The machines are the Theorem 2.5 donors, each wrapped once as a `Block` with its exact
output and its cost in a named class:
* `addBlock`: `frame (binary w a)`, `frame (binary w b)` ↦ `frame (binary w (a+b))` (`Add.add_run`),
  in `2w+1` steps;
* `compareBlock`: appends `[value left ≤ value right]` to an output tape (`Compare.compare_run`), in
  `2|left|+1` steps;
* `incrementBlock`: `binary w n` ↦ `binary w (n+1)` with every head back at cell 0 and a constant
  `w`-cell workspace (`BoundedCounter.increment_run`, padded), in `2w+2` steps;
* `multiplyBlock`: `a`, `bits` ↦ `frame (binary w (a·value bits))` with every head at cell 0
  (`HierarchyMultiplyEntry.multiply_run`), at `128(w+1)(|bits|+1)`.

The paper quantity of each main type is the value its output tape carries (a sum, a comparison bit, a
successor, a product). Each block's cost is a polynomial in the word width, hence within every class
(`add_within` and the like) as soon as the width is at most `q`. The executable twins are the donors' own
reference functions (`Add.sum`, `Compare.decision`), checked by `decide` on small words. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.RepairOrdinary.RadixSemantics

/-! ## Addition -/

/-! ## Comparison -/

theorem compare_runs (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    ∃ r, runFrom Compare.machine (2 * left.length + 1)
      ⟨Compare.machine.start, ![preLeft.length, preRight.length, output.length],
        ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]⟩ = some r := by
  obtain ⟨r, hr, _⟩ := Compare.compare_run preLeft preRight left right tailLeft tailRight output hw
  exact ⟨r, hr⟩

/-- The comparison `value left ≤ value right` of two framed words at given cursors, the decision bit
appended to the output tape. -/
noncomputable def compareBlock (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) : Block 3 :=
  ofRunFrom Compare.machine (2 * left.length + 1) ![preLeft.length, preRight.length, output.length]
    ![preLeft ++ frame left ++ tailLeft, preRight ++ frame right ++ tailRight, output]
    (compare_runs preLeft preRight left right tailLeft tailRight output hw)

theorem compareBlock_out (preLeft preRight left right tailLeft tailRight output : List Bool)
    (hw : left.length = right.length) :
    (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitA 2 =
        output ++ [decide (value left ≤ value right)] ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitA 0 =
        preLeft ++ frame left ++ tailLeft ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitA 1 =
        preRight ++ frame right ++ tailRight ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).exitH =
        ![preLeft.length + 2 * left.length, preRight.length + 2 * right.length, output.length + 1] ∧
      (compareBlock preLeft preRight left right tailLeft tailRight output hw).cost = 2 * left.length + 1 := by
  obtain ⟨r, hr, hf, _⟩ := Compare.compare_run preLeft preRight left right tailLeft tailRight output hw
  have eA := ofRunFrom_exitA _ _ _ _ (compare_runs preLeft preRight left right tailLeft tailRight output hw) r hr
  have eH := ofRunFrom_exitH _ _ _ _ (compare_runs preLeft preRight left right tailLeft tailRight output hw) r hr
  rw [hf] at eA eH
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · rw [compareBlock, eA]; rfl
  · rw [compareBlock, eA]; rfl
  · rw [compareBlock, eA]; rfl
  · rw [compareBlock, eH]
    funext i
    fin_cases i <;> simp [Compare.config]

/-! ## Increment with a constant workspace -/

theorem increment_runs (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    ∃ r, run (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
      (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
        (fun _ : Fin 1 => binary width n) (fun _ : Fin 1 => List.replicate width false)) = some r := by
  obtain ⟨_, r, _, hr, _⟩ := BoundedCounter.increment_run width n width hn (le_refl _)
  exact ⟨r, hr⟩

/-- The raw increment block, whose workspace length after the run is the donor's (`≤ w`). -/
noncomputable def incrementRaw (width n : ℕ) (hn : n + 1 < 2 ^ width) : Block 2 :=
  ofRun (Rewind.machine BinaryIncrement.machine) (2 * width + 2)
    (Fin.addCases (motive := fun _ : Fin (1 + 1) => List Bool)
      (fun _ : Fin 1 => binary width n) (fun _ : Fin 1 => List.replicate width false))
    (increment_runs width n hn)

/-- The workspace padded to `w` cells, so the increment's exit bank is a function of `n`. -/
def incrementCaps (width : ℕ) : Fin 2 → ℕ := ![0, width]

theorem increment_exit (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    (padded (incrementRaw width n hn) (incrementCaps width)).exitA =
        ![binary width (n + 1), List.replicate width false] ∧
      (padded (incrementRaw width n hn) (incrementCaps width)).exitH = (fun _ => 0) ∧
      (padded (incrementRaw width n hn) (incrementCaps width)).entryA =
        ![binary width n, List.replicate width false] ∧
      (padded (incrementRaw width n hn) (incrementCaps width)).entryH = (fun _ => 0) := by
  obtain ⟨next, r, hnext, hr, h0, h1, hh, _⟩ := BoundedCounter.increment_run width n width hn (le_refl _)
  have eA := ofRun_exitA _ _ _ (increment_runs width n hn) r hr
  have eH := ofRun_exitH _ _ _ (increment_runs width n hn) r hr
  refine ⟨?_, ?_, ?_, rfl⟩
  · change (fun i => ZeroPadding.pad (incrementCaps width i) ((incrementRaw width n hn).exitA i)) = _
    rw [incrementRaw, eA]
    funext i
    fin_cases i
    · simp [incrementCaps, h0]
    · simp [incrementCaps, h1, ZeroPadding.pad]
      omega
  · change (incrementRaw width n hn).exitH = _
    rw [incrementRaw, eH]
    funext i
    exact hh i
  · change (fun i => ZeroPadding.pad (incrementCaps width i) ((incrementRaw width n hn).entryA i)) = _
    funext i
    fin_cases i
    · simp [incrementCaps, incrementRaw]
      rfl
    · change ZeroPadding.pad width (List.replicate width false) = List.replicate width false
      simp [ZeroPadding.pad]

/-- **The counter increment** `binary w n ↦ binary w (n+1)`, every head at cell 0 before and after, and
a constant `w`-cell workspace, in `2w+2` steps. -/
noncomputable def incrementBlock (width n : ℕ) (hn : n + 1 < 2 ^ width) : Block 2 :=
  congrExit (padded (incrementRaw width n hn) (incrementCaps width))
    (increment_exit width n hn).2.1 (increment_exit width n hn).1

theorem incrementBlock_spec (width n : ℕ) (hn : n + 1 < 2 ^ width) :
    (incrementBlock width n hn).entryA = ![binary width n, List.replicate width false] ∧
      (incrementBlock width n hn).entryH = (fun _ => 0) ∧
      (incrementBlock width n hn).exitA = ![binary width (n + 1), List.replicate width false] ∧
      (incrementBlock width n hn).exitH = (fun _ => 0) ∧
      (incrementBlock width n hn).cost = 2 * width + 2 :=
  ⟨(increment_exit width n hn).2.2.1, (increment_exit width n hn).2.2.2, rfl, rfl, rfl⟩

/-! ## Multiplication -/

/-! ## Executable twins on small words -/



end NearCubicWires.WireExponent3_5.Block
