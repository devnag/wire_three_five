import Proof.Wire_3_5.Compiler.MachinePoolTableLoop

/-! # C3a, the pool builder: the machine's words are the contract's words (P3:1636-1664)

Paper: "For a common pool over all `2^k` rows and polynomially many original atoms, it gives `P_ex ≤ 2^k n^{O(1)}`"
(P3:1661-1664). The flips loop writes, flip-major, every decomposed child's dense records; the table loop writes the
atom streams with consecutive labels. This module identifies both with the reference: the pool stream's records are
`poolRecs` (the dense children of `densePool`, word (1)), and the table is `childTable Q' (shapeOf densePool)`
(word (2)).

The paper quantities of the main theorems are the two output words: **`poolRecs_eq`**, **`table_eq`**. Main
declarations: `shape_lengths`, `pool_flatten_length`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (a : DecompositionAlgorithm)

/-- **Word (1)**: the flips loop's records are the reference pool's dense records. -/
theorem poolRecs_eq (h : ℕ) {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) :
    poolRecs a h gates side width flips = flips.flatMap (fun f => (GS a gates).flatMap (denseRecs h side f width)) := by
  unfold poolRecs poolChildren GS
  rw [List.flatMap_assoc]
  congr 1
  funext f
  rw [List.flatMap_assoc, List.flatMap_assoc]
  congr 1
  funext g
  rw [List.flatMap_map]

theorem flatMap_const_eq {β γ : Type} (l : List β) (L : List γ) :
    l.flatMap (fun _ => L) = (l.map fun _ => L).flatten := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

/-- The atoms' child counts, flip-major. -/
theorem shape_lengths {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) :
    (shapeOf (densePool a gates side width flips)).map List.length = (flips.map fun _ => counts a gates).flatten := by
  unfold shapeOf densePool counts
  rw [← flatMap_const_eq]
  simp [List.map_flatMap, Function.comp_def]

/-- The machine's table fold as one consecutive-label table. -/
theorem gfold_flips (Q W : ℕ) (cs : List ℕ) : ∀ (flips : List (List Bool)) (st : GSt),
    (flips.foldl (fun st _ => cs.foldl (gnext Q W) st) st).tbl =
      st.tbl ++ (tableOf (entC Q W) st.c ((flips.map fun _ => cs).flatten)).flatMap atomStream
  | [], st => by simp [tableOf]
  | f :: fs, st => by
    rw [List.foldl_cons, gfold_flips Q W cs fs, gfold_tbl, gfold_c, List.map_cons, List.flatten_cons, tableOf_append,
      List.flatMap_append, List.append_assoc]

/-- **Word (2)**: the table loop writes C3.3's children table of the pool. -/
theorem table_eq (Q : ℕ) {n : ℕ} (gates : List (SupportedNormalizedGate n)) (side : List Bool) (width : ℕ)
    (flips : List (List Bool)) (tbl0 : List Bool) (x0 : ℕ) :
    ((flips.foldl (fun st _ => (counts a gates).foldl (gnext Q (flips.length * (counts a gates).sum)) st)
        ⟨0, x0, tbl0⟩).tbl) =
      tbl0 ++ (childTable Q (shapeOf (densePool a gates side width flips))).flatMap atomStream := by
  rw [gfold_flips, childTable_eq, shape_lengths]
  congr 3
  · funext c
    have hw : (shapeOf (densePool a gates side width flips)).flatten.length = flips.length * (counts a gates).sum := by
      rw [List.length_flatten, shape_lengths, List.sum_flatten, List.map_map]
      simp [Function.comp_def, List.sum_replicate, List.map_const']
    rw [hw]
    rfl


end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
