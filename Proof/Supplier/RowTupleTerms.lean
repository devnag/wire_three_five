import Proof.Supplier.RowTupleCandidate

/-! The actual binary enumeration order is a permutation of A.12's list
expansion. Equal monomial values and equal resulting terms stay repeated. -/
namespace NearCubicWires.RepairOrdinary.RowTupleTerms
open RowTupleSubsets RowTupleDigits SupplierPrinter SupplierPipeline SupplierEstimator ThresholdCompiler
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem map_sublistsLen {α β : Type} (f : α→β) (xs : List α) (k : ℕ) :
    (xs.sublistsLen k).map (List.map f)=(xs.map f).sublistsLen k := by
  induction xs generalizing k with
  | nil => cases k <;> simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simp [List.sublistsLen_succ_cons,List.map_map,Function.comp_def,←ih]

def fetch {α : Type} (ms : List (List α)) (i : ℕ) : List α := (ms[i]?).getD []
def selectedMonomials {α : Type} (ms : List (List α)) (ds : List ℕ) := ds.map (fetch ms)

theorem fetch_range {α : Type} (ms : List (List α)) : (List.range ms.length).map (fetch ms)=ms := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [fetch,hj]

theorem monomials_perm {α : Type} (ms : List (List α)) (k : ℕ) :
    ((selected (digitWidth ms.length) ms.length k).map (selectedMonomials ms)).Perm (ms.sublistsLen k) := by
  have h := (chosen_perm ms.length k).map (selectedMonomials ms)
  change ((selected (digitWidth ms.length) ms.length k).map (List.map (fetch ms))).Perm
    (((List.range ms.length).sublistsLen k).map (List.map (fetch ms))) at h
  rw [map_sublistsLen,fetch_range] at h
  exact h

def terms {α : Type} (Q : ℕ) (ms : List (List α)) : List (ℤ×List α) :=
  (List.range (min Q ms.length)).flatMap fun j=>
    (selected (digitWidth ms.length) ms.length (j+1)).map fun ds=>
      ((-2 : ℤ)^j,(selectedMonomials ms ds).flatten)

theorem terms_perm {α : Type} (Q : ℕ) (ms : List (List α)) :
    (terms Q ms).Perm (RowBinLift.terms Q ms) := by
  apply List.Perm.flatMap_left
  intro j _
  have h := (monomials_perm ms (j+1)).map (fun selected=>((-2 : ℤ)^j,selected.flatten))
  simpa only [List.map_map,Function.comp_def] using h

end NearCubicWires.RepairOrdinary.RowTupleTerms
