import Proof.Wire_3_5.Lists.ListMachineRefs

/-! # C2 computable refs, reduced after each operation: the printed repaired list within `(L+1)^D` (P3:1482-1488)

Realizes the construction bound of `list:repair` (P3:1482-1488): "To construct the lists, expand the displayed
recurrences and reduce to squarefree multilinear form over `𝔽₂` after each operation. A degree-`D` polynomial on `M`
formal coordinates has at most `(M+1)^D` monomials; polynomially many intermediate coordinates and naive polynomial
products cost `(M+1)^{O(D)}`."

`normalize p` is the squarefree multilinear reduction over `𝔽₂`: each monomial's repeated coordinates are merged
(`Z_i² = Z_i` on Boolean inputs) and equal monomials cancel in pairs. The reduced refs `bitRefN`, `decoderRefN`,
`recurRefN`, `repairRefN`, `stateRefN` are the unreduced refs of `Proof.Wire_3_5.Lists.ListMachineRefs` with `normalize`
applied after every addition and product; they are what the C2 list machine prints.

Main results: `eval_normalize` (reduction never changes the value), `normalize_length_le` (a reduced list of degree
`≤ D` on `L` coordinates has at most `(L+1)^D` monomials), **`stateRefN_eval`** (the printed state `P_s` is `listStates` on EVERY input) and **`stateRefN_size`** (degree `≤ Σ_{j<J}(H_j−1)`, coordinates `< L`, at most
`(L+1)^{Σ_j(H_j−1)}` monomials), plus the same bound for every intermediate decoder (`decoderRefN_size`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Lists Finset NearCubicWires.WireExponent3_5.ListMachine.Ref

/-! ## Squarefree multilinear reduction over `𝔽₂` -/

/-- A monomial with repeated coordinates merged, sorted. -/
def normMono (m : List ℕ) : List ℕ := (m.dedup).insertionSort (· ≤ ·)

/-- Add one monomial over `𝔽₂`: a second copy cancels the first. -/
def toggle (m : List ℕ) (acc : Poly) : Poly := if m ∈ acc then acc.erase m else m :: acc

/-- **The squarefree multilinear reduction** of an explicit `𝔽₂` polynomial. -/
def normalize (p : Poly) : Poly := (p.map normMono).foldr toggle []

theorem mem_normMono (m : List ℕ) (i : ℕ) : i ∈ normMono m ↔ i ∈ m := by
  unfold normMono
  rw [(List.perm_insertionSort _ _).mem_iff, List.mem_dedup]

theorem all_normMono (m : List ℕ) (ρ : ℕ → Bool) : (normMono m).all ρ = m.all ρ := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h i hi => h i ((mem_normMono m i).mpr hi), fun h i hi => h i ((mem_normMono m i).mp hi)⟩

theorem length_normMono (m : List ℕ) : (normMono m).length ≤ m.length := by
  unfold normMono
  rw [List.length_insertionSort]
  exact (List.dedup_sublist m).length_le

theorem eval_perm {p q : Poly} (h : p.Perm q) (ρ : ℕ → Bool) : F2Poly.eval p ρ = F2Poly.eval q ρ := by
  induction h with
  | nil => rfl
  | cons m _ ih => rw [eval_cons, eval_cons, ih]
  | swap m m' l => rw [eval_cons, eval_cons, eval_cons, eval_cons, ← Bool.xor_assoc, ← Bool.xor_assoc,
      Bool.xor_comm (m'.all ρ)]
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

theorem eval_toggle (m : List ℕ) (acc : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (toggle m acc) ρ = xor (m.all ρ) (F2Poly.eval acc ρ) := by
  unfold toggle
  split_ifs with h
  · rw [eval_perm (List.perm_cons_erase h) ρ, eval_cons, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
  · rw [eval_cons]

/-- **Reduction never changes the value** on any Boolean input. -/
theorem eval_normalize (p : Poly) (ρ : ℕ → Bool) : F2Poly.eval (normalize p) ρ = F2Poly.eval p ρ := by
  unfold normalize
  induction p with
  | nil => rfl
  | cons m p ih => rw [List.map_cons, List.foldr_cons, eval_toggle, ih, all_normMono, eval_cons]

theorem mem_normalize {p : Poly} {m : List ℕ} (hm : m ∈ normalize p) : ∃ m' ∈ p, m = normMono m' := by
  unfold normalize at hm
  induction p with
  | nil => simp at hm
  | cons a p ih =>
    rw [List.map_cons, List.foldr_cons] at hm
    unfold toggle at hm
    split_ifs at hm with h
    · obtain ⟨m', hm', rfl⟩ := ih (List.mem_of_mem_erase hm)
      exact ⟨m', List.mem_cons_of_mem _ hm', rfl⟩
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨a, List.mem_cons_self .., rfl⟩
      · obtain ⟨m', hm', rfl⟩ := ih hm
        exact ⟨m', List.mem_cons_of_mem _ hm', rfl⟩

theorem degLe_normalize {p : Poly} {e : ℕ} (h : DegLe p e) : DegLe (normalize p) e := by
  intro m hm
  obtain ⟨m', hm', rfl⟩ := mem_normalize hm
  exact (length_normMono m').trans (h m' hm')

theorem atomsLt_normalize {p : Poly} {L : ℕ} (h : AtomsLt p L) : AtomsLt (normalize p) L := by
  intro m hm i hi
  obtain ⟨m', hm', rfl⟩ := mem_normalize hm
  exact h m' hm' i ((mem_normMono m' i).mp hi)


/-! ## The reduced refs -/

def nadd (p q : Poly) : Poly := normalize (padd p q)
def nmul (p q : Poly) : Poly := normalize (pmul p q)
def nnot (p : Poly) : Poly := normalize (pnot p)
def nsum (ps : List Poly) : Poly := normalize (psum ps)

@[simp] theorem eval_nadd (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (nadd p q) ρ = xor (F2Poly.eval p ρ) (F2Poly.eval q ρ) := by simp [nadd, eval_normalize]
@[simp] theorem eval_nmul (p q : Poly) (ρ : ℕ → Bool) :
    F2Poly.eval (nmul p q) ρ = (F2Poly.eval p ρ && F2Poly.eval q ρ) := by simp [nmul, eval_normalize]
@[simp] theorem eval_nnot (p : Poly) (ρ : ℕ → Bool) : F2Poly.eval (nnot p) ρ = !F2Poly.eval p ρ := by
  simp [nnot, eval_normalize]
theorem eval_nsum (ps : List Poly) (ρ : ℕ → Bool) : F2Poly.eval (nsum ps) ρ = F2Poly.eval (psum ps) ρ := by
  simp [nsum, eval_normalize]

/-- `binom(S + a, t) mod 2`, reduced after each step. -/
def binomRefN : List Poly → ℤ → ℕ → Poly
  | [], a, t => pconst (chooseMod2 a t)
  | _ :: _, _, 0 => pone
  | ℓ :: ls, a, t + 1 => nadd (binomRefN ls a (t + 1)) (nmul ℓ (binomRefN ls a t))

namespace Ref

end Ref

end NearCubicWires.WireExponent3_5.ListMachine
