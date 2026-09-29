import Proof.Wire_3_5.Compiler.MachineCancelBridge
import Proof.Wire_3_5.Compiler.MachineUnionsAll

/-! # C3.4 → C3.5: the cancelled masks in the unions' entry format (P3:1924-1930)

Paper: "Reducing squares and cancelling repeated monomials [...] Apply Lemma alg:binlift at precision `Q'` to each
polynomial" (P3:1926-1930). The cancellation stage hands its monomials to the lift. On the tape the lift reads monomials
as union entries of size `0`, `ew Q' W (0, U)` (a zero size field, then the mask word); the cancellation machine works
for words of any fixed width, so it runs directly on these entries.

The paper quantity of the main theorem is the cancelled substitution in the lift's format:
**`cancel_run_entry`** shows that the insert-all machine leaves `(oddMasksM pool p).map (fun U => ew Q' W (0, U))`,
exactly the monomial stream `unions_run` consumes. The bridge is `foldl_symInsert_map_of`: insertion by symmetric
difference commutes with any word map that is injective on masks below `2^W`.

Main declarations: `symInsert_map_of`, `foldl_symInsert_map_of`, `entry0_inj`, `oddMasksM_entries`,
**`cancel_run_entry`**; the twin `unions_twin`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch

/-- Insertion commutes with any word map injective on masks below `2^W`. -/
theorem symInsert_map_of (W : ℕ) (f : ℕ → List Bool) (hf : ∀ u v, u < 2 ^ W → v < 2 ^ W → f u = f v → u = v)
    (G : List ℕ) (x : ℕ) (hG : ∀ u ∈ G, u < 2 ^ W) (hx : x < 2 ^ W) :
    (symInsert G x).map f = symInsertW (G.map f) (f x) := by
  have hmem : f x ∈ G.map f ↔ x ∈ G := by
    constructor
    · intro h
      obtain ⟨u, hu, he⟩ := List.mem_map.mp h
      rwa [← hf u x (hG u hu) hx he]
    · intro h
      exact List.mem_map_of_mem h
  unfold symInsert symInsertW
  by_cases h : x ∈ G
  · rw [if_pos h, if_pos (hmem.mpr h), List.filter_map]
    congr 1
    apply List.filter_congr
    intro u hu
    have hiff : (f u = f x) ↔ (u = x) := ⟨hf u x (hG u hu) hx, fun h => h ▸ rfl⟩
    simp only [Function.comp, ne_eq, hiff]
  · rw [if_neg h, if_neg (fun h' => h (hmem.mp h'))]
    simp

theorem foldl_symInsert_map_of (W : ℕ) (f : ℕ → List Bool) (hf : ∀ u v, u < 2 ^ W → v < 2 ^ W → f u = f v → u = v) :
    ∀ (M G : List ℕ), (∀ u ∈ G, u < 2 ^ W) → (∀ u ∈ M, u < 2 ^ W) →
      (M.foldl symInsert G).map f = (M.map f).foldl symInsertW (G.map f)
  | [], _, _, _ => rfl
  | x :: M, G, hG, hM => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ← symInsert_map_of W f hf G x hG (hM x List.mem_cons_self)]
    refine foldl_symInsert_map_of W f hf M (symInsert G x) ?_ (fun u hu => hM u (List.mem_cons_of_mem x hu))
    intro u hu
    rcases mem_symInsert G x u hu with h | h
    · exact hG u h
    · rw [h]; exact hM x List.mem_cons_self

/-- The size-`0` entries are injective on masks below `2^W`. -/
theorem entry0_inj (Q W : ℕ) : ∀ u v, u < 2 ^ W → v < 2 ^ W → ew Q W (0, u) = ew Q W (0, v) → u = v :=
  fun u v hu hv h => (entryWord_inj Q W 0 0 u v (by omega) (by omega) hu hv h).2

/-- **The streaming cancellation in the lift's entry format.** -/
theorem oddMasksM_entries (pool : List (List SynEq)) (p : F2Poly ℕ) (Q : ℕ) :
    (oddMasksM pool p).map (fun U => ew Q pool.flatten.length (0, U)) =
      ((p.flatMap (monoMasks pool)).map (fun U => ew Q pool.flatten.length (0, U))).foldl symInsertW [] := by
  unfold oddMasksM
  rw [foldl_symInsert_map_of _ _ (entry0_inj Q pool.flatten.length) _ [] (by simp)]
  · rfl
  · intro u hu
    obtain ⟨mono, _, hu⟩ := List.mem_flatMap.mp hu
    exact monoMasks_lt pool mono u hu

/-! ## Twin -/


end NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
