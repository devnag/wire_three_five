import Proof.Wire_3_5.Compiler.MachineStream
import Proof.Wire_3_5.Compiler.MachineCancelAll

/-! # C3.4, cancellation: the machine cancels the reference's masks (P3:1924-1929)

Paper: "Substitute the disjoint exact children in each polynomial over `𝔽₂`. [...] Reducing squares and cancelling
repeated monomials leaves at most `Σ_j C(P_ex, j) ≤ (P_ex+1)^d` monomials" (P3:1924-1929).

On the tape a mask `U` of labels below `W` (a monomial over the exact children) is the register word
`maskWord W U = true :: binary W U`: a marker bit, then bit `c` for label `c`. The marker makes every word nonempty,
so a mask stream ends at its `false` terminator even when `W = 0`.

The paper quantity of the main theorem is the cancelled substitution `oddMasksM pool p`, which lists the same masks as
the sorted cancellation `oddMasks pool p` (`oddMasksM_perm`). **`cancel_run`** shows that the insert-all machine
(`Cancel.insertAllM`) leaves exactly `(oddMasksM pool p).map (maskWord W)` on tape 0 when it starts from the empty list
and the stream of the masks of `p`'s expansion. The bridge is `foldl_symInsert_map`: symmetric-difference insertion
commutes with the injective word map on masks below `2^W`.

Main declarations: `maskWord` (`maskWord_inj`), `symInsert_map`, `foldl_symInsert_map`, `monoMasks_lt`,
`oddMasksM_words`, **`cancel_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Cancel
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

theorem mem_symInsert (G : List ℕ) (x u : ℕ) (h : u ∈ symInsert G x) : u ∈ G ∨ u = x := by
  unfold symInsert at h
  split_ifs at h
  · exact Or.inl (List.mem_filter.mp h).1
  · simpa using h

/-- Every mask of a monomial is below `2^{P_ex}`. -/
theorem monoMasks_lt (pool : List (List SynEq)) : ∀ (mono : List ℕ), ∀ u ∈ monoMasks pool mono,
    u < 2 ^ pool.flatten.length
  | [], u, hu => by
    simp only [monoMasks, List.mem_singleton] at hu
    subst hu
    exact Nat.two_pow_pos _
  | a :: as, u, hu => by
    simp only [monoMasks, List.mem_flatMap, List.mem_map] at hu
    obtain ⟨c, hc, u', hu', rfl⟩ := hu
    exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (labelsOf_lt pool a c hc))
      (monoMasks_lt pool as u' hu')

/-! ## Twin -/


end NearCubicWires.WireExponent3_5.CompilerMachine.Bridge
