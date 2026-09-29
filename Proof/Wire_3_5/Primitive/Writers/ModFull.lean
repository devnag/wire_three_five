import Proof.Wire_3_5.Primitive.Writers.ShellLayout

/-! # SB, part 4: the field modulus with every tape's length bounded

`Modulus.modulus_step` (PA library (b), verified) leaves `frame (binary ℓ (GF.firstPrimitive ℓ))` on tape `12` of its
seventeen tapes. A pool writer (`CoreWordsM`) must erase the other tapes afterwards, so it needs their lengths:
the search's bank (`GF2.srBank`: ℓ-bit frames, single flags, `0^{2ℓ+2}`) is at most `2ℓ + 2`, the unary degree `ℓ`,
and the kernel's rewind log at most the bank stage's `4ℓ + 6` steps (`Shell.Step.len`):

* **`modulus_full`**: `modulus_step` with `∀ i, (tout i).length ≤ 4ℓ + 6`.

Paper quantity of the main type: the modulus word `frame (binary ℓ (GF.firstPrimitive ℓ))` (P3:2939-2941, the
filter's field modulus, S4's word `5`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Modulus
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5

theorem modulus_full (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∃ tout : Fin 17 → List Bool,
    Step modM (modCost ℓ) (fun _ => 0) (fun i => if i.val = 0 then List.replicate ℓ true else []) (fun _ => 0) tout ∧
      tout 0 = List.replicate ℓ true ∧ tout 12 = frame (binary ℓ (GF.firstPrimitive ℓ)) ∧
      ∀ i, (tout i).length ≤ 4 * ℓ + 6 := by
  set A0 : Fin 17 → List Bool := fun i => if i.val = 0 then List.replicate ℓ true else [] with hA0
  -- the bank
  obtain ⟨tout1, h1l, ht1⟩ := bank_step ℓ hℓ
  have h1 := dock0 h1l s1 s1_inj A0 (by
    intro k
    fin_cases k <;> rfl)
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = install s1 A0 tout1 := ⟨_, rfl⟩
  rw [← hA1] at h1
  have hA1b : ∀ i : Fin 8, A1 (s1 (i.castAdd 1)) = bankFinal ℓ i := by
    intro i; rw [hA1, inst_at s1 s1_inj _ _ (i.castAdd 1) _ rfl, ht1 i]
  have hA1o : ∀ i : Fin 17, (∀ k, s1 k ≠ i) → A1 i = [] := by
    intro i hi
    rw [hA1, inst_off s1 _ _ i hi]
    have h0 : i ≠ 0 := fun h => hi 0 (by rw [h]; rfl)
    have hv : i.val ≠ 0 := fun h => h0 (Fin.ext h)
    simp only [hA0]
    exact if_neg hv
  -- the flags
  have h2 := dock0 cells_step s2 s2_inj A1 (by
    intro k
    exact hA1o _ (by intro k'; fin_cases k <;> fin_cases k' <;> decide))
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install s2 A1 (fun _ => [false]) := ⟨_, rfl⟩
  rw [← hA2] at h2
  have hA2f : ∀ k : Fin 8, A2 (s2 k) = [false] := by
    intro k; rw [hA2, inst_at s2 s2_inj _ _ k _ rfl]
  have hA2o : ∀ i : Fin 17, (∀ k, s2 k ≠ i) → A2 i = A1 i := by
    intro i hi; rw [hA2, inst_off s2 _ _ i hi]
  -- the search
  have h3l := GF2.search_run ℓ (2 * ℓ + 2) junk0 0 0 false false false hℓ le_rfl
  have hin : ∀ j : Fin 15, A2 (sb j) = GF2.srIn ℓ (2 * ℓ + 2) junk0 0 0 false false false j := by
    intro j
    fin_cases j
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 1
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 2
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 3
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 5
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 6
    · exact hA2f 0
    · exact hA2f 1
    · exact hA2f 2
    · exact hA2f 3
    · exact hA2f 4
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 7
    · rw [hA2o _ (by intro k; fin_cases k <;> decide)]
      exact hA1b 4
    · exact hA2f 5
    · exact hA2f 6
    · exact hA2f 7
  have h3 := dock0 h3l sb sb_inj A2 hin
  have h := (h1.seq h2).seq h3
  have l16 : (tout1 8).length ≤ 4 * ℓ + 6 := by
    have := Shell.Step.len h1l 8 0 (by simp) (by simp [Fin.addCases])
    omega
  have e0 : install sb A2 (GF2.srBank ℓ (2 * ℓ + 2) junk0 false (2 ^ ℓ)) 0 = List.replicate ℓ true := by
    rw [inst_off sb _ _ 0 (by intro k h; have := congrArg Fin.val h; simp [sb] at this),
      hA2o _ (by intro k; fin_cases k <;> decide)]
    exact hA1b 0
  refine ⟨_, h, e0, ?_, ?_⟩
  · rw [inst_at sb sb_inj _ _ 11 12 rfl]
    exact GF2.srBank_out ℓ (2 * ℓ + 2) junk0 false
  · intro i
    by_cases hi : ∃ j, sb j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [install_slot _ sb_inj]
      fin_cases j <;> simp [GF2.srBank] <;> omega
    · simp only [not_exists] at hi
      have hi0 : i.val = 0 ∨ i.val = 16 := by
        by_contra hc
        have hlt := i.isLt
        exact hi ⟨i.val - 1, by omega⟩ (Fin.ext (by simp only [sb]; omega))
      rcases hi0 with h0 | h16
      · rw [show i = 0 from Fin.ext h0, e0]
        simp only [List.length_replicate]
        omega
      · rw [show i = 16 from Fin.ext h16, inst_off sb _ _ 16 (by rw [← show i = 16 from Fin.ext h16]; exact hi),
          hA2o _ (by intro k; fin_cases k <;> decide), hA1, inst_at s1 s1_inj _ _ 8 16 rfl]
        exact l16

end NearCubicWires.WireExponent3_5.PrimAsm.Modulus
