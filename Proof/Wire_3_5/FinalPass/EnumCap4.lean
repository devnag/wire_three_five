import Proof.Wire_3_5.FinalPass.EnumCap3
import Proof.Wire_3_5.Primitive.SeedFix.C4Child

/-! # The enumeration's side conditions at a call, generic in the batch, part 4: the child expression's word

P3:3011-3016: the enumeration's output after the `n_T·2^w` counter values is the printed objective (`outAt_sampTerms`),
and every counter value emits at most `b^{8R}` terms of words at most `T₀ + 8R·b` (the invariant `Inv`, from the
group's fold of `≤ 8R` rows of words `≤ b`). So the child expression `chV` (the objective's terms at a child prefix)
has its word below the group size bound `qG`. Mode-generic.

* `outAt_inv`, **`chV_word_le`**.

Paper quantity of the main type: the child expression's encoding length. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)
open NearCubicWires.WireExponent3_5.PrimT.C4Grp (Inv inv_mono inv_sfold inv_flatMap inv_expr cf_inv chunk_rowOk
  chunk_entry_len RowOk T0 bsz bsz_pos)
open JBody SplitT JEnum

/-- **The output invariant** at every counter value `j` (the group's fold of `≤ 8R` rows). -/
theorem outAt_inv (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (TWd Cap : ℕ) (p' : List Bool)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (j : ℕ) :
    Inv (outAt (PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') j)
      (j * bsz batch ^ (8 * R)) (T0 P + 8 * R * bsz batch) := by
  set X := PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p' with hX
  set b := bsz batch with hbd
  have hb := bsz_pos batch
  rw [← hbd] at hb
  have hrow : ∀ e, ∀ V ∈ (JLink.chunk (2 ^ P.kh) nT R batch).getD e [], RowOk b V :=
    chunk_rowOk _ _ _ batch hpm
  have hmono : ∀ {A : SExpr} {m : ℕ}, m ≤ 8 * R → Inv A (1 * b ^ m) (T0 P + m * b) →
      Inv A (b ^ (8 * R)) (T0 P + 8 * R * b) := by
    intro A m hm h
    refine inv_mono h ?_ ?_
    · rw [Nat.one_mul]; exact Nat.pow_le_pow_right hb hm
    · exact Nat.add_le_add_left (Nat.mul_le_mul_right b hm) _
  have := inv_flatMap (fun i => (at_ X (tOf X i)).emitJ i) (b ^ (8 * R)) (T0 P + 8 * R * b) (List.range j)
    (fun i _ => by
      show Inv ((at_ X (tOf X i)).emitJ i) _ _
      unfold JCtx.emitJ
      split_ifs
      · have hrs : ((at_ X (tOf X i)).rowsJ i).length ≤ 8 * R := by
          unfold JCtx.rowsJ
          rw [List.length_flatMap]
          have := List.sum_le_card_nsmul (((at_ X (tOf X i)).esJ i).map fun e =>
            ((at_ X (tOf X i)).ents.getD e []).length) R (fun y hy => by
              obtain ⟨e, -, rfl⟩ := List.mem_map.mp hy
              exact chunk_entry_len _ _ _ _ _)
          simp only [List.length_map, esJ_length, smul_eq_mul] at this
          omega
        have h1 := inv_sfold b ((at_ X (tOf X i)).rowsJ i) ((at_ X (tOf X i)).cfJ i) 1 (T0 P) (cf_inv _ i)
          (fun V hV => by
            unfold JCtx.rowsJ at hV
            obtain ⟨e, -, hV⟩ := List.mem_flatMap.mp hV
            exact hrow e V hV)
        exact hmono hrs h1
      · exact ⟨by simp, by simp⟩)
  rw [List.length_range] at this
  exact this

/-- **The child expression's word is below `qG`** at every child prefix. -/
theorem chV_word_le (P : SeedParams) (nT R : ℕ) (batch : List SExpr) (TWd Cap : ℕ) (p' : List Bool)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (hQ : 1 ≤ P.Q) :
    (exprWord (PrimT.C4Child.chV P nT R batch p')).length ≤ PrimT.C4Grp.qG P nT R (bsz batch) TWd p'.length := by
  have e := JLink.outAt_sampTerms (PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p') nT R batch
    (JLink.chunk_ok _ _ _ _) hQ
  have hi := inv_expr (outAt_inv P nT R batch TWd Cap p' hpm
    (nT * 2 ^ (PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p').w))
  have e2 : PrimT.C4Child.chV P nT R batch p' =
      outAt (PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p')
        (nT * 2 ^ (PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p').w) := e.symm
  rw [e2]
  refine hi.trans ?_
  have hw : (PrimT.C4Enum.jX P (JLink.chunk (2 ^ P.kh) nT R batch) TWd Cap p').w = 8 + 8 * P.ell + 8 * P.kh := rfl
  rw [hw]
  unfold PrimT.C4Grp.qG PrimT.C4Grp.Fs
  obtain ⟨W, hW⟩ : ∃ W, W = nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = bsz batch ^ (8 * R) * (T0 P + 8 * R * bsz batch + 1) := ⟨_, rfl⟩
  have e3 : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) * bsz batch ^ (8 * R) * (T0 P + 8 * R * bsz batch + 1) = W * C := by
    rw [hW, hC]; ring
  have e4 : (nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) + 1) * (bsz batch ^ (8 * R) * (T0 P + 8 * R * bsz batch + 1) + 1) =
      W * C + W + C + 1 := by rw [hW, hC]; ring
  rw [e3, e4]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
