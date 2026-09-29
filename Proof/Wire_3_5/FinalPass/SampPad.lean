import Proof.Wire_3_5.FinalPass.SampPre
import Proof.Wire_3_5.Primitive.SeedFix.C4PadA

/-! # The degenerate call's padded batch (mode-generic): the same objective, and its shape

At a call with no rows (`R = 0`: no carriers, no circuits) the child expression is the coefficient terms alone; the padded batch (`C4Pad.padBatch`: one constant row `1` per entry, `R′ = 1`) gives every term eight constant factors of
value `1`, so the printed objective, hence the greedy decisions and the seed of `samp:seed` (P3:3034-3038), are
unchanged, and the child request has exactly `m = 8` factors per term.
* `constRow_eval`, `entryRows_pad`, `termsAt_pad_eval`, **`sampTerms_pad_eval`** (the objective is unchanged);
* **`padFacts`** (`BatchFacts (padBatch N nT) 1 (fun _ => 1) 0 A 1`: one constant factor per row, degree `0`).
Paper quantities of the main types: the child's printed objective at a degenerate call, and its shape. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SampShape
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.SeedFix NearCubicWires.WireExponent3_5.Sampler Finset

theorem constRow_eval (ρ : ℕ → Bool) : IntExpression.eval PrimT.C4Pad.constRow ρ = 1 := by
  simp [PrimT.C4Pad.constRow, IntExpression.eval, F2Poly.eval, bitZ]

theorem entryRows_pad (N nT t u v : ℕ) (ht : t < nT) (hu : u < N) (hv : v < N) :
    entryRows (PrimT.C4Pad.padBatch N nT) 1 N t u v = [PrimT.C4Pad.constRow] := by
  unfold entryRows PrimT.C4Pad.padBatch
  have hi : ((t * N + u) * N + v) * 1 + 0 < nT * N ^ 2 := by
    have h1 : t * N + u < nT * N := by nlinarith
    have h2 : (t * N + u) * N + v < nT * N * N := by nlinarith
    rw [sq, ← Nat.mul_assoc]; omega
  simp only [List.range_one, List.map_cons, List.map_nil]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_replicate]

theorem termsAt_pad_eval (P : SeedParams) (nT : ℕ) (batch : List SExpr) (plen pre : ℕ) (w : Fin 8 → Fin P.N)
    (α : Fin 8 → ℕ) (β : Fin 8 → Bool) (t : ℕ) (ht : t < nT) (ρ : ℕ → Bool) :
    IntExpression.eval (termsAt P (PrimT.C4Pad.padBatch P.N nT) 1 plen pre w α β t) ρ =
      IntExpression.eval (termsAt P batch 0 plen pre w α β t) ρ := by
  unfold termsAt
  rw [seval_sfold, seval_sfold]
  have h1 : walkRows P batch 0 w t = [] := by
    unfold walkRows entryRows; simp
  have h2 : ∀ V ∈ walkRows P (PrimT.C4Pad.padBatch P.N nT) 1 w t, IntExpression.eval V ρ = 1 := by
    intro V hV
    unfold walkRows at hV
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hV
    rw [entryRows_pad P.N nT t _ _ ht (cellOf (by norm_num) w k).1.isLt (cellOf (by norm_num) w k).2.isLt] at hk
    rw [List.mem_singleton.mp hk]
    exact constRow_eval ρ
  rw [h1]
  have h3 : ((walkRows P (PrimT.C4Pad.padBatch P.N nT) 1 w t).map fun V => IntExpression.eval V ρ).prod = 1 := by
    rw [List.map_congr_left h2]
    simp
  rw [h3]
  simp

/-- **The padded batch's child expression evaluates as the empty batch's** (the objective is unchanged). -/
theorem sampTerms_pad_eval (P : SeedParams) (nT : ℕ) (batch : List SExpr) (plen pre : ℕ) (ρ : ℕ → Bool) :
    IntExpression.eval (sampTerms P nT 1 (PrimT.C4Pad.padBatch P.N nT) plen pre) ρ =
      IntExpression.eval (sampTerms P nT 0 batch plen pre) ρ := by
  unfold sampTerms
  rw [seval_flatMap, seval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  have ht' : t < nT := List.mem_range.mp ht
  unfold sampTermsT
  rw [seval_flatMap, seval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
  rw [seval_flatMap, seval_flatMap]
  refine congrArg List.sum (List.map_congr_left fun α' _ => ?_)
  split_ifs
  · rw [seval_flatMap, seval_flatMap]
    refine congrArg List.sum (List.map_congr_left fun β' _ => ?_)
    split_ifs
    · rfl
    · exact termsAt_pad_eval P nT batch plen pre w _ _ t ht' ρ
  · rfl

/-- **The padded batch's shape**: one constant factor per row, no atoms, coefficient `1`, one term. -/
theorem padFacts (N nT A : ℕ) : BatchFacts (PrimT.C4Pad.padBatch N nT) 1 (fun _ => 1) 0 A 1 := by
  have hmem : ∀ V ∈ PrimT.C4Pad.padBatch N nT, V = PrimT.C4Pad.constRow := fun V hV =>
    List.eq_of_mem_replicate hV
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i r _ t ht
    rcases Nat.lt_or_ge (i * 1 + r) (PrimT.C4Pad.padBatch N nT).length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi] at ht
      rw [hmem _ (List.getElem_mem hi)] at ht
      simp [PrimT.C4Pad.constRow] at ht
      rw [ht]; rfl
    · rw [List.getD_eq_default _ _ hi] at ht; simp at ht
  · intro V hV t ht p hp mono hmono
    rw [hmem V hV] at ht
    simp [PrimT.C4Pad.constRow] at ht
    rw [ht] at hp
    simp at hp
    rw [hp] at hmono
    simp at hmono
    rw [hmono]
    simp
  · intro V hV t ht
    rw [hmem V hV] at ht
    simp [PrimT.C4Pad.constRow] at ht
    left; rw [ht]
  · intro V hV
    rw [hmem V hV]
    simp [PrimT.C4Pad.constRow]

end NearCubicWires.WireExponent3_5.FinalPass.SampShape

