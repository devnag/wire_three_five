import Proof.Wire_3_5.Primitive.SeedFix.C4HfK

/-! # The HASH child family, part 12: the child's steps within C4H's cost

C4H's `hCoreCost` (the contract `HashEAt` bounds by `Kch`) covers the HASH child's steps: the prep's copies are
at most `10` steps per bit of the kept words (which are no longer than the child's bank's words), the prefix word and the
free-bit ruler at most `18·|p| + 19·c_C`, the terminator `10·|exprWord|` (**`coreSteps_le`**).

Paper quantity of the main type: the HASH child's steps. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.HbM NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairRepresentation

theorem copiesCost_sub (w : Fin 94 → List Bool) : ∀ {l1 l2 : List (Fin 94)}, l1.Sublist l2 →
    copiesCost w l1 ≤ copiesCost w l2
  | _, _, .slnil => le_rfl
  | _, _, .cons a h => by have := copiesCost_sub w h; simp only [copiesCost]; omega
  | _, _, .cons_cons a h => by have := copiesCost_sub w h; simp only [copiesCost]; omega

theorem copiesCost_eq (w : Fin 94 → List Bool) : ∀ l : List (Fin 94),
    copiesCost w l = 10 * (l.map fun j => (w j).length).sum + 2 * l.length
  | [] => rfl
  | j :: l => by rw [copiesCost, copiesCost_eq w l]; simp only [List.map_cons, List.sum_cons, List.length_cons]; ring

theorem flatten_len (f : Fin 94 → List Bool) :
    (List.ofFn f).flatten.length = ((List.finRange 94).map fun j => (f j).length).sum := by
  rw [List.length_flatten, List.ofFn_eq_map, List.map_map]
  rfl

theorem sum_mono (f g : Fin 94 → ℕ) (h : ∀ j, f j ≤ g j) :
    ((List.finRange 94).map f).sum ≤ ((List.finRange 94).map g).sum :=
  List.sum_le_sum (fun j _ => h j)

theorem single_le (f : Fin 94 → ℕ) (j : Fin 94) : f j ≤ ((List.finRange 94).map f).sum :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

theorem pad_len (cC T : ℕ) (h : T ≤ cC) : (ZeroPadding.pad cC (List.replicate T true)).length = cC := by
  unfold ZeroPadding.pad; simp; omega

/-- **The HASH child's steps are within C4H's `hCoreCost`.** -/
theorem coreSteps_le (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm) (R0 : CompilerMachine.Req.C3Req)
    (D : HashData) (c : HbCaps) (Kc : ℕ) (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request)
    (hplen : p.length + 1 ≤ 2 * D.MP.t * D.MP.ell0) (hcC : 2 * D.MP.t * D.MP.ell0 ≤ c.cC) :
    hCoreSteps wa a R0 D c Kc p b r ≤ hCoreCost wa a R0 D c Kc (p ++ [b]) r := by
  set X' := hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b])) with hX'
  set S' := ((List.finRange 94).map fun j => (hb0 X' j).length).sum with hS'
  have hKW : ∀ j, (hb0 (hbX D c 0 0) j).length ≤ (hb0 X' j).length := by
    intro j
    by_cases h80 : j.val = 80
    · have e : j = ⟨80, by omega⟩ := Fin.ext h80
      rw [e, hb0_80, hb0_80]
      simp [SignedSortKey.binary_length]
    · by_cases h93 : j.val = 93
      · have e : j = ⟨93, by omega⟩ := Fin.ext h93
        rw [e, hb0_93, hb0_93, pad_len _ _ (by omega), pad_len _ _ (by omega)]
      · have := hb0_other D c (p ++ [b]).length (SeedFix.listNum (p ++ [b])) j h80 h93
        rw [hX', this]
  have hS0 : ((List.finRange 94).map fun j => (hb0 (hbX D c 0 0) j).length).sum ≤ S' := sum_mono _ _ hKW
  have hcp : copiesCost (hb0 (hbX D c 0 0)) jsC ≤ 10 * S' + 188 := by
    have h1 : copiesCost (hb0 (hbX D c 0 0)) jsC ≤ copiesCost (hb0 (hbX D c 0 0)) (List.finRange 94) :=
      copiesCost_sub _ List.filter_sublist
    have h2 := copiesCost_eq (hb0 (hbX D c 0 0)) (List.finRange 94)
    rw [List.length_finRange] at h2
    omega
  have h93 : (hb0 (hbX D c 0 0) ⟨93, by omega⟩).length ≤ S' := by
    have := single_le (fun j => (hb0 X' j).length) ⟨93, by omega⟩
    rw [hb0_93, pad_len _ _ (by omega)]
    rw [hb0_93, pad_len _ _ (by omega)] at this
    exact this
  have hflat : (List.ofFn (hb0 X')).flatten.length = S' := flatten_len _
  unfold hCoreSteps unitCost hCoreCost hbPrepCost prepCost
  rw [hflat]
  have hT : X'.T2 * X'.ℓ = 2 * D.MP.t * D.MP.ell0 := rfl
  rw [hT]
  omega

end NearCubicWires.WireExponent3_5.PrimT.C4Hf
