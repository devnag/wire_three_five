import Proof.Wire_3_5.Primitive.SeedFix.C4HkG

/-! # The HASH stage, part 8: the stage on the HASH setup's bank

"Greedily choose a child with no larger value [...] the printed decisions are the fixed hash's bits" (P3:2327-2336);
the THR writer's input `req.word ++ frame hashBits`. From any HASH setup run to a C4H-a `HBank2` bank
(the reference one), the HASH stage is C4's wrapper (`C4Wrap.wrapM`) around: the setup then the pre-loop stage (`preZ`), the decision
loop of a HASH child family (`HashFamAt2`) docked by `hashExt` (**`hash_entry`**, a `LoopEntry`), and the finisher
`finM` docked on the request's copy, the loop's prefix and port `2` (**`hash_fin`**, a `FinDock`). **`hashLay_run`**:
the stage ends with `frame (w ++ frame bits)` on port `2`, `bits` the loop's decisions.

Paper quantity of the main type: the HASH stage's output `frame (w ++ frame bits)` (the THR writer's input). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Hk
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Set (slx slx_some slx_none)
open NearCubicWires.WireExponent3_5.PrimT.C4Wrap (LoopEntry FinDock postLoop wrapM wrapCost pfxL)

/-- The finisher's dock: its output on port `2`, the request's copy on `off`, the loop's prefix on `off + 1`. -/
def finExtH {x : ℕ} (off : ℕ) (hr : off + 3 ≤ 3 + x) (j : Fin (2 + 2 + 0 + 1)) : Option (Fin (3 + x)) :=
  if j.val = 0 then some ⟨2, by omega⟩ else if j.val = 2 then some ⟨off, by omega⟩
  else if j.val = 3 then some ⟨off + 1, by omega⟩ else none

section Stage
variable {x : ℕ} (L : C4Set.Lay) (hLx : L.N ≤ 3 + x) (A : C4Iface.AsmStage)
  (wa : RepairRepresentation.WilliamsAlgorithm) (PRE POST : List Bool) (KW : Fin 94 → List Bool) (q uu W sh : ℕ)
  (bits : List Bool) (hF : HashFamAt2 A wa PRE POST KW q uu W sh bits)
  (B : Fin (3 + x) → List Bool) (w v : List Bool) (ρ : ℕ) (hkT : Fin 94 → Fin (3 + x)) (hqT : Fin (3 + x))
  (off : ℕ) (hB : HBank2 L hLx B w v PRE POST KW q uu ρ hkT hqT off)
  (hr : off + 12 ≤ 3 + x) (hn : off + 12 + (hF.F.T + 1 + 1 + 1) ≤ 3 + x)
  (B2 : Fin (3 + x) → List Bool) (hP : PreBank off hr (hF.F.T + 1 + 1 + 1) hn B B2 w sh (2 ^ ρ))

include hB in
theorem ext_bounds (j : Fin (hF.F.T + 1 + 1 + 1)) (g : Fin (3 + x))
    (h : hashExt L hLx A wa hkT hqT off (by omega) hF.F.T j = some g) : 3 ≤ g.val ∧ g.val < off + 3 := by
  have hN := C4Set.Lay.N_eq L
  have hk0 := hB.koff ⟨0, by omega⟩
  rcases hashExt_some L hLx A wa hkT hqT off (by omega) hF.F.T h with ⟨a, b, e⟩ | ⟨a, e⟩ | ⟨a, e⟩ | ⟨a, e⟩
  · have := tgt_range L hLx A wa hkT hqT off (by omega) hB.koff ⟨hB.qoff.1, hB.qoff.2.1⟩ j.val a b
    rw [← e] at this; omega
  · rw [e]; simp only [gS_val, C4Set.Lay.gLG]; omega
  · rw [e]; simp only [gS_val, C4Set.Lay.gRR]; omega
  · omega

theorem pfx_slot_H :
    slx (off + 12) hn (hashExt L hLx A wa hkT hqT off (by omega) hF.F.T) (pfxL hF.F) = ⟨off + 1, by omega⟩ := by
  have hN := C4Set.Lay.N_eq L
  have hFt := hF.ht
  have hU : HU = 253 := rfl
  have hC : CTH A wa = A.t + (HU + C4Pipe.CN wa) := rfl
  have hv : (pfxL hF.F).val = A.t + 94 := hF.pfx
  have hk : (pfxL hF.F).val < CTH A wa ∧ hKeepN A wa (pfxL hF.F).val = true := by
    rw [hv]
    refine ⟨by omega, ?_⟩
    unfold hKeepN
    rw [if_neg (by omega), if_pos (by omega)]
    simp
  rw [slx_some (show hashExt L hLx A wa hkT hqT off (by omega) hF.F.T (pfxL hF.F) =
    some (hashTgt L hLx A wa hkT hqT off (by omega) (pfxL hF.F).val) by unfold hashExt; rw [if_pos hk])]
  rw [hv]
  unfold hashTgt
  rw [if_neg (by omega), dif_neg (by omega), if_pos (by omega)]

include hB hP in
/-- **The loop's entry** on the pre-loop bank (`C4Wrap.LoopEntry`). -/
theorem hash_entry (hRc : hF.F.cellCost + 1 ≤ 2 ^ ρ) :
    LoopEntry hF.F (2 ^ ρ) (2 ^ ρ + 1) (off + 12) hn (hashExt L hLx A wa hkT hqT off (by omega) hF.F.T) w v B2 where
  hR := hRc
  hL := le_refl _
  h3 := by omega
  inj := ext_inj L hLx A wa hkT hqT off (by omega) hB.koff hB.kinj hB.qoff hF.F.T
  lt := fun i g h => by have := ext_bounds L hLx A wa PRE POST KW q uu W sh bits hF B w v ρ hkT hqT off hB hr i g h; omega
  port := fun i g h => by
    have := ext_bounds L hLx A wa PRE POST KW q uu W sh bits hF B w v ρ hkT hqT off hB hr i g h; omega
  pfx := fun g h => by
    have := ext_bounds L hLx A wa PRE POST KW q uu W sh bits hF B w v ρ hkT hqT off hB hr _ g h; omega
  entry := entry_H L hLx A wa PRE POST KW q uu W sh bits hF B w v ρ hkT hqT off hB hr hn B2 hP
  p0 := hP.p0
  p1 := by
    have hk0 := hB.koff ⟨0, by omega⟩
    have hN := C4Set.Lay.N_eq L
    rw [hP.keep _ (by simp only; omega) (by simp)]
    exact hB.p1
  p2 := by
    have hk0 := hB.koff ⟨0, by omega⟩
    have hN := C4Set.Lay.N_eq L
    rw [hP.keep _ (by simp only; omega) (by simp)]
    exact hB.p2

include hB hP in
/-- **The finisher's dock** after the loop (`C4Wrap.FinDock`). -/
theorem hash_fin (hroom : off + 12 + (hF.F.T + 1 + 1 + 1) + (2 + 2 + 0 + 1) ≤ 3 + x) :
    FinDock (off + 12 + (hF.F.T + 1 + 1 + 1)) hroom (finExtH off (by omega)) fiO
      (fun i => if i = fiW then frame w else if i = fiP then frame bits else [])
      (postLoop hF.F (off + 12) hn (hashExt L hLx A wa hkT hqT off (by omega) hF.F.T) B2) where
  inj := fun i j g hi hj => by
    have hk0 := hB.koff ⟨0, by omega⟩
    have hN := C4Set.Lay.N_eq L
    unfold finExtH at hi hj
    apply Fin.ext
    split_ifs at hi hj <;> simp only [Option.some.injEq, reduceCtorEq] at hi hj <;> subst hi <;>
      simp only [Fin.mk.injEq] at hj <;> omega
  lt := fun i g hi => by
    unfold finExtH at hi
    split_ifs at hi <;> simp only [Option.some.injEq, reduceCtorEq] at hi <;> subst hi <;> simp only <;> omega
  port := fun i g hi => by
    have hk0 := hB.koff ⟨0, by omega⟩
    have hN := C4Set.Lay.N_eq L
    unfold finExtH at hi
    split_ifs at hi <;> simp only [Option.some.injEq, reduceCtorEq] at hi <;> subst hi <;> simp only <;> omega
  out := by unfold finExtH; rfl
  inp := fun j g hj => by
    have hk0 := hB.koff ⟨0, by omega⟩
    have hN := C4Set.Lay.N_eq L
    have hps := pfx_slot_H L hLx A wa PRE POST KW q uu W sh bits hF hkT hqT off hr hn
    unfold finExtH at hj
    split_ifs at hj with h0 h2 h3 <;> simp only [Option.some.injEq, reduceCtorEq] at hj <;> subst hj
    · have ej : j = fiO := Fin.ext h0
      subst ej
      unfold postLoop
      rw [hps, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this; omega)]
      rw [hP.keep _ (by simp only; omega) (by simp)]
      exact hB.p2
    · have ej : j = fiW := Fin.ext h2
      subst ej
      unfold postLoop
      rw [hps, Function.update_of_ne (fun e => by have := congrArg Fin.val e; simp at this)]
      rw [hP.wT]; rfl
    · have ej : j = fiP := Fin.ext h3
      subst ej
      unfold postLoop
      rw [hps, Function.update_self, hF.loop]; rfl
  own := fun j hj => by
    unfold finExtH at hj
    split_ifs at hj with h0 h2 h3
    have n2 : j ≠ fiW := fun e => h2 (by rw [e]; rfl)
    have n3 : j ≠ fiP := fun e => h3 (by rw [e]; rfl)
    simp only [if_neg n2, if_neg n3]
  blank := fun i hi => by
    have hps := pfx_slot_H L hLx A wa PRE POST KW q uu W sh bits hF hkT hqT off hr hn
    unfold postLoop
    rw [hps, Function.update_of_ne (fun e => by rw [e] at hi; simp at hi; omega)]
    exact hP.blank i hi

end Stage

end NearCubicWires.WireExponent3_5.PrimT.C4Hk
