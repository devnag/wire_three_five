import Proof.Wire_3_5.Selection.GatePre2

/-! # C1.4: the weight tables in machine order (P3:1339-1344, 1195-1197)

Paper: "The center bits can be divided into two halves differing in size by at most one while keeping each code
block on its assigned side" (P3:1196-1197). The point routine walks a half in machine order (C1.4's `coordL`,
`coordR`: the blocks in descending order, then the free coordinates); the gate record `GA` lists the weights in
coordinate order. This module copies records of `GA` in counted runs (`skipN_rst`, `copyN_rst`) and proves the
machine-order tables are those runs (`tblL_eq`, `tblR_eq`). Paper quantity: a half's weights in the machine's order. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort NearCubicWires.WireExponent3_5.SelectionMachine.Point
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit (cloop cloop_spec)
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write)

variable {ns nr : ℕ}

/-! ## Counted runs of records -/

section Runs
variable (cap : ℕ) (σ0 : WState ns nr) {A B : Fin (ns + 1)} {CA CB : Fin nr} (L : List Bool)
variable (hAB : A ≠ B) (hC : CA ≠ CB)
include hAB hC

/-- **Skip `k` records** from record `j` of a table on `A`. -/
theorem skipN_rst (K T : Fin nr) (hKT : K ≠ T) (hK1 : K ≠ CA) (hK2 : K ≠ CB) (hT1 : T ≠ CA) (hT2 : T ≠ CB) (W : ℕ)
    (recs : List (Bool × ℕ)) (post : List Bool) (hA : σ0.st A = tbl W recs ++ post) (j k : ℕ) (out : List Bool)
    (hK : σ0.val K = k) (hT : σ0.val T = 0) (hjk : j + k ≤ recs.length) (hcap : recs.length * (2 * W + 2) + 2 < cap) :
    WExec cap (cloop K T (skipRec A CA)) (rst σ0 A B CA CB L (j * (2 * W + 2)) out)
      (rst σ0 A B CA CB L ((j + k) * (2 * W + 2)) out) (k * (13 * W + 13 + 8) + 1 + 1 + (7 * k + 1)) := by
  have hl := Point.cloopM cap K T hKT (skipRec A CA) (fun σ i => rst σ A B CA CB L ((j + i) * (2 * W + 2)) out)
    (fun σ i v w => rst_setv2 σ L hAB hC K T v w hK1 hK2 hT1 hT2 _ _) σ0 k (13 * W + 13) hK hT
    (by have := Nat.le_mul_of_pos_right recs.length (show 0 < 2 * W + 2 by omega); omega) (by
      intro i hi v w
      have hp : j + i < recs.length := by omega
      have hsp := tbl_split W recs (j + i) hp
      have hlen : (tbl W (recs.take (j + i))).length = (j + i) * (2 * W + 2) := by
        rw [tbl_length, List.length_take, Nat.min_eq_left (by omega)]
      have h := skipRec_rst cap ((σ0.setv K v).setv T w) L hAB hC W (recAt recs (j + i)) (tbl W (recs.take (j + i)))
        (tbl W (recs.drop (j + i + 1)) ++ post) out (by simp only [WState.setv_st, hA, hsp, recBits, List.append_assoc])
        (by rw [hlen]; nlinarith)
      rw [hlen] at h
      refine WExec.cast cap h ?_ le_rfl
      congr 1; ring)
  simpa using hl

/-- **Copy `k` records** from record `j` of a table on `A`, their signs xor `neg`. -/
theorem copyN_rst (neg : Bool) (K T : Fin nr) (hKT : K ≠ T) (hK1 : K ≠ CA) (hK2 : K ≠ CB) (hT1 : T ≠ CA)
    (hT2 : T ≠ CB) (W : ℕ) (recs : List (Bool × ℕ)) (post : List Bool) (hA : σ0.st A = tbl W recs ++ post) (j k : ℕ)
    (out : List Bool) (hK : σ0.val K = k) (hT : σ0.val T = 0) (hjk : j + k ≤ recs.length)
    (hcap : recs.length * (2 * W + 2) + 2 < cap) (hq : out.length + k * (2 * W + 2) + 2 < cap) :
    WExec cap (cloop K T (copyRec neg A B CA CB)) (rst σ0 A B CA CB L (j * (2 * W + 2)) out)
      (rst σ0 A B CA CB L ((j + k) * (2 * W + 2))
        (out ++ (List.range k).flatMap (fun i => recBits W (xor (recAt recs (j + i)).1 neg, (recAt recs (j + i)).2))))
      (k * (40 * W + 40 + 8) + 1 + 1 + (7 * k + 1)) := by
  have hl := Point.cloopM cap K T hKT (copyRec neg A B CA CB) (fun σ i => rst σ A B CA CB L ((j + i) * (2 * W + 2))
      (out ++ (List.range i).flatMap (fun i' => recBits W (xor (recAt recs (j + i')).1 neg, (recAt recs (j + i')).2))))
    (fun σ i v w => rst_setv2 σ L hAB hC K T v w hK1 hK2 hT1 hT2 _ _) σ0 k (40 * W + 40) hK hT
    (by have := Nat.le_mul_of_pos_right recs.length (show 0 < 2 * W + 2 by omega); omega) (by
      intro i hi v w
      have hp : j + i < recs.length := by omega
      have hsp := tbl_split W recs (j + i) hp
      have hlen : (tbl W (recs.take (j + i))).length = (j + i) * (2 * W + 2) := by
        rw [tbl_length, List.length_take, Nat.min_eq_left (by omega)]
      have hol : ((List.range i).flatMap (fun i' => recBits W (xor (recAt recs (j + i')).1 neg,
          (recAt recs (j + i')).2))).length = i * (2 * W + 2) := by
        rw [List.length_flatMap]; simp [recBits_length, List.sum_replicate]
      have h := copyRec_rst cap ((σ0.setv K v).setv T w) L hAB hC neg W (recAt recs (j + i)) (tbl W (recs.take (j + i)))
        (tbl W (recs.drop (j + i + 1)) ++ post)
        (out ++ (List.range i).flatMap (fun i' => recBits W (xor (recAt recs (j + i')).1 neg, (recAt recs (j + i')).2)))
        (by simp only [WState.setv_st, hA, hsp, recBits, List.append_assoc]) (by rw [hlen]; nlinarith)
        (by rw [List.length_append, hol]; nlinarith)
      rw [hlen] at h
      refine WExec.cast cap h ?_ le_rfl
      congr 1
      · ring
      · rw [List.range_succ, List.flatMap_append]; simp)
  simpa using hl

end Runs

/-! ## The tables in machine order are runs of the gate record -/

/-- The gate record's weights, in coordinate order. -/
def coordRecs {n : ℕ} (g : NormalizedThresholdGate n) : List (Bool × ℕ) :=
  List.ofFn fun i : Fin n => (decide (g.weight i < 0), (g.weight i).natAbs)

theorem gateRec_eq (W : ℕ) {n : ℕ} (g : NormalizedThresholdGate n) :
    gateRec W g = tbl W (coordRecs g) ++ recBits W (decide (g.threshold < 0), g.threshold.natAbs) := by
  unfold gateRec coordRecs tbl
  rw [List.flatMap_def, List.map_ofFn]
  rfl

theorem recAt_coord {n : ℕ} (g : NormalizedThresholdGate n) (c : ℕ) (hc : c < n) :
    recAt (coordRecs g) c = (decide (wAt g c < 0), (wAt g c).natAbs) := by
  unfold recAt coordRecs wAt
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_ofFn, dif_pos hc]

theorem coordRecs_length {n : ℕ} (g : NormalizedThresholdGate n) : (coordRecs g).length = n := by
  simp [coordRecs]

theorem range_mul_flatMap {α : Type} (F : ℕ → List α) (b : ℕ) : ∀ h : ℕ,
    (List.range (h * b)).flatMap F = (List.range h).flatMap (fun t => (List.range b).flatMap (fun i => F (t * b + i)))
  | 0 => by simp
  | h + 1 => by
    rw [add_one_mul, List.range_add, List.flatMap_append, range_mul_flatMap F b h, List.range_succ,
      List.flatMap_append, List.flatMap_map]
    simp

section Tables
variable (P : StarParams) (g : NormalizedThresholdGate P.n) (W : ℕ)

theorem coordL_blk (t i : ℕ) (ht : t < hh P) (hi : i < P.b) : coordL P (t * P.b + i) = (hh P - 1 - t) * P.b + i := by
  have hdm := divmod t i P.b hi
  unfold coordL
  rw [if_pos (blk_lt t (hh P) i P.b ht hi), hdm.1, hdm.2]

theorem coordR_blk (t i : ℕ) (ht : t < hh P) (hi : i < P.b) :
    coordR P (t * P.b + i) = (hh P + (hh P - 1 - t)) * P.b + i := by
  have hdm := divmod t i P.b hi
  unfold coordR
  rw [if_pos (blk_lt t (hh P) i P.b ht hi), hdm.1, hdm.2]

theorem coordL_free (f : ℕ) : coordL P (hh P * P.b + f) = P.r * P.b + f := by
  unfold coordL; rw [if_neg (by omega)]; congr 1; omega

theorem coordR_free (f : ℕ) : coordR P (hh P * P.b + f) = P.r * P.b + fL P + f := by
  unfold coordR; rw [if_neg (by omega)]; congr 1; omega

/-- **The left table as runs**: block `hh − 1 − t` for `t = 0, …, h − 1`, then the free left coordinates, negated. -/
theorem tblL_eq : tbl W (recsL P g) =
    (List.range (hh P)).flatMap (fun t => (List.range P.b).flatMap (fun i =>
      recBits W (xor (recAt (coordRecs g) ((hh P - 1 - t) * P.b + i)).1 true,
        (recAt (coordRecs g) ((hh P - 1 - t) * P.b + i)).2))) ++
    (List.range (fL P)).flatMap (fun f => recBits W (xor (recAt (coordRecs g) (P.r * P.b + f)).1 true,
        (recAt (coordRecs g) (P.r * P.b + f)).2)) := by
  unfold tbl recsL lw
  rw [List.flatMap_map, List.range_add, List.flatMap_append, range_mul_flatMap, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr; intro t ht
    apply List.flatMap_congr; intro i hi
    have ht' := List.mem_range.mp ht
    have hi' := List.mem_range.mp hi
    rw [coordL_blk P t i ht' hi', recAt_coord g _ (by
      have := coordL_lt P (t * P.b + i) (by unfold lw; have := blk_lt t (hh P) i P.b ht' hi'; omega)
      rwa [coordL_blk P t i ht' hi'] at this)]
    simp [Bool.xor_true]
  · apply List.flatMap_congr; intro f hf
    have hf' := List.mem_range.mp hf
    rw [coordL_free P f, recAt_coord g _ (by
      have := coordL_lt P (hh P * P.b + f) (by unfold lw; omega)
      rwa [coordL_free P f] at this)]
    simp [Bool.xor_true]

/-- **The right table as runs**: block `h + (h − 1 − t)`, then the free right coordinates. -/
theorem tblR_eq : tbl W (recsR P g) =
    (List.range (hh P)).flatMap (fun t => (List.range P.b).flatMap (fun i =>
      recBits W (xor (recAt (coordRecs g) ((hh P + (hh P - 1 - t)) * P.b + i)).1 false,
        (recAt (coordRecs g) ((hh P + (hh P - 1 - t)) * P.b + i)).2))) ++
    (List.range (fR P)).flatMap (fun f => recBits W (xor (recAt (coordRecs g) (P.r * P.b + fL P + f)).1 false,
        (recAt (coordRecs g) (P.r * P.b + fL P + f)).2)) := by
  unfold tbl recsR rw
  rw [List.flatMap_map, List.range_add, List.flatMap_append, range_mul_flatMap, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr; intro t ht
    apply List.flatMap_congr; intro i hi
    have ht' := List.mem_range.mp ht
    have hi' := List.mem_range.mp hi
    rw [coordR_blk P t i ht' hi', recAt_coord g _ (by
      have := coordR_lt P (t * P.b + i) (by unfold rw; have := blk_lt t (hh P) i P.b ht' hi'; omega)
      rwa [coordR_blk P t i ht' hi'] at this)]
    simp
  · apply List.flatMap_congr; intro f hf
    have hf' := List.mem_range.mp hf
    rw [coordR_free P f, recAt_coord g _ (by
      have := coordR_lt P (hh P * P.b + f) (by unfold rw; omega)
      rwa [coordR_free P f] at this)]
    simp

end Tables

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
