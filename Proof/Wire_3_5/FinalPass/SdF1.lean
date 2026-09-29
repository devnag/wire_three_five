import Proof.Wire_3_5.FinalPass.SdW1
import Proof.Wire_3_5.Primitive.Writers.CallIndex
import Proof.Wire_3_5.FinalPass.ThrSz1

/-! # S4 (the seeds phase), part 48: the star call's sizes, polynomial in `n` (P3:3170-3178)

At a star call the seeds phase's numbers are polynomial in `n`: the star parameters (`star_le`: `b, s, r/2, hL,
dRow, dR, n − rb ≤ n + 1`, `2^s ≤ n + 1`, `s·(r/2) ≤ n²`), the carriers' mask lengths (`carLen_le`, via
`mask_len2`) and weight widths (`tabHc_le`, `Hof_le`, via ThrSz's `tabGW_len`), the filter's length, capacity and
error exponent (CallIndex's `cap_le`), the seed count and width (`gapSeed_le`, `sw_lt`), the tables' and the tables
word's lengths (`tbl_len`, `twW_len`).

Paper quantity of the main type: the seeds phase's sizes at a star call (P3:3170-3178, with P3:2029-2030). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo (dRow dR hL)
open NearCubicWires.WireExponent3_5.FinalPass.Corner NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.SupplierWalk (majorityThreshold)

theorem star_le (P : StarParams) :
    P.b ≤ P.n ∧ P.s ≤ P.n ∧ P.r / 2 ≤ P.n ∧ 2 ^ P.s ≤ P.n + 1 ∧ hL P ≤ P.n ∧ dRow P ≤ P.n + 1 ∧ dR P ≤ P.n ∧
      P.n - P.r * P.b - hL P ≤ P.n ∧ P.n - P.r * P.b ≤ P.n ∧ P.s * (P.r / 2) ≤ P.n * P.n := by
  have hrb := P.r_mul_b_le
  have hr2 := P.two_le_r
  have h4 := P.four_r_le_n
  have hbs := P.b_succ
  have hb : P.b ≤ P.n := by
    have : P.b ≤ P.r * P.b := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hs : P.s ≤ P.n := by
    have h1 : P.s < 2 ^ P.s := Nat.lt_two_pow_self
    omega
  have hdRow : dRow P ≤ P.n + 1 := by
    show P.leftCenterBits ≤ P.n + 1
    unfold StarParams.leftCenterBits
    have : P.r / 2 * (P.b - P.s) ≤ P.r / 2 * P.b := Nat.mul_le_mul_left _ (by omega)
    have : P.r / 2 * P.b ≤ P.r * P.b := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdR : dR P ≤ P.n := by
    show P.rightCenterBits ≤ P.n
    unfold StarParams.rightCenterBits
    have : P.r / 2 * (P.b - P.s) ≤ P.r / 2 * P.b := Nat.mul_le_mul_left _ (by omega)
    have : P.r / 2 * P.b ≤ P.r * P.b := Nat.mul_le_mul_right _ (by omega)
    have : P.r / 2 * P.b + P.r / 2 * P.b ≤ P.r * P.b := by
      have hre : P.r / 2 * 2 ≤ P.r := Nat.div_mul_le_self _ _
      calc P.r / 2 * P.b + P.r / 2 * P.b = P.r / 2 * 2 * P.b := by ring
        _ ≤ P.r * P.b := Nat.mul_le_mul_right _ hre
    omega
  refine ⟨hb, hs, by omega, by omega, by unfold hL; omega, hdRow, hdR, by omega, by omega,
    Nat.mul_le_mul hs (by omega)⟩

theorem mask_len2 {n : ℕ} : ∀ X : Stars.Carrier n, (maskGates X).length = 2 * X.length
  | [] => rfl
  | g :: X => by
    have ih := mask_len2 X
    unfold maskGates at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    omega

theorem carLen_le {n : ℕ} (carriers : List (Stars.Carrier n))
    (henv : ∀ X ∈ carriers, Stars.Carrier.WithinEnvelope 26 X) (k : ℕ) :
    Seams.carLen carriers k ≤ 2 * (n + 1) ^ 26 := by
  unfold Seams.carLen
  split_ifs with h
  · rw [mask_len2]
    have := (henv (carriers.get ⟨k, h⟩) (List.get_mem carriers ⟨k, h⟩)).1
    omega
  · omega

theorem tabHc_le {n : ℕ} (X : Stars.Carrier n) (c : ℕ) (hc : ∀ g ∈ X, 2 * (4 * n + 9 + 4 * g.encodingBits) + 1 ≤ c) :
    PrimT.tabH X ≤ X.length * c := by
  unfold PrimT.tabH PrimT.tabSeg
  rw [List.length_flatMap]
  exact lsum_le X (fun g => (frame (PrimT.tabGW g)).length) c (fun g hg => by
    have h1 := ThrSz.tabGW_len g
    have h2 := hc g hg
    rw [frame_eq_frameP, List.length_append, frameP_length, List.length_singleton]
    omega)

theorem Hof_le {n : ℕ} (carriers : List (Stars.Carrier n))
    (henv : ∀ X ∈ carriers, Stars.Carrier.WithinEnvelope 26 X) (k : Fin 2) :
    Hof carriers k ≤ (n + 1) ^ 26 * (8 * n + 19 + 8 * (n + 1) ^ 26) := by
  unfold Hof
  split_ifs with h
  · have he := henv (carriers.get ⟨k.val, h⟩) (List.get_mem carriers ⟨k.val, h⟩)
    have := tabHc_le (carriers.get ⟨k.val, h⟩) (8 * n + 19 + 8 * (n + 1) ^ 26) (fun g hg => by
      have := he.2 g hg
      omega)
    exact le_trans this (Nat.mul_le_mul_right _ he.1)
  · exact Nat.zero_le _

theorem sw_lt (FP : GapParams) : Seams.seedWidth FP < Fintype.card (GapSeed FP) := by
  rw [card_gapSeed, ← seedWidth_eq]
  exact Nat.lt_two_pow_self

theorem walkLen_le (FP : GapParams) : FP.walkLen ≤ FP.errExp + 1 := by
  have : FP.walkLen = 2 * (FP.errExp / 4) + 1 := rfl
  omega

theorem thr_le (FP : GapParams) : majorityThreshold FP.walkLen ≤ FP.walkLen := by
  unfold majorityThreshold; omega

theorem tbl_len (FP : GapParams) (e : GapSeed FP) (L : ℕ) :
    (tableWord (filterTable FP e L)).length ≤ (FP.errExp + 1) * (258 + 256 * L) + 1 := by
  have e : 2 + 128 * (2 * L + 2) = 258 + 256 * L := by ring
  rw [tab_len, e]
  have := Nat.mul_le_mul_right (258 + 256 * L) (walkLen_le FP)
  omega

theorem twW_len (FP : GapParams) (es : List (GapSeed FP)) (L0 L1 : ℕ) :
    (twW FP es L0 L1).length =
      es.length * (2 * (FP.walkLen * (2 + 128 * (2 * L0 + 2)) + 1) + 1 +
        (2 * (FP.walkLen * (2 + 128 * (2 * L1 + 2)) + 1) + 1)) + 1 := by
  unfold twW
  rw [List.length_append, List.length_flatMap, List.length_singleton]
  have : ∀ e ∈ es, (fun e => (frame (tb FP e L0) ++ frame (tb FP e L1)).length) e =
      2 * (FP.walkLen * (2 + 128 * (2 * L0 + 2)) + 1) + 1 + (2 * (FP.walkLen * (2 + 128 * (2 * L1 + 2)) + 1) + 1) :=
    fun e _ => by
      simp only [List.length_append, frame_eq_frameP, frameP_length, List.length_singleton, tb, tab_len]
  rw [List.map_congr_left this]
  simp [List.sum_replicate]

end NearCubicWires.WireExponent3_5.FinalPass.Sd
