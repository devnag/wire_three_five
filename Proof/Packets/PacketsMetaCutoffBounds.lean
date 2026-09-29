import Proof.Packets.PacketsMetaCutoffSpec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.PacketsMeta.CutoffMath NearCubicWires.ThresholdAlignedEnvelope
noncomputable section

namespace Bounds
open Lev Setup Tail Prog

/-! ## Fitting the register width -/

theorem natBitLength_le (x : ℕ) : natBitLength x ≤ (natWord x).length := by
  rw [ReadNat.natWord_length]
  omega

theorem fits_of_len (W : ℕ) (e : CD) (h : (pay e).length ≤ W) : Fits W e := by
  have hl : (pay e).length = (natWord e.1).length + (natWord e.2.length).length + (e.2.flatMap exactWord).length := by
    rw [pay_eq]
    simp only [List.length_append]
  refine ⟨?_, ?_, ?_⟩
  · have := natBitLength_le e.1
    omega
  · have := natBitLength_le e.2.length
    omega
  · intro G hG
    have hGl : (exactWord G).length ≤ (e.2.flatMap exactWord).length := by
      rw [List.length_flatMap]
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨G, hG, rfl⟩)
    have hE : (exactWord G).length = ((Child.ws G).flatMap intWord).length + (intWord G.target).length := by
      rw [Child.exactWord_eq, List.length_append]
    refine ⟨?_, ?_, ?_⟩
    · have h1 := childMagnitude_lt e.2 G hG
      have h2 := recMag_childRec G
      have h3 : (childRec G).1 ≤ recMag (childRec G) := by
        simp only [recMag]
        omega
      have h4 : (exactListWord e.2).length ≤ (pay e).length := by
        simp [pay, List.length_append]
      calc (childRec G).1 ≤ recMag (childRec G) := h3
        _ = childMagnitude G := h2
        _ < 2 ^ (exactListWord e.2).length := h1
        _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    · intro j hj
      have hw : (intWord ((Child.ws G)[j]'(by rw [Child.ws_length]; exact hj))).length ≤
          ((Child.ws G).flatMap intWord).length := by
        rw [List.length_flatMap]
        exact List.le_sum_of_mem (List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩)
      have h1 := intWord_length ((Child.ws G)[j]'(by rw [Child.ws_length]; exact hj))
      have h2 := natBitLength_le ((Child.ws G)[j]'(by rw [Child.ws_length]; exact hj)).natAbs
      omega
    · have h1 := intWord_length G.target
      have h2 := natBitLength_le G.target.natAbs
      omega

theorem pay_pad_len : (pay padCD).length = 10 := by
  simp [pay, padCD, padG, exactListWord, exactWord, intWord, ReadNat.natWord_length, natBitLength]

/-! ## The nested sum -/

theorem sum_map_le {α : Type} (l : List α) (g : α → ℕ) (M : ℕ) (h : ∀ x ∈ l, g x ≤ M) :
    (l.map g).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h x (by simp)
    have h2 := ih (fun y hy => h y (by simp [hy]))
    rw [Nat.succ_mul]
    omega

theorem nestedSum_le (T0 T1 T2 T3 : List Rec) (f : List Rec → ℕ) (M : ℕ)
    (h : ∀ x0 ∈ T0, ∀ x1 ∈ T1, ∀ x2 ∈ T2, ∀ x3 ∈ T3, f [x0, x1, x2, x3] ≤ M) :
    nestedSum T0 T1 T2 T3 f ≤ T0.length * (T1.length * (T2.length * (T3.length * M))) := by
  unfold nestedSum
  apply sum_map_le
  intro x0 h0
  apply sum_map_le
  intro x1 h1
  apply sum_map_le
  intro x2 h2
  apply sum_map_le
  intro x3 h3
  exact h x0 h0 x1 h1 x2 h2 x3 h3

theorem selMag_lt (R : ℕ) (x0 x1 x2 x3 : Rec) (h0 : recMag x0 < 2 ^ R) (h1 : recMag x1 < 2 ^ R)
    (h2 : recMag x2 < 2 ^ R) (h3 : recMag x3 < 2 ^ R) : selMag [x0, x1, x2, x3] < 2 ^ (4 * R + 10) := by
  obtain ⟨a0, p0, q0⟩ := x0
  obtain ⟨a1, p1, q1⟩ := x1
  obtain ⟨a2, p2, q2⟩ := x2
  obtain ⟨a3, p3, q3⟩ := x3
  simp only [recMag] at h0 h1 h2 h3
  rw [Body.selMag_eq, Horner.horner4, Horner.horner4, Horner.horner4]
  have hbase : Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 ≤ 2 ^ (R + 2) := by
    have e : 2 ^ (R + 2) = 4 * 2 ^ R := by rw [pow_add]; ring
    simp only [Body.base]
    omega
  have hB1 : 1 ≤ 2 ^ (R + 2) := Nat.one_le_two_pow
  have hbig : 4 * 2 ^ R * (2 ^ (R + 2)) ^ 3 = 2 ^ (4 * R + 8) := by
    rw [← pow_mul, show 4 * 2 ^ R = 2 ^ 2 * 2 ^ R by norm_num, ← pow_add, ← pow_add]
    ring_nf
  have hA := horner_lt (2 ^ R) (2 ^ (R + 2)) a0 a1 a2 a3 _ (by omega) (by omega) (by omega) (by omega) hbase hB1
  have hP := horner_lt (2 ^ R) (2 ^ (R + 2)) p0 p1 p2 p3 _ (by omega) (by omega) (by omega) (by omega) hbase hB1
  have hQ := horner_lt (2 ^ R) (2 ^ (R + 2)) q0 q1 q2 q3 _ (by omega) (by omega) (by omega) (by omega) hbase hB1
  rw [hbig] at hA hP hQ
  have hN := Int.natAbs_sub_le
    ((p0 + Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 * (p1 + Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 *
      (p2 + Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 * p3)) : ℕ) : ℤ)
    ((q0 + Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 * (q1 + Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 *
      (q2 + Body.base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 * q3)) : ℕ) : ℤ)
  simp only [Int.natAbs_natCast] at hN
  have e10 : 2 ^ (4 * R + 10) = 4 * 2 ^ (4 * R + 8) := by rw [show 4 * R + 10 = (4 * R + 8) + 2 by ring, pow_add]; ring
  omega

/-! ## The loops' cost -/

theorem len_le_flatMap_exactWord {n : ℕ} : ∀ l : List (ExactThresholdGate n), l.length ≤ (l.flatMap exactWord).length
  | [] => by simp
  | G :: l => by
    have := len_le_flatMap_exactWord l
    have h1 : 1 ≤ (exactWord G).length := by
      rw [Child.exactWord_eq, List.length_append, intWord_length]
      omega
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem levCost_le (W : ℕ) (hW : 1 ≤ W) (e : CD) (nI : ℕ) (h : (pay e).length ≤ W) :
    levCost W e nI ≤ 110 * (W + 1) ^ 3 + (W + 1) * nI := by
  have hl : (pay e).length = (natWord e.1).length + (natWord e.2.length).length + (e.2.flatMap exactWord).length := by
    rw [pay_eq]
    simp only [List.length_append]
  have hm : e.2.length ≤ W := by
    have := len_le_flatMap_exactWord e.2
    omega
  have hmin : min e.2.length 1 * ((2 * W + 3) + 1 + ((e.1 + 3) * (10 * W + 30) + 1 + nI)) ≤
      (10 * W * W + 64 * W + 99) + nI := by
    rcases Nat.eq_zero_or_pos e.2.length with h0 | h0
    · rw [h0]
      simp
    · rw [Nat.min_eq_right (by omega), Nat.one_mul]
      have ha := arity_le e 0 h0
      have : (e.1 + 3) * (10 * W + 30) ≤ (W + 3) * (10 * W + 30) := Nat.mul_le_mul_right _ (by omega)
      nlinarith
  unfold levCost
  have hm1 : e.2.length + 1 ≤ W + 1 := by omega
  have step : (e.2.length + 1) * ((2 * W + 3) + min e.2.length 1 * ((2 * W + 3) + 1 + ((e.1 + 3) * (10 * W + 30) +
      1 + nI)) + 2) ≤ (W + 1) * ((10 * W * W + 68 * W + 104) + nI) :=
    Nat.mul_le_mul hm1 (by omega)
  have e3 : (W + 1) * ((10 * W * W + 68 * W + 104) + nI) = (W + 1) * (10 * W * W + 68 * W + 104) + (W + 1) * nI := by
    ring
  have ea : (W + 1) * (10 * W * W + 68 * W + 104) = 10 * (W * W * W) + 78 * (W * W) + 172 * W + 104 := by ring
  have eb : 110 * (W + 1) ^ 3 = 110 * (W * W * W) + 330 * (W * W) + 330 * W + 110 := by ring
  omega

theorem loopsCost_le (W : ℕ) (hW : 1 ≤ W) (d : Fin 4 → CD) (h : ∀ c, (pay (d c)).length ≤ W) :
    loopsCost W d ≤ 2000 * (W + 1) ^ 6 := by
  unfold loopsCost
  have hB : nB W ≤ 900 * (W + 1) ^ 2 := by
    unfold nB
    have e : 900 * (W + 1) ^ 2 = 900 * (W * W) + 1800 * W + 900 := by ring
    have e2 : 130 * W * W = 130 * (W * W) := by ring
    omega
  have h3 := levCost_le W hW (d 3) (nB W) (h 3)
  have h2 := levCost_le W hW (d 2) (levCost W (d 3) (nB W)) (h 2)
  have h1 := levCost_le W hW (d 1) (levCost W (d 2) (levCost W (d 3) (nB W))) (h 1)
  have h0 := levCost_le W hW (d 0) (levCost W (d 1) (levCost W (d 2) (levCost W (d 3) (nB W)))) (h 0)
  have p1 : 1 ≤ W + 1 := by omega
  have k3 : levCost W (d 3) (nB W) ≤ 1010 * (W + 1) ^ 3 := by
    have : (W + 1) * nB W ≤ (W + 1) * (900 * (W + 1) ^ 2) := Nat.mul_le_mul_left _ hB
    have e : (W + 1) * (900 * (W + 1) ^ 2) = 900 * (W + 1) ^ 3 := by ring
    omega
  have k2 : levCost W (d 2) (levCost W (d 3) (nB W)) ≤ 1120 * (W + 1) ^ 4 := by
    have : (W + 1) * levCost W (d 3) (nB W) ≤ (W + 1) * (1010 * (W + 1) ^ 3) := Nat.mul_le_mul_left _ k3
    have e : (W + 1) * (1010 * (W + 1) ^ 3) = 1010 * (W + 1) ^ 4 := by ring
    have q : (W + 1) ^ 3 ≤ (W + 1) ^ 4 := Nat.pow_le_pow_right p1 (by norm_num)
    omega
  have k1 : levCost W (d 1) (levCost W (d 2) (levCost W (d 3) (nB W))) ≤ 1230 * (W + 1) ^ 5 := by
    have : (W + 1) * levCost W (d 2) (levCost W (d 3) (nB W)) ≤ (W + 1) * (1120 * (W + 1) ^ 4) :=
      Nat.mul_le_mul_left _ k2
    have e : (W + 1) * (1120 * (W + 1) ^ 4) = 1120 * (W + 1) ^ 5 := by ring
    have q : (W + 1) ^ 3 ≤ (W + 1) ^ 5 := Nat.pow_le_pow_right p1 (by norm_num)
    omega
  have : (W + 1) * levCost W (d 1) (levCost W (d 2) (levCost W (d 3) (nB W))) ≤ (W + 1) * (1230 * (W + 1) ^ 5) :=
    Nat.mul_le_mul_left _ k1
  have e : (W + 1) * (1230 * (W + 1) ^ 5) = 1230 * (W + 1) ^ 6 := by ring
  have q : (W + 1) ^ 3 ≤ (W + 1) ^ 6 := Nat.pow_le_pow_right p1 (by norm_num)
  omega

end Bounds

end
end NearCubicWires.PacketsMeta

