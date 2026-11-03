import Proof.Packets.PacketsMetaCutoffBounds
import Proof.Packets.PacketsTouch
import Proof.Rows.RowsInitCount

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.PacketsMeta.CutoffMath
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open PCJd4d1d9d7d1fa4313_Production
noncomputable section

namespace StageRun
open Lev Setup Tail Prog Spec Bounds

/-! ## From the program's `LRuns` to PG's `Step` -/

theorem init_tr (W : ℕ) (nw tw : List Bool) :
    ∀ i : Fin (3 + 57), TR W (σ0 nw tw i) 0
      (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame tw) (RepairOrdinary.frame nw) i) := by
  intro i
  fin_cases i <;>
    simp [TR, σ0, NearCubicWires.PacketsGlue.RequestMeta.scanIn2, rdF, readTapeBit, blank, Ruler.rb] <;> omega

theorem step_of_lruns {s : ℕ} (P : Machine 60 s) (n W : ℕ) (nw tw : List Bool) (v : ℕ)
    (h : LRuns W P n (σ0 nw tw) (outOnly v)) :
    ∃ (H1 : Fin (3 + 57) → ℕ) (A1 : Fin (3 + 57) → List Bool),
      Step P n (fun _ => 0)
        (NearCubicWires.PacketsGlue.RequestMeta.scanIn2 57 (RepairOrdinary.frame tw) (RepairOrdinary.frame nw)) H1 A1 ∧
      A1 ⟨1, by omega⟩ = List.replicate v true := by
  obtain ⟨H1, A1, hs, hA⟩ := h (fun _ => 0) _ (init_tr W nw tw)
  refine ⟨H1, A1, hs, ?_⟩
  have h1 := hA 1
  simp only [outOnly, Function.update_self, TR] at h1
  exact h1.2

/-! ## Width facts for a THR request -/

section Thr
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- The rest of the THR `nativeWord` after its four leading numbers. -/
def restOf : List Bool :=
  natWord r.circuits.length ++ r.circuits.flatMap (fun c => RepairOrdinary.frame (thrWord c))

theorem nw_eq (four : r.circuits.length ≤ 4) (L target : ℕ) : Request.nativeWord (.thr r four L target) =
    natWord 1 ++ natWord r.q ++ natWord L ++ natWord target ++ restOf r := by
  simp only [Request.nativeWord, restOf, List.append_assoc]

theorem word_le_nw (four : r.circuits.length ≤ 4) (L target : ℕ) (x : ℕ) (hx : x = 1 ∨ x = r.q ∨ x = L ∨ x = target) :
    (natWord x).length ≤ (Request.nativeWord (.thr r four L target)).length := by
  rw [nw_eq r four L target]
  simp only [List.length_append]
  rcases hx with h | h | h | h <;> subst h <;> omega

theorem nw_ge (four : r.circuits.length ≤ 4) (L target : ℕ) : 3 ≤ (Request.nativeWord (.thr r four L target)).length := by
  have h := word_le_nw r four L target 1 (Or.inl rfl)
  have e := ReadNat.natWord_length 1
  have e1 : natBitLength 1 = 1 := by simp [natBitLength]
  omega

theorem tab_len (four : r.circuits.length ≤ 4) (L target : ℕ) (i : Fin 4) : (tab (dOf (dsOf a r) i)).length ≤ 2 ^ (twOf (dsOf a r)).length := by
  rw [tab_eq a r four, tw_eq a r four L target]
  have h1 := T_length_le a r four L target i.val
  have h2 := Nat.lt_two_pow_self (n := (Request.topWord a (.thr r four L target)).length)
  omega

theorem rec_bound (four : r.circuits.length ≤ 4) (L target : ℕ) (i : Fin 4) (x : Rec) (hx : x ∈ tab (dOf (dsOf a r) i)) :
    recMag x < 2 ^ (twOf (dsOf a r)).length := by
  rw [tab_eq a r four] at hx
  rw [tw_eq a r four L target]
  exact rec_lt a r four L target i.val x hx

theorem Cv_le (four : r.circuits.length ≤ 4) (L target : ℕ) : Cv (dsOf a r) ≤ 2 ^ (4 * (twOf (dsOf a r)).length) := by
  have h0 := tab_len a r four L target 0
  have h1 := tab_len a r four L target 1
  have h2 := tab_len a r four L target 2
  have h3 := tab_len a r four L target 3
  unfold Cv
  have e : 2 ^ (4 * (twOf (dsOf a r)).length) = 2 ^ (twOf (dsOf a r)).length * (2 ^ (twOf (dsOf a r)).length *
      (2 ^ (twOf (dsOf a r)).length * (2 ^ (twOf (dsOf a r)).length * 1))) := by ring
  rw [e]
  exact Nat.mul_le_mul h0 (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 (le_refl 1))))

theorem Fv_le (four : r.circuits.length ≤ 4) (L target : ℕ) : Fv (dsOf a r) ≤ 2 ^ (8 * (twOf (dsOf a r)).length + 10) := by
  set R := (twOf (dsOf a r)).length with hR
  have hsel : ∀ x0 ∈ tab (dOf (dsOf a r) 0), ∀ x1 ∈ tab (dOf (dsOf a r) 1), ∀ x2 ∈ tab (dOf (dsOf a r) 2),
      ∀ x3 ∈ tab (dOf (dsOf a r) 3), selMag [x0, x1, x2, x3] ≤ 2 ^ (4 * R + 10) := by
    intro x0 h0 x1 h1 x2 h2 x3 h3
    exact (selMag_lt R x0 x1 x2 x3 (rec_bound a r four L target 0 x0 h0) (rec_bound a r four L target 1 x1 h1)
      (rec_bound a r four L target 2 x2 h2) (rec_bound a r four L target 3 x3 h3)).le
  have hn := nestedSum_le _ _ _ _ selMag _ hsel
  have h0 := tab_len a r four L target 0
  have h1 := tab_len a r four L target 1
  have h2 := tab_len a r four L target 2
  have h3 := tab_len a r four L target 3
  have hm : (tab (dOf (dsOf a r) 0)).length * ((tab (dOf (dsOf a r) 1)).length * ((tab (dOf (dsOf a r) 2)).length *
      ((tab (dOf (dsOf a r) 3)).length * 2 ^ (4 * R + 10)))) ≤
      2 ^ R * (2 ^ R * (2 ^ R * (2 ^ R * 2 ^ (4 * R + 10)))) :=
    Nat.mul_le_mul h0 (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 (Nat.mul_le_mul h3 (le_refl _))))
  have e : 2 ^ R * (2 ^ R * (2 ^ R * (2 ^ R * 2 ^ (4 * R + 10)))) = 2 ^ (8 * R + 10) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    ring_nf
  unfold Fv
  omega

/-- The register width of a THR request. -/
def thrW (four : r.circuits.length ≤ 4) (L target : ℕ) : ℕ :=
  32 * ((Request.nativeWord (.thr r four L target)).length + (twOf (dsOf a r)).length)

/-- **Every width hypothesis of `prog_thr` and `tail_run`.** -/
theorem thr_width (four : r.circuits.length ≤ 4) (L target : ℕ) :
    2 ≤ thrW a r four L target ∧ 5 ≤ thrW a r four L target ∧ natBitLength r.q ≤ thrW a r four L target ∧
      natBitLength L ≤ thrW a r four L target ∧ natBitLength target ≤ thrW a r four L target ∧
      4 * (twOf (dsOf a r)).length + 11 ≤ thrW a r four L target ∧
      (∀ j, Fits (thrW a r four L target) (dOf (dsOf a r) j)) ∧ Fv (dsOf a r) < 2 ^ thrW a r four L target ∧
      Cv (dsOf a r) < 2 ^ thrW a r four L target ∧ 2 * (Fv (dsOf a r) + 1) ≤ 2 ^ thrW a r four L target ∧
      target + 1 < 2 ^ thrW a r four L target ∧
      cutOf (Fv (dsOf a r)) (Cv (dsOf a r)) target < 2 ^ thrW a r four L target := by
  have hN0 := nw_ge r four L target
  have hbl : ∀ x, (x = 1 ∨ x = r.q ∨ x = L ∨ x = target) →
      natBitLength x ≤ (Request.nativeWord (.thr r four L target)).length := by
    intro x hx
    have := word_le_nw r four L target x hx
    have := natBitLength_le x
    omega
  have hF := Fv_le a r four L target
  have hC := Cv_le a r four L target
  have hpad : ∀ j : Fin 4, (pay (dOf (dsOf a r) j)).length ≤ (twOf (dsOf a r)).length + 10 := by
    intro j
    by_cases hj : j.val < (dsOf a r).length
    · rw [dOf_lt _ j hj]
      have := pay_le_tw (dsOf a r) j.val hj
      omega
    · rw [dOf_ge _ j (by omega), pay_pad_len]
      omega
  have hT0 := ReadNat.lt_natBitLength target
  have hbT := hbl target (Or.inr (Or.inr (Or.inr rfl)))
  unfold thrW
  set N := (Request.nativeWord (.thr r four L target)).length with hNdef
  set R := (twOf (dsOf a r)).length with hRdef
  have hpw : ∀ m k, m ≤ k → 2 ^ m ≤ 2 ^ k := fun m k h => Nat.pow_le_pow_right (by norm_num) h
  have hpl : ∀ m k, m < k → 2 ^ m < 2 ^ k := fun m k h => Nat.pow_lt_pow_right (by norm_num) h
  have hT : target + 1 ≤ 2 ^ N := by
    have h2 := hpw _ _ hbT
    omega
  have hF1 : Fv (dsOf a r) + 1 ≤ 2 ^ (8 * R + 11) := by
    have e : 2 ^ (8 * R + 11) = 2 * 2 ^ (8 * R + 10) := by rw [pow_succ]; ring
    have := Nat.one_le_two_pow (n := 8 * R + 10)
    omega
  refine ⟨by omega, by omega, (hbl _ (Or.inr (Or.inl rfl))).trans (by omega),
    (hbl _ (Or.inr (Or.inr (Or.inl rfl)))).trans (by omega), hbT.trans (by omega),
    by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    apply fits_of_len
    have := hpad j
    omega
  · exact lt_of_le_of_lt hF (hpl _ _ (by omega))
  · exact lt_of_le_of_lt hC (hpl _ _ (by omega))
  · have e : 2 ^ (8 * R + 12) = 2 * 2 ^ (8 * R + 11) := by rw [pow_succ]; ring
    have := hpw (8 * R + 12) (32 * (N + R)) (by omega)
    omega
  · exact lt_of_le_of_lt hT (hpl _ _ (by omega))
  · -- the cutoff
    have he : Nat.clog 2 (Fv (dsOf a r) + 1) ≤ 8 * R + 11 := Nat.clog_le_of_le_pow hF1
    have hR2 : R + 1 ≤ 2 ^ R := Nat.lt_two_pow_self
    have he1 : Nat.clog 2 (Fv (dsOf a r) + 1) + 1 ≤ 2 ^ (R + 4) := by
      have e : 2 ^ (R + 4) = 16 * 2 ^ R := by rw [pow_add]; ring
      omega
    have hd1 : 2 * Cv (dsOf a r) * (target + 1) + 1 ≤ 2 ^ (4 * R + N + 2) := by
      have h1 : Cv (dsOf a r) * (target + 1) ≤ 2 ^ (4 * R) * 2 ^ N := Nat.mul_le_mul hC hT
      have e : 2 ^ (4 * R + N + 2) = 4 * (2 ^ (4 * R) * 2 ^ N) := by rw [pow_add, pow_add]; ring
      have hp : 1 ≤ 2 ^ (4 * R) * 2 ^ N := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have e2 : 2 * Cv (dsOf a r) * (target + 1) = 2 * (Cv (dsOf a r) * (target + 1)) := by ring
      omega
    have hS : 6 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * (2 * Cv (dsOf a r) * (target + 1) + 1) ≤
        2 ^ (5 * R + N + 9) := by
      have h1 := Nat.mul_le_mul he1 hd1
      have e : 2 ^ (5 * R + N + 9) = 8 * (2 ^ (R + 4) * 2 ^ (4 * R + N + 2)) := by
        rw [← pow_add, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
        ring_nf
      have e2 : 6 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * (2 * Cv (dsOf a r) * (target + 1) + 1) =
          6 * ((Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * (2 * Cv (dsOf a r) * (target + 1) + 1)) := by ring
      omega
    have hM : max 24 (6 * (Nat.clog 2 (Fv (dsOf a r) + 1) + 1) * (2 * Cv (dsOf a r) * (target + 1) + 1)) ≤
        2 ^ (5 * R + N + 9) := by
      refine max_le ?_ hS
      have := hpw 9 (5 * R + N + 9) (by omega)
      have e : (2 : ℕ) ^ 9 = 512 := by norm_num
      omega
    have hsq : cutOf (Fv (dsOf a r)) (Cv (dsOf a r)) target ≤ 2 ^ (2 * (5 * R + N + 9)) := by
      unfold cutOf canonicalPrimeCutoff canonicalPrimeScale
      rw [pow_mul']
      exact Nat.pow_le_pow_left hM 2
    exact lt_of_le_of_lt hsq (hpl _ _ (by omega))

end Thr

end StageRun

end
end NearCubicWires.PacketsMeta

