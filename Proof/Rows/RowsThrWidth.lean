import Proof.Rows.RowsCellInput
import Proof.Rows.RowsMaskGeneric
import Proof.Rows.RowsSymVerdict
import Proof.Rows.RowsSymBounds
import Proof.CaseAnalysis.RawRowsThresholdSize
import Proof.Supplier.RowCachedEquationMeaning
import Proof.Supplier.RowCachedCoordinateBounds

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.CloseoutRawRows
open NearCubicWires.ThresholdAlignedEnvelope
open scoped BigOperators
noncomputable section

variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

/-- `T := |input|` of the THR request. -/
abbrev T : Nat := ((PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target).input a).length

theorem topWord_le :
    ((PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target).topWord a).length ≤ T a r four L target := by
  simp only [T, PCJd4d1d9d7d1fa4313_Production.Request.input, List.length_append, frame_length]
  omega

theorem children_le (c : NormalizedThresholdThresholdCircuit r.q) (hc : c ∈ r.circuits) :
    (exactListWord (ThresholdRows.children a c)).length ≤ T a r four L target := by
  refine le_trans ?_ (topWord_le a r four L target)
  simp only [PCJd4d1d9d7d1fa4313_Production.Request.topWord, List.length_flatMap]
  have hmem : (frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))).length ∈
      r.circuits.map (fun c => (frame (natWord c.top.support.card ++
        exactListWord (ThresholdRows.children a c))).length) := List.mem_map.mpr ⟨c, hc, rfl⟩
  have h1 := List.le_sum_of_mem hmem
  simp only [frame_length, List.length_append] at h1 ⊢
  omega

theorem childMagnitude_lt (c : NormalizedThresholdThresholdCircuit r.q) (hc : c ∈ r.circuits)
    (g : ExactThresholdGate c.top.support.card) (hg : g ∈ ThresholdRows.children a c) :
    childMagnitude g < 2^(T a r four L target) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have h1 := RowCachedEquation.equation_magnitude ((ThresholdRows.children a c)[i])
  have h2 := RowCachedCoordinateBounds.child_bytes (ThresholdRows.children a c) i hi
  have h3 := children_le a r four L target c hc
  have heq : equationMagnitudeBound (RowCachedEquation.equation ((ThresholdRows.children a c)[i])) =
      childMagnitude ((ThresholdRows.children a c)[i]) := rfl
  rw [heq] at h1
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (h2.trans h3))

theorem children_length_le (c : NormalizedThresholdThresholdCircuit r.q) (hc : c ∈ r.circuits) :
    (ThresholdRows.children a c).length ≤ T a r four L target := by
  refine le_trans ?_ (children_le a r four L target c hc)
  simp only [exactListWord, List.length_append, DecompositionSource.natWord_length]
  have : (ThresholdRows.children a c).length ≤ ((ThresholdRows.children a c).flatMap exactWord).length := by
    rw [List.length_flatMap]
    calc (ThresholdRows.children a c).length = ((ThresholdRows.children a c).map (fun _ => 1)).sum := by simp
      _ ≤ ((ThresholdRows.children a c).map (fun g => (exactWord g).length)).sum := by
        apply List.sum_le_sum
        intro g _
        simp only [exactWord, List.length_append, DecompositionSource.intWord_length]
        omega
  omega

/-! ## The radix -/

theorem radix_lt (sel : ThresholdRows.Selection a r) :
    PCJ45bee56da9f34d5a_StreamPair.radix a r four sel < 2^(T a r four L target+2) := by
  unfold PCJ45bee56da9f34d5a_StreamPair.radix PCJ45bee56da9f34d5a_ThresholdData.base
  have hv : ∀ v ∈ (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel).values, v+1 ≤ 2^(T a r four L target) := by
    intro v hv
    simp only [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.values, PCJ45bee56da9f34d5a_ThresholdData.data,
      List.mem_ofFn] at hv
    obtain ⟨j, rfl⟩ := hv
    exact childMagnitude_lt a r four L target _ (List.get_mem _ _) _ (List.get_mem _ _)
  have hlen : (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel).values.length ≤ 4 := by
    rw [PCJ45bee56da9f34d5a_FourfoldBaseData.values_length]; exact four
  have hv' : ∀ v ∈ (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel).values, v ≤ 2^(T a r four L target)-1 :=
    fun v hv0 => by have := hv v hv0; omega
  have hs := List.sum_le_card_nsmul (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel).values
    (2^(T a r four L target)-1) hv'
  simp only [smul_eq_mul] at hs
  have hs4 : (PCJ45bee56da9f34d5a_ThresholdData.data a r four sel).values.length*(2^(T a r four L target)-1) ≤
      4*(2^(T a r four L target)-1) := Nat.mul_le_mul_right _ hlen
  have hp : 1 ≤ 2^(T a r four L target) := Nat.one_le_two_pow
  have p2 : 2^(T a r four L target+2) = 4*2^(T a r four L target) := by rw [pow_add]; norm_num; ring
  rw [p2]
  omega

/-! ## The prime window -/

theorem clog_succ_le (total count K M : ℕ) (hcount : count ≤ 2 ^ K) (htotal : total ≤ count * 2 ^ M) :
    Nat.clog 2 (total + 1) ≤ K + M + 1 := by
  have h1 : total ≤ 2 ^ K * 2 ^ M := htotal.trans (Nat.mul_le_mul_right _ hcount)
  have hpos : (1 : ℕ) ≤ 2 ^ K * 2 ^ M := by rw [← pow_add]; exact Nat.one_le_two_pow
  have hrw : (2 : ℕ) ^ (K + M + 1) = 2 ^ K * 2 ^ M + 2 ^ K * 2 ^ M := by rw [pow_succ, pow_add]; ring
  have h2 : total + 1 ≤ 2 ^ (K + M + 1) := by rw [hrw]; exact Nat.add_le_add h1 hpos
  calc Nat.clog 2 (total + 1) ≤ Nat.clog 2 (2 ^ (K + M + 1)) := Nat.clog_mono_right 2 h2
    _ = K + M + 1 := Nat.clog_pow 2 _ (by norm_num)

theorem selection_card_le :
    Fintype.card (ThresholdRows.Selection a r) ≤ 2^(4*T a r four L target) := by
  classical
  rw [show Fintype.card (ThresholdRows.Selection a r) =
      ∏ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length by
    simp [ThresholdRows.Selection, Fintype.card_pi]]
  calc (∏ i : Fin r.circuits.length, (ThresholdRows.children a (r.circuits.get i)).length)
      ≤ ∏ _i : Fin r.circuits.length, 2^(T a r four L target) := by
        apply Finset.prod_le_prod' (fun i _ => ?_)
        have h := children_length_le a r four L target (r.circuits.get i) (List.get_mem r.circuits i)
        have := Nat.lt_two_pow_self (n := T a r four L target)
        omega
    _ = (2^(T a r four L target))^r.circuits.length := by simp
    _ ≤ (2^(T a r four L target))^4 := Nat.pow_le_pow_right Nat.one_le_two_pow four
    _ = 2^(4*T a r four L target) := by rw [← pow_mul, Nat.mul_comm]

theorem equation_magnitude_lt (sel : ThresholdRows.Selection a r) :
    equationMagnitudeBound (ThresholdRows.equation a r sel) < 2^(4*(T a r four L target+3)) := by
  apply canonical_stack_magnitude (ThresholdRows.equations a r sel) (T a r four L target)
  · simpa only [ThresholdRows.equations, List.length_ofFn] using four
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    rw [thresholdChildEquation_magnitudeBound]
    exact childMagnitude_lt a r four L target _ (List.get_mem _ _) _ (List.get_mem _ _)

theorem familyExponent_le :
    familyMagnitudeExponent (ThresholdRows.equation a r) ≤
      4*T a r four L target+4*(T a r four L target+3)+1 := by
  classical
  have hsum : familyMagnitudeBound (ThresholdRows.equation a r) ≤
      Fintype.card (ThresholdRows.Selection a r) * 2^(4*(T a r four L target+3)) := by
    have hle := Finset.sum_le_card_nsmul (Finset.univ : Finset (ThresholdRows.Selection a r))
      (fun sel => equationMagnitudeBound (ThresholdRows.equation a r sel))
      (2^(4*(T a r four L target+3))) (fun sel _ => (equation_magnitude_lt a r four L target sel).le)
    simpa [familyMagnitudeBound, Finset.card_univ, smul_eq_mul] using hle
  exact clog_succ_le _ _ _ _ (selection_card_le a r four L target) hsum

theorem target_lt : target < 2^(T a r four L target) := by
  have hn := SymBounds.native_le_input a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target)
  have hh : 2*natBitLength target+1 ≤
      (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target).nativeWord.length := by
    simp only [PCJd4d1d9d7d1fa4313_Production.Request.nativeWord, List.length_append,
      DecompositionSource.natWord_length]
    omega
  have hb : target < 2^(natBitLength target) := by
    unfold natBitLength
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two target
  have hT : T a r four L target = ((PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target).input a).length := rfl
  exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by rw [hT]; omega))

theorem cutoff_le :
    CloseoutFinalC10ThresholdRows.primeCutoff a r target ≤ 2^(12*T a r four L target+18) := by
  have hE := familyExponent_le a r four L target
  have hc := selection_card_le a r four L target
  have htg := target_lt a r four L target
  generalize T a r four L target = t at hE hc htg ⊢
  unfold CloseoutFinalC10ThresholdRows.primeCutoff canonicalPrimeCutoff canonicalPrimeScale
    CloseoutFinalC10ThresholdRows.primeDenominator reciprocalUnionDenominator
  generalize familyMagnitudeExponent (ThresholdRows.equation a r) = E at hE ⊢
  generalize Fintype.card (ThresholdRows.Selection a r) = card at hc ⊢
  have hpt : t+1 ≤ 2^t := Nat.lt_two_pow_self
  have p7 : 2^(t+7) = 128*2^t := by rw [pow_add]; norm_num; ring
  have h1 : 6*(E+1) ≤ 2^(t+7) := by rw [p7]; omega
  have hct : card*(target+1) ≤ 2^(4*t)*2^t := Nat.mul_le_mul hc (by omega)
  have p52 : 2^(5*t+2) = 4*(2^(4*t)*2^t) := by
    rw [show 5*t+2 = 2+(4*t+t) by ring, pow_add, pow_add]; norm_num
  have hX : 1 ≤ 2^(4*t)*2^t := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2 : 2*card*(target+1)+1 ≤ 2^(5*t+2) := by
    rw [p52, show 2*card*(target+1) = 2*(card*(target+1)) by ring]; omega
  have h3 : 6*(E+1)*(2*card*(target+1)+1) ≤ 2^(6*t+9) := by
    rw [show 6*t+9 = (t+7)+(5*t+2) by ring, pow_add]; exact Nat.mul_le_mul h1 h2
  have h24 : 24 ≤ 2^(6*t+9) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) (show 9 ≤ 6*t+9 by omega))
  calc (max 24 (6*(E+1)*(2*card*(target+1)+1)))^2 ≤ (2^(6*t+9))^2 := Nat.pow_le_pow_left (max_le h24 h3) 2
    _ = 2^(12*t+18) := by rw [← pow_mul]; congr 1; ring

/-- **THR widths**: every prime of the row's window and the row's radix fit `w := 12|input|+19` bits. -/
theorem prime_fit (cutoff : Nat) (hcut : cutoff = CloseoutFinalC10ThresholdRows.primeCutoff a r target)
    (p : PrimeIndex cutoff) : 2*p.val ≤ 2^(12*T a r four L target+19) := by
  have hp := (mem_primesUpTo.mp p.property).2
  subst hcut
  have := cutoff_le a r four L target
  rw [pow_succ]
  omega

theorem base_fit (sel : ThresholdRows.Selection a r) :
    PCJ45bee56da9f34d5a_StreamPair.radix a r four sel < 2^(12*T a r four L target+19) :=
  lt_of_lt_of_le (radix_lt a r four L target sel) (Nat.pow_le_pow_right (by decide) (by omega))

end
end RowsConstruction.ThrWidth
