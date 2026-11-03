import Proof.CaseAnalysis.RawRowsChildren

/-! The actual mode row and corrected child source supply the common digit
width. Cut generation is separately added and paid by the strict paper load. -/
namespace NearCubicWires.RepairSource.CloseoutRawRows
open CanonicalFourfoldRowProgram SupplierPipeline SupplierEstimator SupplierWalkBridge
open RepairRepresentation RepairOrdinary
open CloseoutRowsRawLogShape CloseoutRowsCacheInput
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem raw_cuts_bound {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (K w : ℕ) (bank : List (List (List Bool)))
    (hbank : bank.length ≤ 2^K) (hw : ∀ rows∈bank,rows.length ≤ 2^w) (hpos : 1 ≤ w) :
    (bank.flatMap (CloseoutRowsSharedDigits.cuts gs (K+1) w)).length ≤
      2^(2*(K+w*(K+2))) := by
  have hp := CloseoutRowsSharedDigits.batch_perm gs (K+1) w bank hw
  rw [hp.length_eq,RowPowerBinLift.batch_length]
  have hm : ∀ ms∈family gs bank,ms.length ≤ 2^w := by
    intro ms hms
    obtain ⟨rows,hr,rfl⟩ := List.mem_map.mp hms
    simpa only [polynomial,List.length_map] using hw rows hr
  have hb := RowBinLift.batch_length_bound (K+1) (2^w) (family gs bank) hm
  rw [max_eq_right Nat.one_le_two_pow] at hb
  have hfamily : (family gs bank).length ≤ 2^K := by simpa only [family,List.length_map] using hbank
  have hQ : K+1 ≤ 2^(K+1) := Nat.lt_two_pow_self.le
  calc
    _ ≤ 2^K*2^(K+1)*(2^w)^(K+1) :=
      hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hfamily hQ))
    _ = 2^(K+(K+1)+w*(K+1)) := by rw [←pow_add,←pow_mul,←pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      nlinarith

theorem raw_cuts_gate {l r : ℕ} (gs : List (ExactThresholdGate (l+r)))
    (K w s : ℕ) (bank : List (List (List Bool)))
    (hbank : bank.length ≤ 2^K) (hw : ∀ rows∈bank,rows.length ≤ 2^w) (hpos : 1 ≤ w)
    (hload : 200*(K+w*(K+2)) ≤ s) :
    (bank.flatMap (CloseoutRowsSharedDigits.cuts gs (K+1) w)).length^100 ≤ 2^s := by
  calc
    _ ≤ (2^(2*(K+w*(K+2))))^100 := Nat.pow_le_pow_left (raw_cuts_bound gs K w bank hbank hw hpos) 100
    _ = 2^(200*(K+w*(K+2))) := by rw [←pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hload

end
end NearCubicWires.RepairSource.CloseoutRawRows
