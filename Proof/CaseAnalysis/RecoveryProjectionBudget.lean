import Proof.CaseAnalysis.RecoveryProjectionRun

/-! The actual original cold projector has a fixed polynomial cost in the
same paid W and B. Its normalized query stream is retained without traversal;
no identity between query-entry count and encoded byte length is assumed.
Smoke: projection-cold-budget-20260913-1, 154 finite points, then Lean proof. -/
namespace NearCubicWires.RepairOrdinary.RecoveryProjectionCold
open LocalBitMultitape RepairSource RecoveryRootRound SourceInterfaces
open VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem dimension_bound (n W : ℕ) (hn : n≤W) :
    RecoveryProjectionDimension.budget n.bits≤35*(W+1)^2 := by
  have hbits:=RecoveryProjectionRows.bits_le_value n
  have hprod : (n+1)*(n.bits.length+1)≤(W+1)^2 := by
    calc
      _≤(W+1)*(W+1) := Nat.mul_le_mul (by omega) (by omega)
      _=(W+1)^2 := by ring
  have hu : 1≤(W+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hw : W+1≤(W+1)^2 := Nat.le_self_pow (by decide) _
  simp only [RecoveryProjectionDimension.budget,Unary.budget,DimensionProducer.bits_value]
  nlinarith

private theorem fourth_cost (n W : ℕ) (hn : n≤W) :
    DimensionPower.cost 1048576 (n+1) 4≤1000000000*(W+1)^5 := by
  have h:=DimensionPower.cost_bound 4 1048576 (n+1) 4 (by decide)
  norm_num only at h
  have hp : ((n+1)+1)^5≤32*(W+1)^5 := by
    calc
      _≤(2*(W+1))^5 := Nat.pow_le_pow_left (by omega) _
      _=32*(W+1)^5 := by ring
  have hu : 1≤(W+1)^5 := Nat.one_le_pow _ _ (by omega)
  nlinarith

private theorem second_cost (R Q W : ℕ) (hr : R≤W) (hq : Q≤W) :
    DimensionPower.cost 536870912 (R+Q+1) 2≤60000000000*(W+1)^3 := by
  have h:=DimensionPower.cost_bound 2 536870912 (R+Q+1) 2 (by decide)
  norm_num only at h
  have hp : ((R+Q+1)+1)^3≤8*(W+1)^3 := by
    calc
      _≤(2*(W+1))^3 := Nat.pow_le_pow_left (by omega) _
      _=8*(W+1)^3 := by ring
  have hu : 1≤(W+1)^3 := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem scalar_bound (W R Q : ℕ) (hr : R≤W) (hq : Q≤W) (htwo : 2^R≤W) :
    scalarBudget R Q≤1000000000000*(W+1)^5 := by
  have hdr:=dimension_bound R W hr
  have hdq:=dimension_bound Q W hq
  have hp4:=fourth_cost R W hr
  have hp2:=second_cost R Q W hr hq
  have h25 : (W+1)^2≤(W+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have h35 : (W+1)^3≤(W+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have hw : W+1≤(W+1)^5 := Nat.le_self_pow (by decide) _
  have hprod : 2^R*(R+1)≤(W+1)^2 := by
    calc
      _≤(W+1)*(W+1) := Nat.mul_le_mul (by omega) (by omega)
      _=(W+1)^2 := by ring
  have hminus : 2^R-1≤W := (Nat.sub_le _ _).trans htwo
  simp only [scalarBudget,RecoveryPCPFormulaResumeColdScalars.budget,
    RecoveryPCPFormulaResumeCapacity.budget,RecoveryProjectionCapacity.budget,
    PCPSerializerCapacity.Power.budget,RecoveryPCPFormulaResumeCountPair.budget,
    RecoveryPCPFormulaResumeCountCold.budget,RecoveryPCPFormulaResumeCount.budget,
    DimensionProducer.bits_value]
  nlinarith

theorem budget_bound (W R Q : ℕ) (hr : R≤W) (hq : Q≤W) (htwo : 2^R≤W) :
    budget R Q (33*10000000000*(W+1)^6+64)≤10000000000000*(W+1)^6 := by
  have hs:=(scalar_bound W R Q hr hq htwo).trans
    (Nat.mul_le_mul_left 1000000000000 (Nat.pow_le_pow_right (by omega) (by decide : 5≤6)))
  have hc : RecoveryProjectionRows.capacity R≤1048576*(W+1)^6 := by
    apply Nat.mul_le_mul_left 1048576
    exact (Nat.pow_le_pow_left (by omega : R+1≤W+1) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hw : W+1≤(W+1)^6 := Nat.le_self_pow (by decide) _
  simp only [budget,bankBudget,Counter.budget]
  omega

end NearCubicWires.RepairOrdinary.RecoveryProjectionCold
