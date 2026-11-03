import W3.Front.ColdRun
import Proof.CaseAnalysis.CloseoutWitnessOracleBudget
import Proof.PCP.ProjectionDimensionPolynomialBounds
import Proof.CaseAnalysis.WitnessBudgetFast
import Proof.CaseAnalysis.CaseTwoWholeBudget
import W3.Proof.CaseAnalysis.WitnessSourcePolicyBudget
import Outer.Size
import W3.Joins.Cases

/-!
# The cold front end, part 9: the cost class (`N^{d_chk} · q^{O(1)}`, `d_chk = 2`)

Paper: "the work before the PCPP call is N^{d_chk} + q^{O(1)}" and Fact C.2's call on `H_B` (size
`q^{O(1)}`) is `q^{O(1)}`. `coldU_le`: the cold prefix is at most `(N+1)^2 · Gpre(q)`; `Gpre_poly`: `Gpre` is a
polynomial; `tail_le`/`Gtail_poly`: the source dock + policy at `requestOf` of a capped pair is a polynomial in `q`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.PaddedRunnerBudgetClosure

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-- One field's cost past its linear part. -/
def fieldU (E q : ℕ) : ℕ :=
  20 + 200 * (Lq E q + 1) + 40 * (16 * Lq E q + q + 4) + 20 + 200 * (q + 2) + (34 * q + 7) +
    40000000000000000000000 * (16 * Lq E q + q + 4 + 2) ^ 25 + 10

theorem fieldCost_le (E q n : ℕ) (b : List Bool) (hb : b.length ≤ n / 16) :
    fieldCost b (Lq E q) (16 * Lq E q + q + 4) q ≤ 15 * n + fieldU E q := by
  have hpl : (Codec.prefixBits b (Lq E q)).length = Lq E q := by simp [Codec.prefixBits]
  have ho := CloseoutWitness.Oracle.budget_polynomial (List.replicate (16 * Lq E q + q + 4) true)
    (Codec.prefixBits b (Lq E q)) q.bits (by simp) (by simp [hpl] <;> omega) (by rw [LitDecode.value_bits]; simp <;> omega)
  simp only [List.length_replicate] at ho
  unfold fieldCost truncCost fieldU
  omega

open NearCubicWires.RepairSource.ProjectionNormalization in
/-- The cap step's polynomial majorant. -/
def capB (degree q S : ℕ) : ℕ :=
  2 * (80 * (q + 1) ^ 2 + 1 + 80 * (S + 1) ^ 2) + 4 * S + 4 * q + 29 +
    (DimensionPolynomial.coefficient (CloseoutWitness.OracleCap.degree degree) 1 *
      (q + 2) ^ (2 * CloseoutWitness.OracleCap.degree degree + 2) + 4 * S + 20)

open NearCubicWires.RepairSource.ProjectionNormalization in
theorem capU_le (degree q S : ℕ) : capU degree q S ≤ capB degree q S := by
  have := DimensionPolynomial.budget_bound (CloseoutWitness.OracleCap.degree degree) 1 q
  unfold capU capB; omega

section Pre
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree cstar : ℕ)

/-- **The prefix's `q`-polynomial.** -/
noncomputable def Gpre (q : ℕ) : ℕ :=
  3100 + 4 * (OuterM.widthDonor mw SV).K + 30 * cstar + 100 * (q + 1) + boundCost (E0 degree) q +
    2 * fieldU (E0 degree) q + 2 * capB degree q (16 * Lq (E0 degree) q) +
    F.K * (78 * (q + 16 * Lq (E0 degree) q + 5) ^ 2 + q + 1) ^ F.e

theorem coldU_le (n : ℕ) (raw : List Bool) (h16 : 16 * raw.length ≤ n) :
    coldU mw SV F degree cstar n raw ≤ (n + 1) ^ 2 * Gpre mw SV F degree cstar (Outer.width mw SV n) := by
  obtain ⟨R1, R2, -, -, hl1, hl2⟩ := fields_of_raw n raw h16
  have hl1' : (fld1 raw).length ≤ n / 16 := hl1
  have hl2' : (fld2 raw).length ≤ n / 16 := hl2
  have hd16 : 18 * (4 * (n / 16) + 5) ≤ 5 * n + 90 := by omega
  unfold coldU deepCost prepCost tailU frontU headCost widthCost
  rw [show powCostP n = 1000 * (n + 1) ^ 2 from rfl, pow_one]
  generalize Outer.width mw SV n = q
  have f1 := fieldCost_le (E0 degree) q n (fld1 raw) hl1'
  have f2 := fieldCost_le (E0 degree) q n (fld2 raw) hl2'
  have c1 := capU_le degree q (16 * Lq (E0 degree) q)
  have hP1 : n + 1 ≤ (n + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hY : F.K * (n + 1) ^ 2 * (78 * (q + 16 * Lq (E0 degree) q + 5) ^ 2 + q + 1) ^ F.e =
      (n + 1) ^ 2 * (F.K * (78 * (q + 16 * Lq (E0 degree) q + 5) ^ 2 + q + 1) ^ F.e) := by ring
  rw [hY]
  generalize hP : (n + 1) ^ 2 = P at hP1 ⊢
  have hG : P * Gpre mw SV F degree cstar q = P * 3100 + P * (4 * (OuterM.widthDonor mw SV).K) + P * (30 * cstar) +
      P * (100 * (q + 1)) + P * boundCost (E0 degree) q + P * (2 * fieldU (E0 degree) q) +
      P * (2 * capB degree q (16 * Lq (E0 degree) q)) +
      P * (F.K * (78 * (q + 16 * Lq (E0 degree) q + 5) ^ 2 + q + 1) ^ F.e) := by unfold Gpre; ring
  have l1 : ∀ t : ℕ, t ≤ P * t := fun t => Nat.le_mul_of_pos_left t (by omega)
  have l2 : ∀ t : ℕ, (n + 1) * t ≤ P * t := fun t => Nat.mul_le_mul_right t hP1
  have m1 := l2 (4 * (OuterM.widthDonor mw SV).K)
  have m2 := l2 3100
  have m3 := l1 (30 * cstar)
  have m4 := l1 (100 * (q + 1))
  have m5 := l1 (boundCost (E0 degree) q)
  have m6 := l1 (2 * fieldU (E0 degree) q)
  have m7 := l1 (2 * capB degree q (16 * Lq (E0 degree) q))
  have e1 : (n + 1) * (4 * (OuterM.widthDonor mw SV).K) = 4 * ((OuterM.widthDonor mw SV).K * (n + 1)) := by ring
  have e2 : (n + 1) * 3100 = 3100 * n + 3100 := by ring
  rw [hG]
  omega

end Pre

section PrePoly
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree cstar : ℕ)

open NearCubicWires.RepairOrdinary.CloseoutWitness.BudgetTools in
open NearCubicWires.RepairSource.ProjectionNormalization in
theorem Gpre_poly : SourcePoly (Gpre mw SV F degree cstar) := by
  unfold Gpre boundCost fieldU capB CheckedPCPP.EncSetup.powCost Lq
  fast_budget_poly

end PrePoly

section TailB
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (a : PointwisePCPPAlgorithm) (D copies degree : ℕ) (delta : ℚ)

/-- A majorant of `|H_B|` at a capped pair (`Dat_size_le`, `outC_size_le`, `M0` from `natBitLength_T_le`). -/
noncomputable def SzB (M0 q : ℕ) : ℕ :=
  (Outer.alg mw SV).coefficient * (q ^ (G0 + 2) + (M0 + (k0 + 2) * q) + 1) ^ (Outer.alg mw SV).sizeExp *
    ((q + 1) ^ (E0 degree) + 1) + q + 2

noncomputable def MqB (M0 q : ℕ) : ℕ :=
  PCPPQueryCachedBounds.coefficient a * (SzB mw SV degree M0 q + q + 1) ^ PCPPQueryCachedBounds.degree a

/-- **The tail's `q`-polynomial.** -/
noncomputable def Gtail (M0 q : ℕ) : ℕ :=
  2 * (PCPPSourceCache.coefficient a * (q + SzB mw SV degree M0 q + 5) ^ PCPPSourceCache.totalDegree a) +
    8 * (3 * MqB mw SV a degree M0 q + 3) + 16 + 1 +
    W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.envelope D copies delta (MqB mw SV a degree M0 q)

theorem size_le (M0 : ℕ) (hM0 : ∀ ν, natBitLength (SV.T (Outer.instLength G0 ν)) ≤ M0 + (k0 + 2) * ν) (ν : ℕ)
    (hν : 1 ≤ ν) (B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν)))
    (hp : B.pf.size ≤ oracleSizeBound degree (Outer.width mw SV (2 ^ ν))) :
    (Outer.Dat mw SV ν B).D.size ≤ SzB mw SV degree M0 (Outer.width mw SV (2 ^ ν)) := by
  have hνq := nu_lt_width mw SV ν
  have hD := Outer.Dat_size_le mw SV ν B
  have hO := Outer.outC_size_le mw SV ν hν B.src
  have hI : Outer.instLength G0 ν ≤ Outer.width mw SV (2 ^ ν) ^ (G0 + 2) := Nat.pow_le_pow_left hνq.le _
  have hT := hM0 ν
  have hb : Outer.instLength G0 ν + natBitLength (SV.T (Outer.instLength G0 ν)) + 1 ≤
      Outer.width mw SV (2 ^ ν) ^ (G0 + 2) + (M0 + (k0 + 2) * Outer.width mw SV (2 ^ ν)) + 1 := by
    have : (k0 + 2) * ν ≤ (k0 + 2) * Outer.width mw SV (2 ^ ν) := Nat.mul_le_mul_left _ hνq.le
    omega
  have hO' := hO.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb (Outer.alg mw SV).sizeExp))
  have hs := Amplifier.oracleSizeBound_succ degree (Outer.width mw SV (2 ^ ν))
  have hpf : B.pf.size + 1 ≤ (Outer.width mw SV (2 ^ ν) + 1) ^ (E0 degree) + 1 := by unfold E0; omega
  have hm := Nat.mul_le_mul hO' hpf
  unfold SzB
  omega

theorem tail_le (M0 : ℕ)
    (hM0 : ∀ ν, natBitLength (SV.T (Outer.instLength G0 ν)) ≤ M0 + (k0 + 2) * ν) (ν : ℕ) (hν : 1 ≤ ν)
    (B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν))) (hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν))
    (hp : B.pf.size ≤ oracleSizeBound degree (Outer.width mw SV (2 ^ ν))) :
    CloseoutCaseTwo.RequestSource.budget a (requestOf mw SV a ν B hq) + 1 +
      W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget D copies (requestOf mw SV a ν B hq).arity
        (a.output (requestOf mw SV a ν B hq)).systematicBits (a.output (requestOf mw SV a ν B hq)).auxiliaryBits
        (a.output (requestOf mw SV a ν B hq)).clauseBits delta ≤
      Gtail mw SV a D copies degree delta M0 (Outer.width mw SV (2 ^ ν)) := by
  set r := requestOf mw SV a ν B hq with hr
  have hsz := size_le mw SV degree M0 hM0 ν hν B hp
  have hsz' : r.circuit.size ≤ SzB mw SV degree M0 (Outer.width mw SV (2 ^ ν)) := hsz
  have har : r.arity = Outer.width mw SV (2 ^ ν) := rfl
  obtain ⟨hM1, hR, hin, hsys, haux, hpow, hcb, -⟩ := CloseoutCaseTwo.WholeBudget.components a r
  have hM : CloseoutCaseTwo.WholeBudget.measure a r ≤ MqB mw SV a degree M0 (Outer.width mw SV (2 ^ ν)) := by
    unfold CloseoutCaseTwo.WholeBudget.measure PCPPQueryCachedBounds.capacity MqB
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hrs := CloseoutCaseTwo.WholeBudget.request_source_bound a r
  have htot : PCPPSourceCache.totalBudget a r ≤ PCPPSourceCache.coefficient a *
      (Outer.width mw SV (2 ^ ν) + SzB mw SV degree M0 (Outer.width mw SV (2 ^ ν)) + 5) ^
        PCPPSourceCache.totalDegree a := by
    unfold PCPPSourceCache.totalBudget PCPPRequestRuntime.sourceParameter
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have hpol := W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.budget_le D copies r.arity
    (a.output r).systematicBits (a.output r).auxiliaryBits (a.output r).clauseBits
    (MqB mw SV a degree M0 (Outer.width mw SV (2 ^ ν))) delta (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold Gtail
  omega

open NearCubicWires.RepairOrdinary.CloseoutWitness.BudgetTools in
theorem Gtail_poly (hD : 1 ≤ D) (M0 : ℕ) : SourcePoly (Gtail mw SV a D copies degree delta M0) := by
  have hSz : SourcePoly (SzB mw SV degree M0) := by unfold SzB; fast_budget_poly
  have hMq : SourcePoly (MqB mw SV a degree M0) := by unfold MqB; fast_budget_poly
  have hE := W3.NearCubicWires.RepairOrdinary.CloseoutWitness.SourcePolicy.envelope_polynomial D copies delta hD hMq
  unfold Gtail
  fast_budget_poly

end TailB

end W3.NearCubicWires.RepairSource.Outer3.Front
