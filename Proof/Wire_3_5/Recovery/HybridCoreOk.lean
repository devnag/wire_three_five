import Proof.Wire_3_5.Recovery.HybridCore
import Proof.Wire_3_5.Recovery.RecoveryCaseTwoOk

/-! # The hybrid core is hard in both classes, from the atom test's completeness

"Otherwise choose the lexicographically first such oracle before choosing any class mode. … Lemma tr:completeness would
then supply an accepting sparse guess in that mode, contradicting rejection of the union machine" (P3:3711-3729). The
guess Case 2 constructs passes the atom test (P3:3670), so **`hybrid_bounds_ok`** is `hybrid_bounds` with completeness
only at accepting guesses WITH `AtomsOkG` (through `no_sampled_sym_ok`, `no_sampled_thr_ok`).

Paper quantity of the main type: the hybrid core's agreement with every small circuit in both classes. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RecoveryPipeline NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.OuterPCPRecovery (acceptsOracleCircuit projectedInput)
open NearCubicWires.RepairSource.RecoveryChoice (SmallOracle oracleSelector)
open NearCubicWires.RepairSource.CloseoutLanguage (core paddedUnsigned)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ProjectionPCPPadding (padProjectionPCP prefixBits)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open NearCubicWires.RecoveryWitnessPolicy (symmetricDescriptionCap thresholdDescriptionCap)
open NearCubicWires.CircuitRestriction NearCubicWires.RepairXor NearCubicWires.ComponentwiseTransfer

section BoundsOk
variable (l : Literals) (G : Split.Gate) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

/-- **The hybrid core of one source length is hard in both classes** (Case 1 at the native PCP, Case 2 at `S₂`), from completeness at the guesses passing the atom test. -/
theorem hybrid_bounds_ok (P : FusedPrimitive (G.inputs kclk coef A a ha)) (M : OrdinaryWeakMachine) {N : ℕ}
    (z : BitInput N)
    (hacc : ∀ g : UnionGuess (recSetup2 l G kclk coef A a ha) z,
      UnionAccepts (recSetup2 l G kclk coef A a ha) P z g → AtomsOkG g → M.accepts N z)
    (hrej : ¬ M.accepts N z) (copies clauseBits target symCap thrCap : ℕ) (gamma : ℝ)
    -- Case 1, at the native PCP
    (hq : 1 ≤ (recPCP l kclk).pcp.nativeWidth N)
    (complete : ∃ proof, ∀ randomness, (recPCP l kclk).pcp.accepts z proof randomness)
    (hfit1 : ((selectedAmplifier l.eightSources.amplification (recOracleDeg l)).output
      (RecoveryCaseOneRequest.request (recPCP l kclk).pcp z).inputArity
      (RecoveryCaseOneRequest.request (recPCP l kclk).pcp z).function).arity ≤ target)
    (hsym1 : 40 * (target + symCap + 2) ^ 4 ≤ integerFloorRoot l.eightSources.amplification.stvExponent
      (oracleSizeBound (recOracleDeg l) ((recPCP l kclk).pcp.nativeWidth N)))
    (hthr1 : 50 * (target + thrCap + 2) ^ 4 ≤ integerFloorRoot l.eightSources.amplification.stvExponent
      (oracleSizeBound (recOracleDeg l) ((recPCP l kclk).pcp.nativeWidth N)))
    (hadv1 : Real.rpow (oracleSizeBound (recOracleDeg l) ((recPCP l kclk).pcp.nativeWidth N) : ℝ)
      (-(1 : ℝ) / l.eightSources.amplification.stvExponent) < gamma)
    -- Case 2, at the padded request of `S₂`
    (hcopies : 1 ≤ copies) (heps : xorEpsilon ((gateCParams1 l).ζ : ℝ) copies < gamma)
    (hc2 : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ oracleSizeBound (recOracleDeg l) ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      ((recSetup2 l G kclk coef A a ha).pcppOf z oracle).clauseBits ≤ clauseBits)
    (hfit2 : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ oracleSizeBound (recOracleDeg l) ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      copies * (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseBits + 1) ≤ target)
    (ledS : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ oracleSizeBound (recOracleDeg l) ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      CaseTwoLedger (recSetup2 l G kclk coef A a ha) z oracle .sym P (gateCParams1 l)
        (massCap (gateCParams1 l).ζ copies) symCap
        (restrictedSymmetricDescriptionCap ((recSetup2 l G kclk coef A a ha).request z oracle).arity
          (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseBits + 1)
          (2 ^ symmetricDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseBits + 1)
            symCap) symCap))
    (ledT : ∀ oracle : BooleanCircuit ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N),
      oracle.size ≤ oracleSizeBound (recOracleDeg l) ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) →
      CaseTwoLedger (recSetup2 l G kclk coef A a ha) z oracle .thr P (gateCParams1 l)
        (massCap (gateCParams1 l).ζ copies) thrCap
        (restrictedThresholdDescriptionCap ((recSetup2 l G kclk coef A a ha).request z oracle).arity
          (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseBits + 1)
          (2 ^ thresholdDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseBits + 1)
            thrCap)
          (thresholdDescriptionCap (((recSetup2 l G kclk coef A a ha).request z oracle).arity + clauseBits + 1)
            thrCap))) :
    (∀ circuit : SymmetricThresholdCircuit target, circuit.wireCount ≤ symCap →
      agreement circuit.eval (hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _)
        (gatePCPP l) (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z copies clauseBits target) <
        1 / 2 + gamma) ∧
    (∀ circuit : ThresholdThresholdCircuit target, circuit.wireCount ≤ thrCap →
      agreement circuit.eval (hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _)
        (gatePCPP l) (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z copies clauseBits target) <
        1 / 2 + gamma) := by
  have hz0 := gateZeta_pos l
  have hz1 := gateZeta_lt l
  have hwN : (recPCP l kclk).pcp.nativeWidth N ≤ paddedWidth l G (refH l kclk) N := le_max_left _ _
  by_cases hsmall : SmallOracle (recPCP l kclk).pcp (recOracleDeg l) z
  · have hsizeO : (castCircuit hwN
        (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) z hsmall).circuit).size ≤
        oracleSizeBound (recOracleDeg l) ((recSetup2 l G kclk coef A a ha).pcp.nativeWidth N) := by
      rw [castCircuit_size]
      exact (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) z hsmall).sizeBounded.trans
        (oracleSizeBound_monotone _ hwN)
    have haccO : ∀ r, acceptsOracleCircuit (recSetup2 l G kclk coef A a ha).pcp z
        (castCircuit hwN (oracleSelector (recPCP l kclk).pcp (recOracleDeg l) z hsmall).circuit) r =
          true := fun r =>
      (accepts_cast (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) z _ r).trans
        ((oracleSelector (recPCP l kclk).pcp (recOracleDeg l) z hsmall).accepts _)
    have htaut := taut_of_accepts (recSetup2 l G kclk coef A a ha) z (recSetup2_hind l G kclk coef A a ha z) _ haccO
    have hc := hc2 _ hsizeO
    have hfit := hfit2 _ hsizeO
    have hs := no_sampled_sym_ok (recSetup2 l G kclk coef A a ha) z _ l.eightSources.normalization l.eightSources.expander
      P (gateCParams1 l) M hacc hrej hsizeO htaut clauseBits copies symCap hc (gateCParams1 l).ζ hz0 hz1 le_rfl
      (ledS _ hsizeO)
    have ht := no_sampled_thr_ok (recSetup2 l G kclk coef A a ha) z _ l.eightSources.normalization l.eightSources.expander
      P (gateCParams1 l) M hacc hrej hsizeO htaut clauseBits copies thrCap hc (gateCParams1 l).ζ hz0 hz1 le_rfl
      (ledT _ hsizeO)
    rw [hybridCore_two (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l)
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z copies clauseBits target hsmall hc hfit]
    have hsX := CloseoutLanguage.xor_hardness_from_sampled Bindings.CLW20Lemma38.clw20_xor_source
      (gateCParams1 l).ζ hz0 hz1 symmetricWireFamily symmetricWireFamily_literalProjectionClosed
      symmetricWireFamily_negationClosed _ (by omega) copies symCap hcopies hs
    have htX := CloseoutLanguage.xor_hardness_from_sampled Bindings.CLW20Lemma38.clw20_xor_source
      (gateCParams1 l).ζ hz0 hz1 thresholdWireFamily thresholdWireFamily_literalProjectionClosed
      thresholdWireFamily_negationClosed _ (by omega) copies thrCap hcopies ht
    have hsP := averageHard_padCore (family := symmetricWireFamily) (size := symCap)
      symmetricWireFamily_restrictionClosed hsX hfit
    have htP := averageHard_padCore (family := thresholdWireFamily) (size := thrCap)
      thresholdWireFamily_restrictionClosed htX hfit
    have hstrict : 1 / 2 + xorEpsilon ((gateCParams1 l).ζ : ℝ) copies < 1 / 2 + gamma := by linarith
    exact ⟨fun circuit hcap => (hsP circuit.eval ⟨circuit, hcap, rfl⟩).trans_lt hstrict,
      fun circuit hcap => (htP circuit.eval ⟨circuit, hcap, rfl⟩).trans_lt hstrict⟩
  · rw [hybridCore_one (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l)
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z copies clauseBits target hsmall]
    exact CloseoutCaseOne.core_hardness (recPCP l kclk).pcp (gatePCPP l)
      (selectedAmplifier l.eightSources.amplification (recOracleDeg l)) z copies clauseBits target symCap thrCap
      l.eightSources.normalization hq complete hsmall hfit1 hsym1 hthr1 gamma hadv1

end BoundsOk

end NearCubicWires.WireExponent3_5.Transfer
