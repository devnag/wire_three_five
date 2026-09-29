import Proof.Wire_3_5.Recovery.RecoveryCaseTwo
import Proof.CaseAnalysis.CaseOneHardness
import Proof.CaseAnalysis.CaseTwoDirect

/-! # One slice of the recovered language is hard in both classes (P3:3704-3733; D1.4, D1.5)

Realizes the two cases at one source length (P3:3704-3733): "There are two cases, chosen independently of the class
tag. If no size-`q^G` oracle makes the outer verifier a tautology, any honest outer oracle is worst-case hard for that
general-circuit bound. Apply the imported worst-case amplifier." (Case 1, base `CloseoutCaseOne.core_hardness`) and
"Otherwise choose the lexicographically first such oracle before choosing any class mode. [...] The same `f` is
therefore approximate-sum hard in both modes. Lemma tr:xor makes `f^{⊕t(q)}` correlation hard for both classes, with
threshold `e_{t(q)}` and the original per-atom cap." (Case 2, base `CloseoutLanguage.case_two_direct_hardness` fed by
`no_sampled_sym`, `no_sampled_thr`).

Paper quantity: the agreement bound `< 1/2 + γ` of every `SYM∘THR` and `THR∘THR` circuit within the per-atom caps with
the core `core pcp a amplifier z t clauseBits n` of one source length (**`core_bounds`**), at an input the union machine
rejects although every accepting guess would make it accept. The case split is on base's `SmallOracle`; the
tautology of the selected oracle's substituted circuit is `taut_of_accepts`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.OuterPCPRecovery (acceptsOracleCircuit projectedInput)
open NearCubicWires.RepairSource.RecoveryChoice (SmallOracle oracleSelector)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open NearCubicWires.RecoveryWitnessPolicy (symmetricDescriptionCap thresholdDescriptionCap)
open NearCubicWires.CircuitRestriction (symmetricWireFamily thresholdWireFamily)

section Slice
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N)

/-- **The selected oracle's substituted circuit is a tautology**: an oracle accepting every random string of a
decision-independent PCP makes the substituted request circuit accept every input. -/
theorem taut_of_accepts (hind : ∀ u v, S.pcp.decision z u = S.pcp.decision z v)
    (oracle : BooleanCircuit (S.pcp.nativeWidth N)) (hacc : ∀ r, acceptsOracleCircuit S.pcp z oracle r = true) :
    ∀ y, (S.request z oracle).circuit.eval y = true := by
  intro y
  show (PCPPRequestBoundary.request S.pcppAlg (PCPPSubstitution.compactSubstituted oracle (S.pcp.queryAddressBits z)
    (S.pcp.decision z fun _ => false))).circuit.eval y = true
  rw [PCPPRequestBoundary.request_eval, CompetitorSourceAverage.outer_eval S.pcp z oracle hind]
  have h := hacc (ProjectionPCPPadding.prefixBits (Nat.le_max_left _ _) y)
  unfold acceptsOracleCircuit at h
  unfold ProjectionPCP.accepts ProjectionPCP.queryAddress
  simp only [CompetitorSourceAverage.oracleProof_address]
  exact h

end Slice

end NearCubicWires.WireExponent3_5.Transfer
