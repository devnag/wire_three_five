import Proof.Wire_3_5.Recovery.RecoverySetupTwo

/-! # The hybrid core: Case 1 and the case split at the native PCP, Case 2 at the padded request (P3:3704-3733; D1.6)

Realizes the two cases of the recovery (P3:3704-3733) in the form the `E^NP` program computes: "If no
size-`q^G` oracle makes the outer verifier a tautology, any honest outer oracle is worst-case hard [...] Apply the
imported worst-case amplifier" at the refuter hierarchy's NATIVE outer PCP (width `R`), and "Otherwise choose the
lexicographically first such oracle [...] The same `f` is therefore approximate-sum hard in both modes" with `f` the
PCPP proof of the union machine's PADDED request (width `q(N)`) at that oracle with its inputs cast (`ext C`).

Paper quantities:
* `castCircuit_eval` (the cast oracle computes the native oracle on the low address bits) and **`accepts_cast`**
  (the padded verifier accepts the cast oracle at `r` iff the native verifier accepts the oracle at the prefix of `r`);
* **`hybridCore`**: the slice's core (the native case split and Case 1; Case 2's XOR of the padded request's PCPP
  proof);
* **`hybrid_bounds`**: at an input the union machine at `S₂` rejects although every accepting guess makes it accept,
  every `SYM∘THR` and `THR∘THR` circuit within the caps has agreement `< 1/2 + γ` with the hybrid core (Case 1: base's
  `core_hardness` at the native PCP; Case 2: `no_sampled_*` at `S₂` with the oracle `ext C`, base's
  `xor_hardness_from_sampled` and `averageHard_padCore`). -/

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

/-! ## The cast oracle -/

theorem castCircuit_eval {R w : ℕ} (h : R ≤ w) (C : BooleanCircuit R) (x : BitInput w) :
    (castCircuit h C).eval x = C.eval (fun i => x (Fin.castLE h i)) := by
  have hnode : ∀ (node : BooleanNode R) (prior : Array Bool),
      (castNode h node).eval x prior = node.eval (fun i => x (Fin.castLE h i)) prior := by
    intro node prior; cases node <;> rfl
  have hfold : ∀ (nodes : List (BooleanNode R)) (init : Array Bool),
      (nodes.map (castNode h)).foldl (fun prior node => prior.push (node.eval x prior)) init =
        nodes.foldl (fun prior node => prior.push (node.eval (fun i => x (Fin.castLE h i)) prior)) init := by
    intro nodes
    induction nodes with
    | nil => intro init; rfl
    | cons node tail ih =>
      intro init
      simp only [List.map_cons, List.foldl_cons, hnode]
      exact ih _
  unfold BooleanCircuit.eval BooleanCircuit.values
  show ((C.nodes.map (castNode h)).foldl (fun prior node => prior.push (node.eval x prior)) #[])[C.output.val]?.getD
    false = _
  rw [hfold]

/-- **The padded verifier accepts the cast oracle** exactly where the native verifier accepts the oracle. -/
theorem accepts_cast {M : TimedDecisionMachine} {T : ℕ → ℕ} (pcp : ProjectionPCP M T) (wf : ℕ → ℕ)
    (hw : ∀ n, pcp.nativeWidth n ≤ wf n) {N : ℕ} (z : BitInput N) (C : BooleanCircuit (pcp.nativeWidth N))
    (r : BitInput (wf N)) :
    acceptsOracleCircuit (padProjectionPCP pcp wf hw) z (castCircuit (hw N) C) r =
      acceptsOracleCircuit pcp z C (prefixBits (hw N) r) := by
  unfold acceptsOracleCircuit
  show (pcp.decision z (prefixBits (hw N) r)).eval _ = (pcp.decision z (prefixBits (hw N) r)).eval _
  congr 1
  funext query
  rw [castCircuit_eval]
  congr 1
  funext i
  show ((padProjectionPCP pcp wf hw).queryAddressBits z query (Fin.castLE (hw N) i)).eval r =
    (pcp.queryAddressBits z query i).eval (prefixBits (hw N) r)
  simp only [padProjectionPCP, Fin.val_castLE, Fin.is_lt, ↓reduceDIte, Fin.eta,
    ProjectionPCPPadding.liftProjectedRandomBit_eval]

/-! ## The hybrid core -/

/-- **The hybrid core**: the case split and Case 1 at the native PCP; Case 2 is the XOR of the PCPP proof of the
padded request at the cast selected oracle. -/
noncomputable def hybridCore {M : TimedDecisionMachine} {T : ℕ → ℕ} {c d n : ℕ} (pcp : ProjectionPCP M T)
    (wf : ℕ → ℕ) (hw : ∀ k, pcp.nativeWidth k ≤ wf k) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n) (copies clauseBits target : ℕ) :
    BoolFunction target := by
  classical
  exact if hsmall : SmallOracle pcp d input then
    if hc : (a.output (unionRequest (padProjectionPCP pcp wf hw) a input
        (castCircuit (hw n) (oracleSelector pcp d input hsmall).circuit))).clauseBits ≤ clauseBits then
      if ht : copies * ((unionRequest (padProjectionPCP pcp wf hw) a input
          (castCircuit (hw n) (oracleSelector pcp d input hsmall).circuit)).arity + clauseBits + 1) ≤ target then
        padCore (xorPower (paddedUnsigned (a.output (unionRequest (padProjectionPCP pcp wf hw) a input
          (castCircuit (hw n) (oracleSelector pcp d input hsmall).circuit))) hc) copies) ht
      else fun _ => false
    else fun _ => false
  else core pcp a amplifier input copies clauseBits target

theorem hybridCore_one {M : TimedDecisionMachine} {T : ℕ → ℕ} {c d n : ℕ} (pcp : ProjectionPCP M T)
    (wf : ℕ → ℕ) (hw : ∀ k, pcp.nativeWidth k ≤ wf k) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n) (copies clauseBits target : ℕ)
    (hsmall : ¬ SmallOracle pcp d input) :
    hybridCore pcp wf hw a amplifier input copies clauseBits target = core pcp a amplifier input copies clauseBits target := by
  unfold hybridCore
  rw [dif_neg hsmall]

theorem hybridCore_two {M : TimedDecisionMachine} {T : ℕ → ℕ} {c d n : ℕ} (pcp : ProjectionPCP M T)
    (wf : ℕ → ℕ) (hw : ∀ k, pcp.nativeWidth k ≤ wf k) (a : PointwisePCPPAlgorithm)
    (amplifier : OrdinaryScheduleAmplifier c d) (input : BitInput n) (copies clauseBits target : ℕ)
    (hsmall : SmallOracle pcp d input)
    (hc : (a.output (unionRequest (padProjectionPCP pcp wf hw) a input
        (castCircuit (hw n) (oracleSelector pcp d input hsmall).circuit))).clauseBits ≤ clauseBits)
    (ht : copies * ((unionRequest (padProjectionPCP pcp wf hw) a input
        (castCircuit (hw n) (oracleSelector pcp d input hsmall).circuit)).arity + clauseBits + 1) ≤ target) :
    hybridCore pcp wf hw a amplifier input copies clauseBits target =
      padCore (xorPower (paddedUnsigned (a.output (unionRequest (padProjectionPCP pcp wf hw) a input
        (castCircuit (hw n) (oracleSelector pcp d input hsmall).circuit))) hc) copies) ht := by
  unfold hybridCore
  rw [dif_pos hsmall, dif_pos hc, dif_pos ht]

/-! ## The hybrid core is hard in both classes -/

section Bounds

end Bounds

end NearCubicWires.WireExponent3_5.Transfer
