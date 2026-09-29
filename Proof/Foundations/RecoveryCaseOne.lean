import Proof.Foundations.RecoverySourceContracts

/-! Immediate and enclosing recovery consumers of the corrected source.
One ordinary hierarchy and one selected PCP supply the canonical Case-1 table.
The later-cutoff-universal AmplifierWitness and legacy executable refuter are
not cast targets. Source construction and final language execution remain
separate from these proved semantic applications. -/
namespace NearCubicWires.RepairSource
open ExecutableInterfaces SourceInterfaces RecoveryPipeline OuterPCPRecovery
open RecoveryScheduleEnvelope ComponentwiseTransfer PhysicalRecovery CaseOnePadding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def selectedAmplifier (factory : SourceAmplifierFactory) (d : ℕ) :
    OrdinaryScheduleAmplifier factory.stvExponent d :=
  Classical.choice (factory.forSchedule d)

/-- Canonical accepted table; worst-case hardness follows from the literal
absence of a small accepting oracle for this same PCP. -/
noncomputable def scheduledAmplifierCore
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {c d n : ℕ} (amplifier : ScheduleAmplifier c d)
    (pcp : ProjectionPCP machine timeBound) (input : BitInput n)
    (hq : 1 ≤ pcp.nativeWidth n)
    (complete : ∃ proof, ∀ randomness, pcp.accepts input proof randomness)
    (noSmall : ∀ circuit : BooleanCircuit (pcp.nativeWidth n),
      circuit.size ≤ oracleSizeBound d (pcp.nativeWidth n) →
      ¬∀ randomness, acceptsOracleCircuit pcp input circuit randomness) :
    HardCore booleanCircuitFamily := by
  let canonical := Classical.choice (existsCanonicalAcceptingProof pcp input complete)
  let seed := proofFunction pcp canonical.proof
  have hard : WorstCaseHardAt seed (oracleSizeBound d (pcp.nativeWidth n)) := by
    intro circuit hsize
    by_contra hmatches
    have heval : circuit.eval = seed := by
      funext address
      exact not_ne_iff.mp (not_exists.mp hmatches address)
    exact noSmall circuit hsize
      (acceptsOracleCircuit_of_proof pcp input canonical.proof
        canonical.accepts circuit heval)
  let result := amplifier.output (pcp.nativeWidth n) seed
  refine { arity := result.arity
           function := result.function
           size := integerFloorRoot c (oracleSizeBound d (pcp.nativeWidth n))
           advantage := Real.rpow (oracleSizeBound d (pcp.nativeWidth n) : ℝ)
             (-(1 : ℝ) / c)
           hard := ?_ }
  intro candidate hcandidate
  obtain ⟨circuit, hsize, rfl⟩ := hcandidate
  exact amplifier.sound _ seed hq hard circuit hsize

/-- The table is padded semantically by ignored variables, preserving both
hardness parameters. This is the existing physical consumer's actual core. -/
noncomputable def padAmplifierCore (core : HardCore booleanCircuitFamily)
    (target : ℕ) (hcore : core.arity ≤ target) : HardCore booleanCircuitFamily where
  arity := target
  function := padCore core.function hcore
  size := core.size
  advantage := core.advantage
  hard := averageHard_padCore (family := booleanCircuitFamily) (size := core.size)
    booleanCircuitFamily_restrictionClosed core.hard hcore

end NearCubicWires.RepairSource
