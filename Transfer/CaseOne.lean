import Joins.Transfer
import Proof.CaseAnalysis.ScheduleBounds
import Proof.Foundations.Semantics
import Target
import Proof.CaseAnalysis.CaseOneHardness
import Proof.CaseAnalysis.CaseOneBounds

/-!
# CaseOnePart — the near-cubic-gates paper's extraction of the hard table, Case 1

Outside Case 2 at the selected source length, the native function is the padded amplified hard function of the
three-way Case 1 (the near-cubic-gates paper's extraction of the hard table): (i) the source input `X_z` when no source circuit of `q^G` gates passes CHECK, (iii)
the first honest oracle `O*` when it has no `q^G`-gate circuit (the exceptional branch without an honest oracle does
not occur past the refuter's onset). A weighted symmetric circuit within the budget is a
symmetric threshold circuit with at most `b(q)(m+1)` wires (`toSymmetric`), whose Boolean simulation is far below the
amplifier's size bound once `G ≥ 17 c_STV` (proof 1's `symmetricAverageHard_of_boolean`,
`amplifier_size_ge_power`); its agreement is at most `1/2 + q^{-G/c}`, eventually below `1 − γ/5 + ε`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.CloseoutCaseOne NearCubicGates.Close.Gadget NearCubicGates.Target
open NearCubicWires.OuterPCPRecovery NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.PhysicalRecovery

/-- The amplified Case 1 core of a worst-case hard function on `q` inputs (proof 1's `scheduledAmplifierCore`, with the
hard function given directly: the source input `X_z` in Case 1 (i), the first honest oracle `O*` in Case 1 (iii)). -/
noncomputable def ampCore {c d : ℕ} (amplifier : ScheduleAmplifier c d) (q : ℕ) (f : BoolFunction q) (hq : 1 ≤ q)
    (hard : WorstCaseHardAt f (oracleSizeBound d q)) : HardCore booleanCircuitFamily where
  arity := (amplifier.output q f).arity
  function := (amplifier.output q f).function
  size := integerFloorRoot c (oracleSizeBound d q)
  advantage := Real.rpow (oracleSizeBound d q : ℝ) (-(1 : ℝ) / c)
  hard := by
    intro candidate hcandidate
    obtain ⟨circuit, hsize, rfl⟩ := hcandidate
    exact amplifier.sound _ f hq hard circuit hsize

/-- The Case 1 branch of `gateCore` is the padded amplified function. -/
theorem amplified_eq {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (q : ℕ) (f : BoolFunction q)
    (target : ℕ) (hfit : (amplifier.output q f).arity ≤ target) :
    GateParams.amplified amplifier q f target = padCore (amplifier.output q f).function hfit := by
  unfold GateParams.amplified
  simp only []
  rw [dif_pos hfit]

/-- `D_B`'s truncation inverts the oracle answer's padding (F4), when `ℓ ≤ q`. -/
theorem truncInput_padQuery {q ℓ : ℕ} (h : ℓ ≤ q) (a : BitInput ℓ) :
    Outer.truncInput (q := q) (Outer.padQuery a) = a := by
  funext i
  simp [Outer.truncInput, Outer.padQuery, show i.val < q by omega]

end NearCubicGates.Close.Transfer
