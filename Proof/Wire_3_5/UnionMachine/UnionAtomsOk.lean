import Lean
import Proof.Wire_3_5.UnionMachine.UnionEventual
import Proof.Wire_3_5.Transfer.TransferUnion
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule


noncomputable section
set_option maxRecDepth 4096


/-! # The union machine's atom test at the transfer level, and completeness at the honest guesses

"The weak machine guesses one size-`q^G` general oracle, a class tag, and one sparse grid sum for each distinct PCPP
variable. It rejects malformed descriptions, oversized atoms, and coefficients outside the fixed grid" (P3:3669-3671).
The completeness the paper uses is at the guess it CONSTRUCTS (Case 2, P3:3711-3716: the honest oracle and, for each
named variable, the occurrence average of the bounded approximate sum from Lemma tr:xor), whose atoms are within the
envelope.

* **`AtomsOkG`**: every grid atom within the description envelope of `PrimitiveInputs.Call`,
  `descriptionBits ≤ (q+1)^descDeg` (the same body as `UnionMachine.PlanW3.AtomsOkG`, here without the union machine);
* **`CompleteForEventuallyOk`**: past an onset, every accepting guess WITH its atoms in the envelope makes the machine
  accept (the completeness contract of a machine that runs the atom test);
* `CompleteForEventually.ok`: the old contract gives the new one.

Paper quantities of the main types: the atoms' description sizes against the envelope `(q+1)^descDeg`; the machine's
acceptance at the accepting guesses that pass the atom test. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost NearCubicWires.RepairSource

section Ok
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **The paper's atom test on a guess** (P3:3670): every grid atom within the description envelope of
`PrimitiveInputs.Call`, `descriptionBits ≤ (q+1)^descDeg`. -/
def AtomsOkG {S : UnionSetup I} {N : ℕ} {z : BitInput N} (g : UnionGuess S z) : Prop :=
  ∀ X a, g.mode.descriptionBits (g.atom X a) ≤ (g.q + 1) ^ I.descDeg

/-- **Completeness of a machine that runs the atom test**: past an onset, every accepting guess whose
atoms pass the test makes the machine accept. -/
def CompleteForEventuallyOk (S : UnionSetup I) (P : FusedPrimitive I) (M : OrdinaryWeakMachine) : Prop :=
  ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), UnionAccepts S P z g → AtomsOkG g →
    M.accepts N z

/-- The contract without the atom test gives the one with it. -/
theorem CompleteForEventually.ok {S : UnionSetup I} {P : FusedPrimitive I} {M : OrdinaryWeakMachine}
    (h : CompleteForEventually S P M) : CompleteForEventuallyOk S P M := by
  obtain ⟨onset, h⟩ := h
  exact ⟨onset, fun N hN z g hg _ => h N hN z g hg⟩

end Ok

end NearCubicWires.WireExponent3_5.Transfer

end
