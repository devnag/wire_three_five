import Proof.Wire_3_5.UnionMachine.UnionCheck

/-! # Eventual completeness of the union machine (P3:3675-3680, 3771)

Realizes the union machine's completeness in the paper's eventual form: "At the finitely many source lengths where
this fixed envelope exceeds the refuter's `N/10` guess budget, the machine rejects outright, so the imported
nondeterministic-bit restriction holds literally at every length; the eventual bounds make the guard vacuous for all
sufficiently large `N`" (P3:3675-3680), and "Finite exceptional lengths may be fixed arbitrarily" (P3:3771).

Paper quantity: the union machine's acceptance on every accepting guess past an onset, **`CompleteForEventually S P M`**
(the field `complete` of the split's `UnionLeafAt`, verbatim). The onset is chosen after the primitive and the language,
so the machine may reject outright below it; the ledger's time split holds with its onset fixed before the language.

* `CompleteFor.eventually`: 's `CompleteFor` implies it.
* `completeForEventually_of_run`: a machine accepting, past an onset, every witness of its length `W(N) ≥ ⌊N/16⌋` on
  which `unionRun` accepts, is eventually complete (`unionRun_complete`).
* `accepts_of_completeForEventually`: the Case-2 use, an accepting guess at a length past the onset is accepted. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost NearCubicWires.RepairSource

section Eventual
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

/-- **Eventual completeness of a machine**: past an onset, every accepting guess of the setup makes the
machine accept. -/
def CompleteForEventually (S : UnionSetup I) (P : FusedPrimitive I) (M : OrdinaryWeakMachine) : Prop :=
  ∃ onset : ℕ, ∀ N, onset ≤ N → ∀ (z : BitInput N) (g : UnionGuess S z), UnionAccepts S P z g → M.accepts N z

end Eventual

end NearCubicWires.WireExponent3_5.Transfer
