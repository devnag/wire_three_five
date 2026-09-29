import Proof.Foundations.ComponentwiseVerifierParameters

/-!
# One-sided componentwise weak-machine ledger

This module is the last source-independent step in Appendix C.10.  An
accepting verifier branch on a hierarchy-NO input must expose the three
quantities it actually checked: rounded clause mean, real clause mean, and
decoded supplier estimate.  The local validity and gap lemmas make that trace
empty, hence every branch rejects.
-/

namespace NearCubicWires.ComponentwiseWeakMachine

open NearCubicWires
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.ComponentwiseVerifierParameters
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline

end NearCubicWires.ComponentwiseWeakMachine
