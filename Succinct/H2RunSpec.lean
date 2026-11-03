import Succinct.H2Header
import Succinct.H2Spec

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform

/-- The cost class of one substitution. -/
def h2Cost (S : ℕ) : ℕ := 10000000000 * (S + 2) ^ 7

def H2RunSpec : Prop :=
  ∀ (oc : OracleOutput) {q : ℕ} (B : BooleanCircuit q), ∃ (cap : ℕ) (τ : NearCubicWires.WireExponent3_5.FinalPass.Tm.WState 4 nrH),
    WXExec cap h2Prog (start oc.word (PCPPNative.descriptor B)) τ (h2Cost (sizeS oc B)) ∧
      τ.st sO = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity) ∧
      τ.st sW = oc.word ∧ τ.st sD = PCPPNative.descriptor B

end NearCubicGates.Close.Succinct.H2
