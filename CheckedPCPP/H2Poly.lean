import Proof.Amplification.RecoveryCaseOnePaddedBitRun
import Proof.Amplification.RecoveryPCPFormulaResumeHierarchyActual
import Proof.Hierarchy.HierarchyStreamReady
import Proof.PCP.PCPPNativeClauseDescriptorConsumer
import Proof.PCP.PCPPNativeClauseDescriptorForward
import Proof.PCP.PCPPNativeClauseDescriptorTyped
import Proof.PCP.PCPPNativeFrame
import Proof.PCP.PCPPNativeHierarchyNodesReady
import Proof.PCP.PCPPRequestSourceInput
import Proof.PCP.PCPPSubstitutionCircuit
import CheckedPCPP.PolyClass
import CheckedPCPP.Dock
import Proof.PCP.PCPPNativeHierarchyCost
import Proof.PCP.PCPPNativeHierarchyEnvelope
import Proof.Foundations.BooleanCircuitSizePadding

/-!
# H2 with polynomial fuel (part of R3.cp)

`Substituted.global_run` (H2) has an explicit but unbounded fuel `Substituted.budget`. In the near-cubic-gates
paper the oracle is substituted "into the outer verifier to obtain a circuit `D_B` of size `q^{O_G(1)}`", with fixed polynomial
factors: here the fuel is bounded by `C·(|h| + |d| + 1)^e` in the hierarchy word `h` and the oracle descriptor `d`,
with `C, e` fixed by the source, the hierarchy and the padding (`global_run_poly`). Ingredients, all proof 1's: the
hierarchy stream cost (input and log exponents), `PCPPNativeHierarchySource.parameter_bound`,
`PCPPNativeResourceCost.source_counter_budget`, the compact node count, the descriptor-entry and tail bounds
(`PCPPNativeDescriptorBounds.entry_budget`, `PCPPNativeDescriptorTail.budget_bound`, minimum arity `0`).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.CheckedPCPP.H2Poly

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicGates.Close.CheckedPCPP

noncomputable section

theorem natWord_len_le (x : ℕ) : (natWord x).length ≤ 2 * x + 3 := by
  simp only [natWord, WilliamsPublishedForm.framedNatBits, List.length_append, List.length_replicate,
    List.length_cons, WilliamsPublishedForm.fixedWidthNatBits, List.length_ofFn]
  have : natBitLength x ≤ x + 1 := by
    have := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
    have := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2)
    simp only [natBitLength]; omega
  omega

end

end NearCubicGates.Close.CheckedPCPP.H2Poly
