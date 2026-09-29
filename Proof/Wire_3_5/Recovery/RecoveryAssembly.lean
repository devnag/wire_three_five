import Proof.Wire_3_5.Recovery.RecoveryEventual

/-! # The recovery leaf (P3:3699-3756, 3820-3852; D1.7)

Realizes `tr:recovery`'s conclusion at row B: "The same `f` is therefore approximate-sum hard in both modes. Lemma
tr:xor makes `f^{⊕t(q)}` correlation hard for both classes, with threshold `e_{t(q)}` and the original per-atom cap"
(P3:3729-3733), "Choose the largest `a` such that `m_a ≤ n/2`, and extend the selected core to `n` inputs by ignoring the
suffix" (P3:3740-3741), and the row-B transfer to the headline caps (P3:3831-3852), at the union setup `S₁` pinned at
the gate.

Paper quantities:
* **`core_hard_at`**: at one source length, from the per-width facts (`RecQ`), the ledger's fit and guess budget, and
  the refuter's rejected yes-instance, the core is below `1/2 + e_{t(q)}` for every `SYM∘THR` and `THR∘THR` circuit within
  `⌊w_i(q)⌋` wires (`core_bounds` with Case 1's `caseOne_size` and Case 2's `ledger_at`);
* **`eventually_slice`**: the same at the recovered language's slice `n` past an onset, with `q = q(2^{a(n)})`;
* **`recLanguageCut`**: the recovered language, `false` below a cutoff on `N_a = 2^{a(n)}` (the cutoff the `E^NP`
  program may need, as in base's `CloseoutLanguage.language`);
* **`recLanguageCut_hard`**: `ThrHardAt (1/8) (11/2)` and `SymHardAt (1/8) (9/2)` at every multiplier (`rowB_thrHardAt`, `rowB_symHardAt`);
* **`recoveryLeaf`**: `RecoveryLeaf G S₁` from the gate relations and the language's `E^NP` certificate (D1.6). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open NearCubicWires.RepairSource.CloseoutSampledWitness (massCap)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open Filter

section Assembly

end Assembly

end NearCubicWires.WireExponent3_5.Transfer
