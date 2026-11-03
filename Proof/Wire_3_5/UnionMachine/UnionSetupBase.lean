import Proof.Wire_3_5.UnionMachine.UnionAtoms
import Proof.Wire_3_5.UnionMachine.UnionParams
import Bindings.CLW20_Lemma3_10
import Bindings.CLW20_Lemma3_11_TM2
import Bindings.TuringBridge.Budget
import Proof.CaseAnalysis.FinalTapeLocality
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.Hierarchy.HierarchyNormalizedRealization
import Proof.MachineModel.UWholeLanguage
import Proof.PCP.PCPPNativeHierarchyEnvelope
import Statement
import Proof.Wire_3_5.Foundations.SkeletonBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Ledger.LedgerWidth
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Foundations.Contracts
import Proof.Wire_3_5.Ledger.LedgerBudget
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule
import Proof.Hierarchy.CompetitorSourceAverage
import Proof.Foundations.ProjectionPCPPadding

/-! # The pinned union setup `S₀` (P3:3232-3260, 3632-3697)

Realizes the union setup the freeze gate pins (`Gate.Setup`): for every clock `T(N) = N^{kclk+2}` and every hierarchy
language `L ∈ NTIME(T)`, the data the union machine fixes before it is presented to the refuter (P3:3693-3697):
"Choose a polynomial hierarchy clock `T(N)=N^{C_clk}`. As in [NagCubic, Lemmas C.5–C.6], pad the outer verifier to
the exact width `q(N)` [...] Extra random bits are ignored; proof addresses receive a zero suffix. All probabilities and
the projection property are preserved" (P3:3632-3644); "Substituting a guessed size-`q^G` general oracle now gives a
circuit `H`" (P3:3651-3653); the outer PCP's soundness "at most `N^{−10}`" (P3:3257-3259).

Paper quantities (the fields of `UnionSetup`):
* the outer projection PCP of `L`: base's universal-source hierarchy PCP (`HierarchyNormalized.separated`, the `clw310`
  literal at `UWhole`, fixed before `kclk`) at `H = choose (L ∈ NTIME(T))`, padded (`padProjectionPCP`) to the width
  `max(R(N), q(N))`, which is the ledger's `q(N)` eventually (`width_le_nativeWidth`, `gateApad`);
* the pointwise PCPP (`gatePCPP`, literal `clw311`);
* **`outerSound`** from the PCP's soundness: the substituted circuit's acceptance mean is the padded PCP's acceptance
  fraction at the oracle's truth table (base `request_acceptance`, `outer_acceptance`) and is `≤ N^{−10}`
  (`padded_outerSound`);
* the masked verifier's constants (`gateParams`, from `exists_unionParams` at the PCPP gap);
* the grid: `s(q) = row.sp q` (the gate's), `Λ̄(q) = ⌊√(s(q)/C_δ)⌋`, `C_δ = ⌈5/δ²⌉`, so `19Λ̄⁴ ≤ s²δ⁴` at every `q`
  (`gridMass_hsδ`, the `hsδ` of `exists_unionAccepts`);
* the constant and parity atoms (`unionConstAtom`, `unionParityAtom`);
* the oracle degree `G` (a parameter until D1.4 pins it).

Main declarations: `padded_outerSound`, `setupOfResult` (a setup from any hierarchy PCP result), **`unionSetupS0`**
(`Gate.Setup` at every gate), `unionSetupS0_language` (its language is `L`), `gridMass_hsδ`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.ProjectionPCPPadding (padProjectionPCP padProjectionPCP_sound)
open NearCubicWires.RepairOrdinary.CompetitorSourceAverage (acceptanceMean request_acceptance outer_acceptance
  oracleProof)
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

/-! ## Outer soundness of a padded hierarchy PCP -/

/-! ## A setup from a hierarchy PCP result -/

section Setup

end Setup

/-! ## The gate's setup `S₀` -/

/-- `Λ̄(q) = ⌊√(s(q)/C_δ)⌋`: the largest mass the gate's grid size supports. -/
def gridMassOf (Cδ : ℕ) (sp : ℕ → ℕ) (q : ℕ) : ℚ := (Nat.sqrt (sp q / Cδ) : ℕ)

/-- **`19Λ̄⁴ ≤ s²δ⁴`** at every `q` (`hsδ` of `exists_unionAccepts`), whenever `5 ≤ C_δ δ²`. -/
theorem gridMass_hsδ (Cδ : ℕ) (sp : ℕ → ℕ) (δ : ℚ) (hδ : 0 ≤ δ) (hC : 5 ≤ (Cδ : ℚ) * δ ^ 2) (q : ℕ) :
    19 * ((gridMassOf Cδ sp q : ℚ) : ℝ) ^ 4 ≤ ((sp q : ℕ) : ℝ) ^ 2 * (δ : ℝ) ^ 4 := by
  unfold gridMassOf
  set m := Nat.sqrt (sp q / Cδ) with hm
  have h1 : m * m ≤ sp q / Cδ := Nat.sqrt_le _
  have h2 : sp q / Cδ * Cδ ≤ sp q := Nat.div_mul_le_self _ _
  have h3 : Cδ * (m * m) ≤ sp q := by nlinarith
  have h3' : (Cδ : ℝ) * ((m : ℝ) * m) ≤ (sp q : ℝ) := by exact_mod_cast h3
  have hC' : (5 : ℝ) ≤ (Cδ : ℝ) * (δ : ℝ) ^ 2 := by exact_mod_cast hC
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  push_cast
  have hsq : ((Cδ : ℝ) * ((m : ℝ) * m)) ^ 2 ≤ (sp q : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) h3' 2
  have h25 : (25 : ℝ) * (m : ℝ) ^ 4 ≤ ((Cδ : ℝ) * (δ : ℝ) ^ 2) ^ 2 * (m : ℝ) ^ 4 := by
    have : (25 : ℝ) ≤ ((Cδ : ℝ) * (δ : ℝ) ^ 2) ^ 2 := by nlinarith
    nlinarith [pow_nonneg hm0 4]
  nlinarith [pow_nonneg hm0 4, pow_nonneg hδ0 4]

variable (l : Literals) (oracleDeg : ℕ)

/-- The hierarchy of `L` (chosen from `L ∈ NTIME(T)`). -/
noncomputable def hierarchyOf {kclk : ℕ} {L : Language} (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    OrdinaryHierarchy (fun n => n ^ (kclk + 2)) :=
  Classical.choose hL

end NearCubicWires.WireExponent3_5.Transfer
