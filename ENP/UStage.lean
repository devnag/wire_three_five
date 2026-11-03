import ENP.UGraph
import Proof.CaseAnalysis.RecoverySearchJoin
import Proof.CaseAnalysis.RecoverySearchCanonical

/-!
# Stages 1 and 3: one listed-pairs stage of the E^NP recovery (stages 1 and 3)

The near-cubic-gates paper's uniform recovery (sec:all-lengths, E^NP paragraph): "First, a formula over the description of `B_src` with the `N` constraints
(eq:source-check) … finds the first source circuit `B*_src`, or shows that there is none … Third, a formula over the
description of `B_pf` with the `2^{ℓ_out}` constraints `B_pf(a0^{q−ℓ_out}) = O*(a)` … finds the first `B*_pf`, or
shows that there is none." the extraction of the hard table: "Descriptions are ordered lexicographically, and 'first' refers to this order."

`program d`: the listed-pairs formula builder (`ENP.UGraph`) followed by proof 1's completed SAT search
(`RecoveryBoundedColdSearchJoin`, prefix self-reduction with the corrected SAT oracle). `stage_run`: it halts with the
flag `caseTwo (unitOuter w R vals hw) d x` (some bounded circuit agrees with the listed pairs) and, when it is set, the
canonical description of `RecoveryChoice.oracleSelector` — the first such circuit in description order. With
`vals = z`, `w = ν` this is `SrcExists` / `firstSrc` of Joins/Transfer; with `vals = tt(O*)`, `w = ℓ` it is stage 3.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.ENP.UStage

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.BoundedOracleStructuralCircuit NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace NearCubicWires.RepairSource.OrdinaryOracleCompose
open NearCubicWires.RepairSource.RecoveryChoice NearCubicWires.OuterPCPRecovery
open NearCubicGates.Close.ENP.USupply (uTapes)

/-- The stage program: the listed-pairs formula, then proof 1's SAT prefix search. -/
noncomputable abbrev program (d : ℕ) := RecoveryBoundedColdSearchJoin.program (UGraph.machine d)

/-- The stage's tapes. -/
abbrev tapes (d : ℕ) := 1664 + uTapes d + 790

/-- The stage's entry: the listed table, `R` and `W`. -/
def input (d : ℕ) (table : List Bool) (R W : ℕ) : Fin (tapes d) → List Bool :=
  Fin.addCases (m := 1664 + uTapes d) (n := 790) (UGraph.input d table R W) (fun _ => [])

/-- The flag tape (proof 1's search: `correctedSat` of the whole formula). -/
def flagPort (d : ℕ) : Fin (tapes d) := (369 : Fin 790).natAdd (1664 + uTapes d)
/-- The description tape (proof 1's search: the recovered prefix). -/
def descPort (d : ℕ) : Fin (tapes d) := (787 : Fin 790).natAdd (1664 + uTapes d)
/-- The query tape. -/
def queryPort (d : ℕ) : Fin (tapes d) := (356 : Fin 790).natAdd (1664 + uTapes d)

/-- The listed-pairs recovery formula (proof 1's bounded-oracle recovery formula of `unitOuter`). -/
noncomputable def formula (d w R : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n) :=
  boundedOracleRecoveryFormula (unitOuter w R vals hw) x (oracleSizeBound d R)

/-- The stage's cost bound. -/
noncomputable def cost (d w R W : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n) : ℕ :=
  UGraph.budget d w R W vals hw x + 2 + 1099511627776 *
    (RecoveryPrefixCold.radius (RecoveryFormulaPrefix.payload (formula d w R vals hw x))
      (descriptionWidth R (oracleSizeBound d R))) ^ 3

/-- **One listed-pairs stage** (the near-cubic-gates paper's uniform recovery, stages 1 and 3): the flag is `caseTwo` of the listed-pairs PCP and the
description tape holds the first bounded circuit agreeing with the listed pairs (description order). -/
theorem stage_run (d : ℕ) (vals post : List Bool) (w R W : ℕ) (hlen : vals.length = 2 ^ w) (hw : w ≤ R)
    {n : ℕ} (x : BitInput n) (hb : 0 < oracleSizeBound d R)
    (hW : originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ W)
    (hsource : (DedupBytes.fields (unitPCP w vals)).length ≤ W) (htwo : 2 ^ R ≤ W) :
    ∃ c ≤ cost d w R W vals hw x, ∃ final,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (program d) c
        (initialConfiguration (program d).base.machine (input d (RepairOrdinary.frame vals ++ post) R W)) final ∧
      (program d).base.machine.halted final.control = true ∧
      readTapeBit (final.tapes (flagPort d)) 0 = caseTwo (unitOuter w R vals hw) d x ∧
      (∀ small : SmallOracle (unitOuter w R vals hw) d x,
        final.tapes (descPort d) = RepairOrdinary.frame (canonicalBoundedCircuitDescription (oracleSizeBound d R)
          (oracleSelector (unitOuter w R vals hw) d x small).circuit)) ∧
      (final.tapes (queryPort d)).length ≤ c ∧ final.heads (queryPort d) = 0 := by
  obtain ⟨r, hr, _hs, hp, hhp, ha, hha⟩ :=
    UGraph.first_run d vals post w R W hlen hw x hb hW hsource htwo
  obtain ⟨c, hc, final, trace, halt, _heads, flag, description, qlen, qhead, _keep⟩ :=
    RecoveryBoundedColdSearchJoin.run (UGraph.machine d) (UGraph.budget d w R W vals hw x)
      (RecoveryFormulaPrefix.payload (formula d w R vals hw x)) (descriptionWidth R (oracleSizeBound d R))
      (RecoveryBoundedGraphBudget.scalarBacking W) (UGraph.input d (RepairOrdinary.frame vals ++ post) R W) r hr
      hp ha hhp hha
  refine ⟨c, hc, final, trace, halt, ?_, ?_, qlen, qhead⟩
  · exact flag.trans (CloseoutRecoveryCaseQuery.case_query (unitOuter w R vals hw) d x)
  · intro small
    exact description.trans (congrArg RepairOrdinary.frame
      (RecoveryBoundedSearchExecution.canonical_search (unitOuter w R vals hw) d x small))

end NearCubicGates.Close.ENP.UStage
