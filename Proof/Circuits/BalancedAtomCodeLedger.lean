import Proof.Amplification.CanonicalBalancedRecoveryQueryCharges
import Proof.Circuits.PaddedRunnerBudgetClosure
import Proof.Circuits.StructuralGateBudgetEnvelope

namespace NearCubicWires.R1Leaf56BalancedAtomCodeLedger

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedRecoveryQueryCharges
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PaddedRunnerBudgetClosure
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.R1Leaf56StructuralGateBudgetEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.TotalInverseCanonicalBodySelectorLocalClosure
open NearCubicWires.ValidatorPolynomialDomination

/-! ## §1 The envelope chain is a source polynomial -/

theorem sourcePoly_atomEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => atomEnvelope (width m) (oracleBound m)) := by
  have hsum : SourcePoly (fun m => width m + oracleBound m + 1) :=
    (hwidth.add hbound).add (polyDominated_const 1)
  have hfactor :
      SourcePoly (fun m => 3 * (width m + oracleBound m + 1) + 1 + 1) :=
    ((hsum.const_mul 3).add (polyDominated_const 1)).add (polyDominated_const 1)
  refine PolyDominated.mono ((hsum.mul hfactor).add (polyDominated_const 20))
    fun m => le_of_eq ?_
  simp only [atomEnvelope, boundedCircuitFieldLimit]

theorem sourcePoly_rowEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => rowEnvelope (width m) (oracleBound m)) := by
  refine PolyDominated.mono
    (((sourcePoly_atomEnvelope hwidth hbound).const_mul 16).add
      (polyDominated_const 64)) fun m => le_of_eq ?_
  simp only [rowEnvelope]

theorem sourcePoly_grammarEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => grammarEnvelope (width m) (oracleBound m)) := by
  have hleft : SourcePoly (fun m => oracleBound m + 1) :=
    hbound.add (polyDominated_const 1)
  have hright :
      SourcePoly (fun m => rowEnvelope (width m) (oracleBound m) + 1) :=
    (sourcePoly_rowEnvelope hwidth hbound).add (polyDominated_const 1)
  refine PolyDominated.mono ((hleft.mul hright).add (polyDominated_const 1))
    fun m => le_of_eq ?_
  simp only [grammarEnvelope]

theorem sourcePoly_nodeEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => nodeEnvelope (width m) (oracleBound m)) := by
  have hatom := sourcePoly_atomEnvelope hwidth hbound
  have hshift :
      SourcePoly (fun m => atomEnvelope (width m) (oracleBound m) + 2) :=
    hatom.add (polyDominated_const 2)
  have hblock :
      SourcePoly (fun m =>
        oracleBound m * (atomEnvelope (width m) (oracleBound m) + 2) + 1) :=
    (hbound.mul hshift).add (polyDominated_const 1)
  refine PolyDominated.mono
    ((((hblock.const_mul 2).add (hatom.const_mul 2)).add
      (polyDominated_const 3)).add
      ((hshift.const_mul 5).add (polyDominated_const 1))) fun m => le_of_eq ?_
  simp only [nodeEnvelope]

theorem sourcePoly_outputEnvelope {width oracleBound : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound) :
    SourcePoly (fun m => outputEnvelope (width m) (oracleBound m)) := by
  have hatom := sourcePoly_atomEnvelope hwidth hbound
  have hshift :
      SourcePoly (fun m => atomEnvelope (width m) (oracleBound m) + 2) :=
    hatom.add (polyDominated_const 2)
  refine PolyDominated.mono
    ((hbound.mul (sourcePoly_nodeEnvelope hwidth hbound)).add
      ((hbound.mul hshift).add (polyDominated_const 1))) fun m => le_of_eq ?_
  simp only [outputEnvelope]

theorem sourcePoly_rowBudgetEnvelope {width oracleBound queryCount clauseCount :
      ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount) :
    SourcePoly (fun m =>
      rowBudgetEnvelope (width m) (oracleBound m) (queryCount m)
        (clauseCount m)) := by
  refine PolyDominated.mono
    (((sourcePoly_outputEnvelope hwidth hbound).mul hquery).add
      ((hclause.const_mul 6).add (polyDominated_const 1))) fun m => le_of_eq ?_
  simp only [rowBudgetEnvelope]

theorem sourcePoly_fixedCountEnvelope {width oracleBound queryCount clauseCount :
      ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount)
    (htwo : SourcePoly (fun m => 2 ^ width m)) :
    SourcePoly (fun m =>
      fixedCountEnvelope (width m) (oracleBound m) (queryCount m)
        (clauseCount m)) := by
  have hrow :
      SourcePoly (fun m =>
        rowBudgetEnvelope (width m) (oracleBound m) (queryCount m)
          (clauseCount m) + 1) :=
    (sourcePoly_rowBudgetEnvelope hwidth hbound hquery hclause).add
      (polyDominated_const 1)
  refine PolyDominated.mono
    (((sourcePoly_grammarEnvelope hwidth hbound).add
      ((hrow.mul htwo).add (polyDominated_const 1))).add
      (polyDominated_const 1)) fun m => le_of_eq ?_
  simp only [fixedCountEnvelope]

theorem sourcePoly_structuralGateEnvelope
    {width oracleBound queryCount clauseCount : ℕ → ℕ}
    (hwidth : SourcePoly width) (hbound : SourcePoly oracleBound)
    (hquery : SourcePoly queryCount) (hclause : SourcePoly clauseCount)
    (htwo : SourcePoly (fun m => 2 ^ width m)) :
    SourcePoly (fun m =>
      structuralGateEnvelope (width m) (oracleBound m) (queryCount m)
        (clauseCount m)) := by
  refine PolyDominated.mono
    ((((sourcePoly_fixedCountEnvelope hwidth hbound hquery hclause htwo).add
      (polyDominated_const 2)).mul hbound).add (polyDominated_const 1))
    fun m => le_of_eq ?_
  simp only [structuralGateEnvelope]

/-! ## §2 The canonical coordinates -/

end NearCubicWires.R1Leaf56BalancedAtomCodeLedger
