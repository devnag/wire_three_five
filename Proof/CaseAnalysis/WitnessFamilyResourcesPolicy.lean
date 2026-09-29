import Proof.CaseAnalysis.WitnessCorePolicy
import Proof.CaseAnalysis.WitnessFamilyResourcesCosts

/-! The actual coefficient and term caps have one fixed-source polynomial
envelope in the guarded public input length. No hierarchy clock occurs in
the parameters of this construction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
open SourceInterfaces RepairSource RepairRepresentation CloseoutWitnessPolicy PaddedRunnerBudgetClosure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def countBound (coefficient degree N : ℕ) := coefficient*(N+1)^degree
def coreBound (D N : ℕ) := (D+1)*(N+1)
def coefficientCap (delta : ℚ) (copies D R cb : ℕ) :=
  CloseoutXor.cap delta (CorePolicy.q0 D R) copies*max 1 (2*2^cb)
def termCap (delta : ℚ) (copies D R cb : ℕ) := LegalPolicy.T delta copies (CorePolicy.q0 D R) cb
def coefficientBound (delta : ℚ) (copies D c d N : ℕ) :=
  (64*delta.den^(3*copies+2))*(coreBound D N+1)*countBound c d N
def termBound (delta : ℚ) (copies D c d N : ℕ) :=
  (2*countBound c d N)*(termNumerator delta copies*coreBound D N+termDenominator delta copies)
def scale (delta : ℚ) (copies D c d N : ℕ) :=
  N+2+countBound c d N+coefficientBound delta copies D c d N+
    termBound delta copies D c d N+CloseoutMassThreshold.literalWidth delta copies

theorem scale_polynomial (delta : ℚ) (copies D c d : ℕ) : SourcePoly (scale delta copies D c d) := by
  have hc (v : ℕ) : SourcePoly (fun _=>v) := polyDominated_const v
  have hn:=sourcePoly_id.add (hc 1)
  have hcount:SourcePoly (countBound c d) := (sourcePoly_pow hn d).const_mul c
  have hcore:SourcePoly (coreBound D) := hn.const_mul (D+1)
  have hco:SourcePoly (coefficientBound delta copies D c d) :=
    ((hcore.add (hc 1)).const_mul (64*delta.den^(3*copies+2))).mul hcount
  have hterm:SourcePoly (termBound delta copies D c d) :=
    (hcount.const_mul 2).mul ((hcore.const_mul (termNumerator delta copies)).add
      (hc (termDenominator delta copies)))
  exact ((((sourcePoly_id.add (hc 2)).add hcount).add hco).add hterm).add
    (hc (CloseoutMassThreshold.literalWidth delta copies))

def countCoefficient (a : PointwisePCPPAlgorithm) (qc qd od : ℕ) :=
  (CloseoutSourceCounts.shortBound_polynomial a qc qd od).choose
def countDegree (a : PointwisePCPPAlgorithm) (qc qd od : ℕ) :=
  (CloseoutSourceCounts.shortBound_polynomial a qc qd od).choose_spec.choose
def sourceScale (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ) (delta : ℚ) (copies : ℕ) :=
  scale delta copies D (countCoefficient a qc qd od) (countDegree a qc qd od)

theorem source_scale_polynomial (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies : ℕ) : SourcePoly (sourceScale a qc qd od D delta copies) :=
  scale_polynomial delta copies D _ _

theorem source_envelope (a : PointwisePCPPAlgorithm) (qc qd od D : ℕ)
    (delta : ℚ) (copies : ℕ) :
    ∃ K E,1 ≤ K ∧ ∀ N,capacity (sourceScale a qc qd od D delta copies N) ≤ K*(N+1)^E := by
  have h:=((sourcePoly_pow ((source_scale_polynomial a qc qd od D delta copies).add
    (polyDominated_const 2)) 26).const_mul 100000000000000000000000000000000)
  obtain ⟨E,K,hbound⟩:=h
  refine ⟨K+1,E,by omega,fun N=>(hbound N).trans ?_⟩
  exact Nat.mul_le_mul_right _ (by omega)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyResources
