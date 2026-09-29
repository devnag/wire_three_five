import Proof.Wire_3_5.Recovery.RecoveryFamily
import Proof.Wire_3_5.UnionMachine.UnionEventual

/-! # Case 2 of the recovery: an approximate sum contradicts the union machine's rejection (P3:3711-3729; D1.2)

Realizes the Case-2 argument (P3:3711-3729): "Otherwise choose the lexicographically first such oracle before
choosing any class mode. The PCPP honest-assignment algorithm determines one Boolean addressed proof table
`f(i,j,x)`, shared by both modes. Suppose it [had] the bounded approximate sum from Lemma tr:xor in either mode.
[...] Lemma tr:completeness would then supply an accepting sparse guess in that mode, contradicting rejection of the
union machine. The same `f` is therefore approximate-sum hard in both modes."

Paper quantities: the accepting guess `∃ g, UnionAccepts S P z g` built from the XOR lemma's approximate sum
(`exists_unionAccepts_of_family`, from the occurrence-averaged family of D1.1), and the conclusion the Case-2
hardness donor reads: **`SampledXorSum (sym|thr)WireFamily ζ (q+r+1) t W (paddedUnsigned pcpp hr) → False`**
(`no_sampled_sym`, `no_sampled_thr`) at an input the machine rejects past its completeness onset. The ledger's
conditions at `q` (`exists_unionAccepts`'s hypotheses) are carried as the record `CaseTwoLedger`, discharged
eventually in the assembly (D1.5/D1.7). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.WireExponent3_5.Shared (uMean bitR)

section CaseTwo
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
variable (S : UnionSetup I) {N : ℕ} (z : BitInput N) (oracle : BooleanCircuit (S.pcp.nativeWidth N)) (m : Mode)

/-- The ledger's conditions at the request's width `q` that `exists_unionAccepts` reads, for atoms within the wire
cap `W` and the description cap `Ldesc` (the Case-2 family's limits), at mass bound `A`. -/
structure CaseTwoLedger (P : FusedPrimitive I) (cparams : MaskedCompletenessParameters S.params) (A : ℚ)
    (W Ldesc : ℕ) where
  hA : (A : ℝ) ≤ (S.gridMass (S.request z oracle).arity : ℝ)
  hΛ : 1 ≤ (S.gridMass (S.request z oracle).arity : ℝ)
  hs : 1 ≤ S.gridSize (S.request z oracle).arity
  hsδ : 19 * (S.gridMass (S.request z oracle).arity : ℝ) ^ 4 ≤
    (S.gridSize (S.request z oracle).arity : ℝ) ^ 2 * (cparams.δ : ℝ) ^ 4
  hStar : I.StarAt (S.request z oracle).arity
  hFit : B.FitsAt (S.request z oracle).arity
  hname : 2 ≤ I.nameCount
  hdesc : Ldesc ≤ ((S.request z oracle).arity + 1) ^ I.descDeg
  hdescK : m.descriptionBits (S.constAtom m (S.request z oracle).arity) ≤ ((S.request z oracle).arity + 1) ^ I.descDeg
  hdescP : ∀ Sp, m.descriptionBits (S.parityAtom m (S.request z oracle).arity Sp) ≤
    ((S.request z oracle).arity + 1) ^ I.descDeg
  hKP : ∀ Sp, (m.gates (S.parityAtom m (S.request z oracle).arity Sp)).length ≤ W
  hlen : (S.gridSize (S.request z oracle).arity + 1) * W ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg
  hbC : Ldesc ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg
  hbP : ∀ Sp, ∀ gt ∈ m.gates (S.parityAtom m (S.request z oracle).arity Sp),
    gt.encodingBits ≤ ((S.request z oracle).arity + 1) ^ I.carrierDeg
  Cpar : ℝ
  hCpar : 0 ≤ Cpar
  hwP : ∀ Sp, ((m.gates (S.parityAtom m (S.request z oracle).arity Sp)).wires : ℝ) ≤
    Cpar * ((S.request z oracle).arity : ℝ) ^ 2
  hcap : (I.starParams (S.request z oracle).arity hStar).popRate *
      ((S.gridSize (S.request z oracle).arity : ℝ) * W + Cpar * ((S.request z oracle).arity : ℝ) ^ 2) ≤
    (cparams.β : ℝ) * (B.capOf m (S.request z oracle).arity : ℝ)
  hξ : 1 / (2 : ℝ) ^ (I.filterParams m (S.request z oracle).arity).errExp ≤ (cparams.ξ : ℝ)
  hD : (1 + (S.gridMass (S.request z oracle).arity : ℝ)) ^ 4 *
      ((S.request z oracle).arity : ℝ) ^ (-(I.D : ℝ)) ≤ (S.params.eps0 : ℝ)
  Ko : ℕ
  Ks : ℕ
  Kc : ℕ
  hO : (natWord (ExecutableInterfaces.encodeBooleanCircuit oracle)).length ≤ Ko
  hKs : ∀ σ ∈ ({-1, 0, 1} : Finset ℤ), (intWord σ).length ≤ Ks
  hcodeC : ∀ C : m.Circuit (S.request z oracle).arity, m.descriptionBits C ≤ Ldesc → (natWord (m.code C)).length ≤ Kc
  hcodeK : (natWord (m.code (S.constAtom m (S.request z oracle).arity))).length ≤ Kc
  hbudget : 1 + Ko + ((S.pcppOf z oracle).systematicBits + (S.pcppOf z oracle).auxiliaryBits) *
    (S.gridSize (S.request z oracle).arity * (Ks + Kc)) ≤ N / 16

open NearCubicWires.RepairSource.CloseoutSampledWitness (symmetric_family threshold_family massCap symmetricLimits
  thresholdLimits)
open NearCubicWires.ComponentwiseCircuitRestriction (restrictedSymmetricDescriptionCap
  restrictedThresholdDescriptionCap)
open NearCubicWires.RecoveryWitnessPolicy (symmetricDescriptionCap thresholdDescriptionCap)
open NearCubicWires.CircuitRestriction (symmetricWireFamily thresholdWireFamily)

end CaseTwo

end NearCubicWires.WireExponent3_5.Transfer
