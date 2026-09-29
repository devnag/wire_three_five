import Proof.Foundations.PaddedOracleRestriction
import Proof.Foundations.ProjectionWidthEnvelope
import Proof.Foundations.SupplierPrinter

/-!
# Branch-independent PCPP clause padding

The pointwise PCPP may return a circuit-dependent clause-address width.  The
headline schedule, however, must be fixed before the Case-1/Case-2 split.  This
module derives one source-only width envelope and repeats every native clause
over the added high address bits.  The repetition preserves the exact
acceptance fraction and keeps every padded query on the factory's one fixed
clause runner.
-/

namespace NearCubicWires.PCPPClausePadding

open Finset
open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter

def clauseAddressEquiv (native padded : ℕ) (hwidth : native ≤ padded) :
    Fin (2 ^ padded) ≃ Fin (2 ^ (padded - native)) × Fin (2 ^ native) := by
  let cast :
      Fin (2 ^ padded) ≃ Fin (2 ^ (padded - native) * 2 ^ native) :=
    finCongr (by
      rw [← Nat.pow_add, Nat.sub_add_cancel hwidth])
  exact cast.trans finProdFinEquiv.symm

def repeatedClauseIndex {native padded : ℕ} (hwidth : native ≤ padded)
    (index : Fin (2 ^ padded)) : Fin (2 ^ native) :=
  (clauseAddressEquiv native padded hwidth index).2

theorem binaryAddress_val_eq_ofBits {width : ℕ} (bits : BitInput width) :
    (binaryAddress bits).val = Nat.ofBits bits := by
  unfold binaryAddress
  change
    encodeBitInput bits % 2 ^ width =
      Nat.ofBits bits
  rw [encodeBitInput_eq_ofBits]
  exact Nat.mod_eq_of_lt (Nat.ofBits_lt_two_pow bits)

/-- The semantic repeated-clause PCPP.  Systematic and auxiliary coordinates,
the honest assignment, and the charged construction are unchanged. -/
noncomputable def padClauses
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits) :
    PointwisePCPP circuit where
  systematicBits := pcpp.systematicBits
  auxiliaryBits := pcpp.auxiliaryBits
  clauseBits := paddedClauseBits
  systematicSupport := pcpp.systematicSupport
  systematicSupportBound := pcpp.systematicSupportBound
  clauses := fun index => pcpp.clauses (repeatedClauseIndex hwidth index)
  honestAuxiliary := pcpp.honestAuxiliary
  constructionSteps := pcpp.constructionSteps
  honestSteps := pcpp.honestSteps

@[simp] theorem padClauses_assignment
    {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (paddedClauseBits : ℕ)
    (hwidth : pcpp.clauseBits ≤ paddedClauseBits)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) :
    (padClauses pcpp paddedClauseBits hwidth).assignment input auxiliary =
      pcpp.assignment input auxiliary :=
  rfl

/-! ## Simultaneous outer-randomness and clause-address padding -/

/-! ## Source-only outer and clause-width envelopes -/

end NearCubicWires.PCPPClausePadding
