import Proof.CaseAnalysis.RowsGateSupportMeaning
import Proof.CaseAnalysis.RowsStrictNative

/-! The cold field stream is the same decoded supported gate. These exact
port identities feed the arity/support checks and strict native request,
without interpreting a second circuit or serializing a second field list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateFieldsMeaning
open LocalBitMultitape RadixSemantics CanonicalBinary CanonicalWitnessCodec SupplierPipeline
open CloseoutWitness CloseoutRowsGateSupport RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def codes {n : ℕ} (g : SupportedNormalizedGate n) : Fin 3 → ℕ :=
  ![encodeIntList (List.ofFn g.gate.weight),encodeInt g.gate.threshold,encodeBoolList (gateMembers g.support)]

theorem field_codes {n : ℕ} (g : SupportedNormalizedGate n) (bits : List Bool)
    (h : value bits=encodeSupportedNormalizedGate g) :
    CompetitorWitnessTriple.structural bits ∧ ∀ i,value (CloseoutRowsGateHeader.codeWord bits i)=codes g i := by
  obtain ⟨hs,h0,h1,h2⟩ := CompetitorWitnessTriple.extracted_values bits (codes g 0) (codes g 1) (codes g 2) h
  refine ⟨hs,?_⟩
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem threshold_payload (bits : List Bool) (z : ℤ) (h : decodeInt (value bits)=some z) :
    CloseoutRowsIntegerGuard.payload bits=z.natAbs.bits := by
  have hc := encodeInt_of_decode h
  have hm : value (RecoveryFixedUnpair.rightWord bits)=encodeNat z.natAbs := by
    rw [(RecoveryFixedUnpair.word_values bits).2,←hc,encodeInt,Nat.unpair_pair]
  exact (BitFields.encoded_passes _ _ hm).2

end NearCubicWires.RepairOrdinary.CloseoutRowsGateFieldsMeaning
