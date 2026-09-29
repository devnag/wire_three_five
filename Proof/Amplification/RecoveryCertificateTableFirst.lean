import Proof.Amplification.RecoveryCommittedBitLookup

/-! The selected physical certificate starts with the shared finite valuation.
The linear list cap follows from Fits; no semantic language or source premise
changes. The table prefix is quadratic and is copied once by the checker. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.TableFirst
open RepairOrdinary BalancedCertificate Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def limit (code : Nat) := 3*(natBitLength code+1)
def pack (width : Nat) (certificate : Certificate) : List Bool :=
  packList (packEntry width) certificate.table++RawSyntaxCertificate.pack width certificate.view++
    packList (packRow width) certificate.inner++packList (packRow width) certificate.outer

theorem counts_fit (code : Nat) : natBitLength code≤limit code ∧
    3*natBitLength code≤limit code ∧ 2*natBitLength code+1≤limit code := by
  unfold limit
  omega

theorem pack_length (width : Nat) (certificate : Certificate) :
    (pack width certificate).length=(Serialization.pack width certificate).length := by
  simp only [pack,Serialization.pack,List.length_append]
  omega

theorem pack_bound (code : Nat) (certificate : Certificate) (hf : Fits code certificate) :
    (pack (width code) certificate).length≤128*(natBitLength code+1)^3 := by
  rw [pack_length]
  exact Serialization.pack_bound code certificate hf

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.TableFirst
