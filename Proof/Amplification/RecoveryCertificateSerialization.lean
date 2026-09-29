import Proof.Amplification.RecoveryCertificateParsing

/-! Literal flat certificate serialization and its bounded inverse. -/
namespace NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairOrdinary BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def packEntry (width : Nat) (entry : Nat×Bool) : List Bool :=
  SignedSortKey.binary width entry.1++[entry.2]
def readEntry (width : Nat) : Parser (Nat×Bool) := fun bits => do
  let (index,rest) ← readField width bits
  let (bit,tail) ← readBit rest
  some ((index,bit),tail)
def packRow (width : Nat) (row : Row) : List Bool :=
  SignedSortKey.binary width row.kind++SignedSortKey.binary width row.code++
    SignedSortKey.binary width row.count++SignedSortKey.binary width row.payload
def readRow (width : Nat) : Parser Row := fun bits => do
  let (kind,r1) ← readField width bits
  let (code,r2) ← readField width r1
  let (count,r3) ← readField width r2
  let (payload,r4) ← readField width r3
  some (⟨kind,code,count,payload⟩,r4)
def pack (width : Nat) (certificate : Certificate) : List Bool :=
  RawSyntaxCertificate.pack width certificate.view++packList (packEntry width) certificate.table++
    packList (packRow width) certificate.inner++packList (packRow width) certificate.outer

theorem readEntry_pack (width : Nat) (entry : Nat×Bool)
    (hi : entry.1<2^width) (suffix : List Bool) :
    readEntry width (packEntry width entry++suffix)=some (entry,suffix) := by
  rcases entry with ⟨index,bit⟩
  simp [readEntry,packEntry,List.append_assoc,readField_pack width index hi,readBit]

def RowFitsWidth (width : Nat) (row : Row) : Prop :=
  row.kind<2^width ∧ row.code<2^width ∧ row.count<2^width ∧ row.payload<2^width

theorem readRow_pack (width : Nat) (row : Row) (h : RowFitsWidth width row) (suffix : List Bool) :
    readRow width (packRow width row++suffix)=some (row,suffix) := by
  rcases row with ⟨kind,code,count,payload⟩
  simp [readRow,packRow,List.append_assoc,readField_pack width kind h.1,
    readField_pack width code h.2.1,readField_pack width count h.2.2.1,
    readField_pack width payload h.2.2.2]

def width (code : Nat) := natBitLength code+2

theorem fields_fit (code : Nat) : code<2^width code ∧ natBitLength code<2^width code ∧ 2<2^width code := by
  have hc : code<2^natBitLength code := Nat.lt_pow_succ_log_self (by omega) _
  have hp : 2^natBitLength code≤2^width code := Nat.pow_le_pow_right (by omega) (by simp [width])
  have hn : natBitLength code<2^natBitLength code := Nat.lt_two_pow_self
  have ht : 2^2≤2^width code := Nat.pow_le_pow_right (by omega) (by simp [width])
  exact ⟨hc.trans_le hp,hn.trans_le hp,by omega⟩

end NearCubicWires.RepairSource.RecoveryOracle.CompactCertificate.Serialization
