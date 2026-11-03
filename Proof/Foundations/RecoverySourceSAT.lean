import Proof.Foundations.RecoveryOracleSemantics
import Statement

/-! The source refuter uses conventional explicit 3SAT, represented by a
canonical balanced list of fixed-length clause codes.  Recursive `Encodable`
is used only inside a three-literal clause, never around the whole formula.
The source predicate has no committed-prefix or legacy size-guard convention.
Its polynomial representation conversion and the lift to the corrected
recovery predicate are local theorems, not imported premises. -/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open CanonicalBinary BalancedCNFSATEncoding
open private legacyDecodeCNF natBitLength_succ_le pairSuccBits_le
  from Statement






end NearCubicWires.RepairSource.RecoveryOracle
