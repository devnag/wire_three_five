import Proof.CaseAnalysis.RecoveryPreparedLayout

/-! The physically initialized bank is the literal initial state consumed
by the original count compiler, with the one shared description arity. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (q bound Q clauses B : ℕ) : Fin 12→List Bool:=
  Function.update (RecoveryBoundedColdMetadata.extra q bound Q clauses B) 6
    (ZeroPadding.pad B (List.replicate (rowWidth q bound*(bound+1)) true))
noncomputable def targetData (q bound C Q clauses B : ℕ) (proj : Fin 37→List Bool) (source : List Bool) : Fin 158→List Bool:=
  Fin.addCases (m:=153) (n:=5)
    (RecoveryBoundedCountUniform.scanData
      (RecoveryBoundedCountBank.data B B (RecoveryBoundedGrammarBank.base 0 B [] [] [] source)
        proj (2^q) (RecoveryBoundedGrammarCold.metadata q bound 0 C B (extra q bound Q clauses B))
        (RecoveryBoundedColdDrivers.driver B bound) (RecoveryBoundedColdDrivers.driver B 0)) bound)
    (fun j=>List.replicate (RecoveryBoundedColdScalarMetadata.values q bound C Q clauses j) true)

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPrepared
