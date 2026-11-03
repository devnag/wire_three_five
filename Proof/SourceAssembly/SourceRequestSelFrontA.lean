import Proof.SourceAssembly.SourceRequestLitInfo
import Proof.SourceAssembly.SourceRequestCoordBridge

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.SelFront
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause (index negative)
open NearCubicWires.SourceRequest.LitInfo
open PCJ6e421fabe2aa4155_SourceLiteralSupport (value)
open NearCubicWires.SourceRequest.CurComp (copyM copy_step)
open NearCubicWires.SourceFactorSel.Count (wordM word0_step)
noncomputable section

abbrev NF : Nat := 7000

/-! ## LitInfo's dock -/

def litSl (b : Fin 91) : Fin NF :=
  if cacheSide b then ⟨b.val, by unfold NF; omega⟩ else ⟨100 + b.val, by unfold NF; omega⟩

/-- **Front A**: `1^Q` onto LitInfo's driver port, LitInfo, `word iL`, `word iR`. -/
def frontA := Composition.machine (copyM (17 : Fin NF) 144 37)
  (Composition.machine (RecoveryFocus.machine litSl litM)
  (Composition.machine (wordM false (129 : Fin NF) 200 38) (wordM false (141 : Fin NF) 201 38)))

def costA (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (ci : Fin (2 ^ (a.output r).clauseBits)) : Nat :=
  2 * PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity) + 4 + 1 +
    (litCost a r ci (PCPPQueryCachedBounds.capacity a (r.circuit.size + r.arity)) + 1 +
      (2 * index ((a.output r).clauses ci).left + 8 + 1 + (2 * index ((a.output r).clauses ci).right + 8)))

end
end NearCubicWires.SourceRequest.SelFront

