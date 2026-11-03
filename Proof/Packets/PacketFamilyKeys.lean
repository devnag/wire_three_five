import Proof.CaseAnalysis.FiveRowKeys

/-! # Row keys in the exact `F.rows` order, for the packet family loop.

Paper: "One external row. It fixes one child tuple g, prime p, walk seed e,
and scalar residue f" (`paper.tex:1193-1196`); "All external rows ... are
multiplied by q^{h_D} exactly once" (`:1204-1206`). Consumer:
`Request.raw selector a r = F.rows.flatMap (rawWord a F g)`
(`Proof/Assembly/Production.lean`), which the family loop must
emit row by row in exactly `F.rows` order, duplicates kept. Budget: none
(this module is definitions and one order equation).

`RowKeys a` is the interface the parent consumes: a key type per request, the
key list, its decoding, and the order equation `keys.map decode = F.rows`.
`rcFiveKeys a` SUPPLIES it from the checked closeout keys
(`Proof/CaseAnalysis/FiveRowKeys.lean`: `sym_rows_eq` `:40`, `thr_rows_eq` `:81`). The terminal
sentinel has no rows and an empty key type. Nothing physical is claimed here.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketFamilyParent
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## The supplied instance: the checked closeout keys -/

/-- SYM: seed then offset tuple; THR: selection, prime, seed, residue < prime. -/
def rcKey (a : DecompositionAlgorithm) : Request → Type
  | .terminal => PEmpty
  | .sym r _ L target => RCFive.RowKeys.SymKey r L target
  | .thr r _ L target => RCFive.RowKeys.ThrKey a r L target

def rcKeys (a : DecompositionAlgorithm) : ∀ r : Request, List (rcKey a r)
  | .terminal => []
  | .sym r _ L target => RCFive.RowKeys.symKeys r L target
  | .thr r _ L target => RCFive.RowKeys.thrKeys a r L target

end
end NearCubicWires.PacketFamilyParent
