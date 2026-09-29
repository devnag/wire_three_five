import Proof.Foundations.TseitinCNF

/-!
# Conservative extension facts for compact balanced CNF queries

The compact marker occupies only queries rejected by the historical
well-sizedness predicate.  The extended SAT semantics therefore preserves
every old accepted query and sends a balanced marker to the exact historical
decision on its decoded formula.
-/

namespace NearCubicWires.BalancedCNFSATEncodingConservativeExtension

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.CanonicalBinary

end NearCubicWires.BalancedCNFSATEncodingConservativeExtension
