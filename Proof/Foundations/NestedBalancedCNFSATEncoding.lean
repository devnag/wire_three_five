import Proof.Foundations.NestedBalancedCNFCodec
import Proof.Foundations.BalancedCNFSATEncodingConservativeExtension

/-!
# Semantic promotion for nested balanced CNF queries

This module keeps the historical and flat-balanced SAT interfaces frozen and
specifies the additive semantics of the false-tagged, two-level balanced
marker.  The outer payload is a balanced list of chunk codes; each chunk is a
balanced list of canonical clause codes.  Flattening occurs only after both
levels have decoded successfully.
-/

namespace NearCubicWires.NestedBalancedCNFSATEncoding

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.BalancedCNFSATEncodingConservativeExtension
open NearCubicWires.CanonicalBinary
open NearCubicWires.NestedBalancedCNFCodec

open private decodeClauseCodes from Statement
open private legacyDecodeCNF from Statement

/-! ## Public canonical-clause decoding boundary -/

/-! ## Marker separation and historical rejection -/

/-! ## Additive SAT semantics -/

/-! ## Old-rejection of both nested markers by the *historical* semantics

Conservativity of the nested extension is the statement that the historical
`.sat` semantics — `legacyEncodedSat`, which the splice preserves verbatim on
its own branch — already rejects every nested marker.  Both facts below are
unconditional, so nothing the nested branch adds can disturb a query the
historical semantics already answered. -/

/-! ## The core splice, landed

`Semantics.encodedSat` now consults `decodeNestedBalancedCNF` on exactly the
branch both earlier decoders reject, so the promotion below is definitional.
The `…Promotion` predicate and the `_of_promotion` lemmas are kept so that
consumers written against the pre-splice interface continue to elaborate. -/

end NearCubicWires.NestedBalancedCNFSATEncoding
