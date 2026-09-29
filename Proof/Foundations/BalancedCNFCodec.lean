import Proof.Foundations.CanonicalBinary

/-!
# Compact balanced CNF query codec

This low-level module sits below `Semantics`, so the fixed SAT opcode can
recognize the additive balanced query convention without changing the machine
instruction set.  The marker is an ordinary, constant-size CNF code whose
first clause is empty.  Hence the historical well-sized CNF convention rejects
it, while the singleton second clause carries a canonical balanced list of
ordinary clause codes.
-/

namespace NearCubicWires.BalancedCNFSATEncoding

open NearCubicWires
open NearCubicWires.CanonicalBinary

/-- Balanced payload containing the ordinary code of each clause. -/
def balancedCNFPayload (formula : List (List (Bool × ℕ))) : ℕ :=
  encodeBalancedList (formula.map Encodable.encode)







open private legacyDecodeCNF natBitLength_succ_le from Statement

/-! ## Level-2 (nested) balanced payload

The level-1 payload above is a single balanced list of clause codes.  A
scheduled producer cannot materialize that flat list without re-entering the
refuted geometric width cone of `OuterProofFormulaStreamGeometricDefect`, so
the additive convention below adds a second, disjointly tagged marker whose
payload is a balanced list of *chunk* codes, each chunk itself a balanced list
of canonical clause codes.  Decoding validates both levels and flattens only
afterwards, so no machine register ever holds the flat list.

The nested marker uses the `false` payload literal where the level-1 marker
uses `true`, so the two recognized regions are disjoint and both remain
old-malformed.  These definitions sit here, beside `decodeBalancedCNF`,
because `Proof.Foundations.Semantics` must see the nested decoder to dispatch `.sat`;
their theory is in `Proof.Foundations.NestedBalancedCNFCodec`. -/



/-- Prefix-constrained nested marker. -/
def nestedBalancedPrefixCNFMarkerOfPayload
    (payload assignment count : ℕ) : List (List (Bool × ℕ)) :=
  [[], [(false, payload)], [(false, assignment), (true, count)]]

def encodeNestedBalancedPrefixCNFPayloadMarker
    (payload assignment count : ℕ) : ℕ :=
  Encodable.encode
    (nestedBalancedPrefixCNFMarkerOfPayload payload assignment count)







end NearCubicWires.BalancedCNFSATEncoding
