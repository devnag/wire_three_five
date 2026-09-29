import Proof.SourceAssembly.SourceRequestTermSegA

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermBridge
open NearCubicWires RepairOrdinary RadixSemantics CanonicalBinary CanonicalWitnessCodec
open NearCubicWires.SourceRequest.TermSeg NearCubicWires.SourceRequest.TermReader

theorem atom_lt (w code a : Nat) (hcode : code < 2 ^ w) (ha : a ∈ (PCPPNativeCanonicalTree.tree code).atoms) :
    a < 2 ^ w :=
  lt_of_le_of_lt (CloseoutWitness.Reencode.atom_le code a ha) hcode

end NearCubicWires.SourceRequest.TermBridge

