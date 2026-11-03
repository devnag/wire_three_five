import Succinct.H2Split

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.H2

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.Bindings.MW20
open NearCubicGates.Close.Platform NearCubicGates.Close.Succinct NearCubicGates.Close.Outer
open RepairRepresentation (natWord)

def EndOutSpec : Prop :=
  ∀ (o : OracleOutput) {q : ℕ} (B : BooleanCircuit q),
    marks (hdrD o B ++ (accI B o.circuit o.circuit.nodes.length).1.flatMap PCPPRequestNodeSchema.native ++
        PCPPRequestNodeSchema.native
          (BooleanNode.not (posF (ofl o.circuit) o.circuit.output.val (B.nodes.length - 1) B.output.val) :
            BooleanNode q) ++
        (List.replicate (q - (szv o B + 1)) (BooleanNode.const false : BooleanNode q)).flatMap
          PCPPRequestNodeSchema.native ++
        natWord (szv o B)) ++ [false] =
      RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit o.circuit B).padToArity)

end NearCubicGates.Close.Succinct.H2
