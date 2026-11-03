import Proof.Wire_3_5.Recovery.CaseTwoPad
import Proof.CaseAnalysis.CaseTwoOriginalSource

/-! # The padded request's descriptor and PCPP source (P3:3761-3763; D1.6, Case 2 of the hybrid)

Realizes "each honest proof bit is computed by the deterministic PCPP algorithm" (P3:3762-3763) on `S₂`'s padded
request, one level up from `WireExponent3_5CaseTwoPad`: base's descriptor consumer (`PCPPNativeClauseDescriptorConsumer`,
generic in the producer and the circuit) framed on the padded producer writes the descriptor of
`request a (castCircuit hq c)`, its arity `1^{domain a q}` and size; base's `NativeSourceDock` (generic in the
descriptor machine and the request) then runs base's `RequestSource`/`SourceCache` on that request, i.e. computes the
PCPP output of the padded request.

Paper quantity: the PCPP output of the padded request; **`pmachine`** / **`pdescriptor_run`** (the padded descriptor)
and **`omachine`** / **`osource_run`** (the padded source: the clause data of `a.output request` and `frame (pcppInput
request)` for `request = PCPPRequestBoundary.request a (castCircuit hq c)`), with the input `oinput` by values
(`oinput_val`: the framed hierarchy/oracle word on tape 0 and `1^q` on the producer's extra tape). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-! ## The padded descriptor -/

def pbase (k : ℕ) := PCPPNativeClauseDescriptorConsumer.tapes (PCPPNativeHierarchyNodes.tapes source k + 5)
def ptapes (k : ℕ) := (pbase source k + 2) + 2

/-! ## The padded source -/

def otapes (a : PointwisePCPPAlgorithm) (k : ℕ) := NativeSourceDock.tapes a (ptapes source k)

/-! ## The padded source's input by values -/

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
