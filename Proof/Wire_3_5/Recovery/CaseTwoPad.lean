import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.Recovery.CertScan
import Proof.CaseAnalysis.CaseTwoRequestDescriptor
import Proof.Supplier.EquationRowCutsForward
import Proof.PCP.ProjectionNormalizationForwardRules

/-! # The padded request's node producer (P3:3728-3729, 3761-3763; D1.6, Case 2 of the hybrid)

Realizes the first machine step of "after which each honest proof bit is computed by the deterministic PCPP algorithm"
(P3:3762-3763) for the hybrid slice: the PCPP algorithm runs on `S₂`'s PADDED request, the request of the native
circuit cast to the padded width `q ≥ R` (`unionRequest_pad`: `request a (castCircuit h C)`). Base's request
descriptor (`CloseoutCaseTwo.RequestDescriptor`) frames `PCPPNativeClauseDescriptorConsumer.machine a p …` of the
hierarchy node producer `p`, and the consumer's `descriptor_run` is generic in the producer and in the circuit: it reads
the producer's node stream, output index, size, and WIDTH tape `1^n`. The padded producer is base's producer followed by
a width rewrite `1^R ↦ 1^q` (erase the width tape with driver `1^q`, copy `1^q` onto exactly `q` cells); the cast
circuit has the same node stream, size and output (`castCircuit`, `stream_cast`), so the consumer then writes the
descriptor of the padded request.

Paper quantity: the padded request `request a (castCircuit h c)`; **`widthFix`** / **`widthFix_ready`**,
**`padProducer`**, **`padProducer_forward`** (the producer writes its node stream by forward append), and
**`padProducer_run`**: the padded producer leaves the cast circuit's node stream, output index, size and width `1^q`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-! ## The cast circuit's descriptor data -/

/-! ## The width rewrite `1^R ↦ 1^q` -/

section Fix


end Fix

/-! ## The padded producer -/

noncomputable section Producer

end Producer

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad
