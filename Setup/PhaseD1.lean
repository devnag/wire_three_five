import Setup.PhaseC
import Recovery.TableSem
import WorkerArith.Classes
import CheckedPCPP.ClauseFront

/-!
# W3c, phase D, part 1: the registers of the loop entry

From `AfterC` (exact ideal state): `proofBits`, `rb` from the J8 header (`LitDecode.binW`, framed binary into a
register, then the head back), `sysCount = q + P.code.length q` from the opening `natWord` of the checked circuit word
(`readNatM`; `checkedCircuit_n`), `cl = clog 2 ((q+2)^{d_G}) = size ((q+2)^{d_G} − 1)` (`EncSetup.powW`,
`HTParts.sizeW`, `TableSem.clog_eq_size`), `M = 2^{cl}` (`ClauseFront.dblW`; the near-cubic-gates paper:
`M = 2^{⌈d_G lg(q+2)⌉}`), the loop counter `M`, and the transcoder's count `aux = proofBits + M`. Streams and heads
are unchanged (`regs_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val)
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK)

noncomputable section

/-! ## Framed binary into a register, head back -/

/-! ## A marked `natWord` into a register, head back -/


end

end NearCubicGates.Close.Setup
