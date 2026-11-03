import Setup.PhaseK
import Worker.Meaning

/-!
# W3c ((a′) form), phase C: the CheckedPCPP composite on the pair

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer): "Substituting `O_{B_pf}` for every oracle gate and negating the output gives the
outer verifier `D_B` … Apply imp:three-pcpp". On the accept branch (all guards hold): the composite (`CompFull`),
docked by `Worker.portDonor_ideal` with its port `cIn` ON the A-run's word port (the word of `C^O_{⟨B_src⟩_ν}`,
`CheckedPCPP.mwWord`) and `dIn` ON `B_pf`'s descriptor slot, its other tapes on the block `kB`, leaves the checked
circuit word, the J8 word, the supports record and the J8 header of `checkedCircuit P.code D_B`. `phC_ideal`: the end
state reads like an ideal state satisfying `AfterC`, the hand-off to phase D.
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.CanonicalWitnessCodec NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.Platform NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu PairOK)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

end

end NearCubicGates.Close.Setup
