import Setup.PhaseB
import Proof.Wire_3_5.Primitive.Writers.HashCellA

/-!
# W3c ((a′) form), phase R: the guarded length walk and the imported constructor (A-run)

The near-cubic-gates paper's fixed weak machine (sec:gadget-transfer): the weak machine checks that "every … description of at most `L_ν` bits" holds
for `⟨B_src⟩_ν` and "constructs `C^O_{⟨B_src⟩_ν}`" with the imported constructor of imp:short-pcp applied to the
succinct verifier of lem:succinct-verifier. From `AfterB` with both fields decoded (`Decodes`): `1^ν` onto `NU`
(`HashCell.wrU`), the A-run (`OuterM.ARun`, docked with `dIn` ON `B_src`'s descriptor slot and `nIn` ON `NU`), then
`FL := [SrcFits]` from its flag port. Its word port then holds the RAW word of `C^O_{⟨B_src⟩_ν}`
(`CheckedPCPP.mwWord`), the composite's port `cIn`. `phR_ideal`: the end state reads like an ideal state satisfying
`AfterR`.
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
open NearCubicGates.Close.Worker.Format (readCount readField readBits countWord)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

noncomputable section

section Prog

end Prog

end

end NearCubicGates.Close.Setup
