import Setup.Main
import Setup.Growth
import Codec.Field
import Codec.Transcode
import Worker.Format
import Proof.CaseAnalysis.CloseoutWitnessOracleBudget
import Gadget.CheckedSize
import Outer.Size

/-!
# SetupU, part 1 ((a′) form): the sizes the set-up reads and writes

The near-cubic-gates paper's fixed weak machine: the set-up costs `N^{d_0} poly(q)` (CHECK: `N·q^{O(G)}`), with one exponent for every clock.
* `cold_le`, `desc_le`: proof 1's cold decoder within `c (N+1)^25` steps, so each guessed circuit's native descriptor
  is at most that long;
* `mw_le`: the word of `C^O_{⟨B_src⟩_ν}` (A-run writes it within `K (ν+1)^e` steps);
* `comp_out_le`: the composite's J8 word and supports record (`CompFull`, within its fuel);
* `checked_m_le`: the size of `checkedCircuit P.code D_B` from `|D_B| ≤ |C|·(|B_pf| + 1) + q + 2`
  (`Outer.Dat_size_le`) and the import's size clause (`Outer.outC_size_le`);
* `polylog_le`: every fixed polynomial in `ν = ⌊log₂ N⌋` is at most linear in `N`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairOrdinary.RadixSemantics NearCubicWires.CanonicalWitnessCodec
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Joins
open NearCubicGates.Close.Worker (width pcpp gadgets oracleOK nu)

end NearCubicGates.Close.Setup
