import Lean
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Recovery.HybridLeaf
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Recovery.HybridAssembly
import Proof.Wire_3_5.Assembly.FreeBase
import Proof.Wire_3_5.Assembly.Ok
import Proof.Wire_3_5.Recovery.HybridLeafOk
import Proof.Wire_3_5.Recovery.HybridLedgerOk
import Proof.CaseAnalysis.CaseTwoDirect
import Proof.CaseAnalysis.NativeWidthStep
import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Recovery.RecoveryEventualBase
import Proof.Wire_3_5.Recovery.RecoveryFamily
import Proof.Wire_3_5.Recovery.RecoveryLeaf
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.Transfer.TransferUnionCompleteBase
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule


noncomputable section
set_option maxRecDepth 120000


/-! # Leaf R with free constants for union leaves with the atom test, from D1.6 (§H.6)

The recovery leaf at every choice of the gate's free constants: the union machine is one-sided and `o(T(N))`, so the
refuter returns a rejected hierarchy yes-instance; the recovered language at that machine is hard in both classes
(`recLanguageCut2_hardOk`) and has an `E^NP` certificate (D1.6's input `Split.CertGen l`, at the clock `kclk`):
* **`recoveryLeafF2_of_certGen : CertGen l → RecoveryLeafF2 l`**;
* `literals_parts_of_certGen2`: `Parts` from leaves P, U (with the atom test) and D1.6.

Paper quantity of the main type: leaf R (the recovered language, its `E^NP` certificate, both hardnesses). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Transfer

variable (l : Literals)

/-- **Leaf R from D1.6** (§H.6: the recovered language is in `E^NP`), at every choice of the free constants, for union
leaves with the atom test: the language, its certificate and both hardness statements (`recoveryLeaf2Ok`). -/
noncomputable def recoveryLeafF2_of_certGen (h : CertGen l) : RecoveryLeafF2 l :=
  fun F _ => recoveryLeaf2Ok l (gate0 l F) (gateRel_gate0 l F) h

end NearCubicWires.WireExponent3_5.Split

end
