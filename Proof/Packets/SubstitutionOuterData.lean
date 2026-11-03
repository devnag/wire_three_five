import Proof.Packets.SubstitutionScan
import Proof.Packets.VectorAccumulatorRight
import Proof.Packets.VectorOperandCopies

/-! Shared physical arena for exact monomial substitution. Tapes39/40 hold the
outer sum; tapes41/42 retain the physically generated constant-one packet. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding



def accumulatorPorts : Fin 36→Fin 43 := Fin.addCases (m:=34) (n:=2) (fun i=>i.castAdd 9) ![39,40]
def constantPorts : Fin 36→Fin 43 := Fin.addCases (m:=34) (n:=2) (fun i=>i.castAdd 9) ![41,42]









end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionOuter
