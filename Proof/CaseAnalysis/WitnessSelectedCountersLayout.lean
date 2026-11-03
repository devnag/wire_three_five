import Proof.CaseAnalysis.WitnessSelectedStreamsLayout
import Proof.MachineModel.OrdinaryMatrixPacketBranch
import Proof.PCP.PCPPNativeHierarchyCountersDock

/-! Same retained stream fields enter the original native metadata/mass
producer. This preserves the size counter for the exact paper cap guard. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCounters
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
abbrev base (k : ℕ):=SelectedStreams.tapes source k
abbrev tapes (k : ℕ):=base source k+75
def sourcePorts (k : ℕ) : Fin 6→Fin (base source k):=
  ![SelectedStreams.old source k (SelectedOracle.descriptorSlot source k),
    SelectedStreams.old source k (SelectedStreams.bits source k 1),
    StreamCall.slots (SelectedStreams.fields source k) 46,
    StreamCall.slots (SelectedStreams.fields source k) 29,
    StreamCall.slots (SelectedStreams.fields source k) 25,
    StreamCall.slots (SelectedStreams.fields source k) 38]

def slots (k : ℕ) (i : Fin 75) : Fin (tapes source k):=
  if i=0 then (sourcePorts source k 0).castAdd 75
  else if i=40 then (sourcePorts source k 1).castAdd 75
  else if i=47 then (sourcePorts source k 2).castAdd 75
  else if i=52 then (sourcePorts source k 3).castAdd 75
  else if i=54 then (sourcePorts source k 4).castAdd 75
  else if i=57 then (sourcePorts source k 5).castAdd 75
  else i.natAdd (base source k)

def first (k CH Cpad : ℕ) (code : List Bool):=TapeEmbedding.machine 75 (SelectedStreams.machine source k CH Cpad code)
def second (k : ℕ):=RecoveryFocus.machine (slots source k) PCPPNativeColdCounters.machine
def machine (k CH Cpad : ℕ) (code : List Bool):=Composition.machine (first source k CH Cpad code) (second source k)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.SelectedCounters
