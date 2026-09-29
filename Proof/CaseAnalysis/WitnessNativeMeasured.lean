import Proof.CaseAnalysis.WitnessOracle

/-! The retained source word and decoded oracle feed the original stream
and measured-counter workers. This is the actual post-decoder continuation;
neither source selection nor canonical oracle parsing is repeated. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeMeasured
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
open RepairSource ProjectionNormalization SourceInterfaces ExecutableInterfaces VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def slots (i : Fin 75) : Fin 125:=
  if i=0 then 49 else if i=40 then 48 else if i=47 then 46
  else if i=52 then 29 else if i=54 then 25 else if i=57 then 38 else i.natAdd 50
def first:=TapeEmbedding.machine 77 Streams.machine
def second:=RecoveryFocus.machine slots PCPPNativeColdCounters.machine
def machine:=Composition.machine first second

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeMeasured
