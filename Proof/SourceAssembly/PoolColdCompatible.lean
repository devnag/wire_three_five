import Proof.SourceAssembly.Compatible
import Proof.SourceAssembly.PoolDonorCompatible

/- The actual paired-pool writer followed immediately by Cold decomposition.
The shared source port aliases the append output. This omits the unused
atom-cache conversion and retains the exact child-count stream for packet input.
All input templates/reserves remain explicit; the caller must produce them. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6fbdd6f776f6447d_Source.PoolCold
open NearCubicWires LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairSource SupplierPipeline RepairRepresentation VerifierDecoding P1Closure
open scoped BigOperators
attribute [local irreducible] PoolEntryOccurrence.machine Cold.machine

abbrev sourcePort (a : DecompositionAlgorithm) := Cold.port a (str a)
def slots (a : DecompositionAlgorithm) (i : Fin (Cold.tapes a)) :
    Fin (132+Cold.tapes a) :=
  if i=sourcePort a then (61 : Fin 132).castAdd _ else i.natAdd 132

noncomputable def machine (a : DecompositionAlgorithm) := Composition.machine
  (TapeEmbedding.machine (Cold.tapes a) PoolEntryLoop.machine)
  (RecoveryFocus.machine (slots a) (Cold.machine a))

noncomputable def start {q : Nat} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w : Nat) (top : List Bool) :=
  RepeatMachine.cfg 0
    (PoolEntryLoop.cfg live occ B w 0 (natWord (2*occ.length)++RepairOrdinary.frame top)) occ.length 1

def coldHeads (a : DecompositionAlgorithm) := Cold.heads a 0
def coldData (a : DecompositionAlgorithm) (P q : Nat) := Cold.data a P q []

end PCJ6fbdd6f776f6447d_Source.PoolCold
