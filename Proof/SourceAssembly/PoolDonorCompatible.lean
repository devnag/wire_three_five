import Proof.Rows.ClosureConstantGateReusable

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateFrame
open LocalBitMultitape RepairOrdinary RepairSource.ProjectionNormalization
open RepairSource.CloseoutFinal

end NearCubicWires.P1Closure.ConstantGateFrame

end

section

/-! The actual framed frozen native gate request. The arity prefix is
copied from its runtime native field, and the shifted strict threshold is
computed from original signed fields and membership. The existing measured
output framer physically writes the outer frame and restores every head. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.ConstantGateFrame
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open RepairSource.ProjectionNormalization CloseoutRowsPoolWeight
open SupplierPipeline

def aritySlots : Fin 4 → Fin 51 := ![48,49,34,50]
noncomputable def arity := RecoveryFocus.machine aritySlots CloseoutCaseTwo.NativeCopy.machine
def extra (q C : Nat) : Fin 3 → List Bool :=
  ![ZeroPadding.pad C (natWord q),List.replicate C false,List.replicate C false]
def input (xs : List Item) (z : Int) (tail backing : List Bool) (w C D E : Nat) : Fin 51 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) (ConstantGate.data xs z tail backing [] w C D E)
    (extra xs.length C)
def position : Machine 51 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>decide (q=1)
  rule := fun q _=>if q=0 then
    some ⟨1,fun _=>none,fun i=>if i=42 ∨ i=46 then .right else .stay⟩ else none
noncomputable def raw := Composition.machine (Composition.machine position arity)
  (TapeEmbedding.machine 3 ConstantGate.machine)

noncomputable def machine := AppendOutputFrame.machine raw (34 : Fin 51)

end NearCubicWires.P1Closure.ConstantGateFrame

end

section

/-! Read one original framed native gate into its arity and signed-field
ports. The only semantic source word is the original frame; neither the
field slice nor a transformed gate is supplied as input advice. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryLoad
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource.VerifierDecoding

def word {q : Nat} (g : ExactThresholdGate q) := natWord q++exactWord g
def unwrapSlots : Fin 3 → Fin 8 := ![0,1,7]
def headerSlots : Fin 3 → Fin 8 := ![1,3,2]
def recordSlots : Fin 4 → Fin 8 := ![1,4,5,6]
noncomputable def unwrap := RecoveryFocus.machine unwrapSlots Streaming.machine
noncomputable def header := RecoveryFocus.machine headerSlots (PCPPQueryField.machine true)
noncomputable def records := RecoveryFocus.machine recordSlots DecompositionSource.Records.child
def move (right : Bool) : Machine 8 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=6 then if right then .right else .left else .stay⟩ else none
noncomputable def raw := Composition.machine
  (Composition.machine (Composition.machine (Composition.machine unwrap header) (move true)) records) (move false)

def selected (i : Fin 8) := decide (i=2 ∨ i=5)
noncomputable def machine := MaskedReset.machine raw selected

end NearCubicWires.P1Closure.PoolEntryLoad

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RepairRepresentation RepairSource VerifierDecoding
open SupplierPipeline ProjectionNormalization CompilerSemantics
open scoped BigOperators

noncomputable def ready {q : Nat} (live : Finset (Fin q)) (g : SupportedNormalizedGate q) (B w : Nat) :=
  AppendOutputFrame.input (ConstantGateFrame.input (CloseoutRowsPoolMinimum.items g.gate live)
    (g.gate.threshold-1) [] [] w (ConstantGateReusable.C w) 0 (ConstantGateReusable.E B q))

end NearCubicWires.P1Closure.PoolEntry

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch

def xSlots : Fin 3 → Fin 64 := ![55,61,62]
def cSlots : Fin 3 → Fin 64 := ![53,61,63]
noncomputable def appendX := RecoveryFocus.machine xSlots CompetitorFrameAppend.machine
noncomputable def appendC := RecoveryFocus.machine cSlots CompetitorFrameAppend.machine

end NearCubicWires.P1Closure.PoolEntry

end

section

/-! One physical X/C pool entry, built from an original gate RepairOrdinary.frame.
The original arity and signed fields are loaded by the machine; the C
RepairOrdinary.frame is computed from those fields and runtime membership. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource VerifierDecoding
open SupplierPipeline ProjectionNormalization CompilerSemantics
open scoped BigOperators

abbrev workerSlots : Fin 55 → Fin 64 := fun i=>i.castAdd 9
def loadSlots : Fin 9 → Fin 64 := ![55,56,48,57,58,0,42,59,60]
noncomputable def loader := RecoveryFocus.machine loadSlots PoolEntryLoad.machine
noncomputable def frozen := RecoveryFocus.machine workerSlots ConstantGateFrame.machine
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine loader frozen) appendX) appendC



end NearCubicWires.P1Closure.PoolEntry

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntry
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch
open RepairRepresentation RepairSource SupplierPipeline
open scoped BigOperators


end NearCubicWires.P1Closure.PoolEntry

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryCursor
open LocalBitMultitape RepairOrdinary RecoveryExecution ExtDecompositionBatch

def selected (i : Fin 2) := decide (i=1)
noncomputable def copy := MaskedReset.machine (CloseoutRowsTupleSeek.frameMachine true) selected

end NearCubicWires.P1Closure.PoolEntryCursor

end

section

/-! Complete paid restoration of the original-gate callback. The protected
ports are growing output61 and retained original frame55. Every other working tape is restored from its retained
baseline master. Padding handles allocated blank tails without truncation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryRestore
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch ExtIncidence

def work : Fin 62 → Fin 64 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,56,57,58,59,60,62,63]
def selected (i : Fin 64) : Bool := decide (i≠61)

def maskSlots : Fin 65 → Fin 129 :=
  Fin.addCases (m:=64) (n:=1) (motive:=fun _=>Fin 129) (fun j : Fin 64=>j.castAdd 65) (fun _ : Fin 1=>126)
def restoreSlots : Fin 126 → Fin 129 :=
  Fin.addCases (m:=125) (n:=1) (motive:=fun _=>Fin 129)
    (Fin.addCases (m:=62) (n:=63) (motive:=fun _=>Fin 129) (fun j : Fin 62=>(j.castAdd 3).natAdd 64)
      (Fin.addCases (m:=62) (n:=1) (motive:=fun _=>Fin 129)
        (fun j : Fin 62=>(work j).castAdd 65) (fun _ : Fin 1=>127)))
    (fun _ : Fin 1=>128)
noncomputable def first {s : Nat} (p : Machine 64 s) := RecoveryFocus.machine maskSlots (MaskedReset.machine p selected)
noncomputable def restore := RecoveryFocus.machine restoreSlots (TemplateRestore.machine 62)
noncomputable def machine {s : Nat} (p : Machine 64 s) := Composition.machine (first p) restore

end NearCubicWires.P1Closure.PoolEntryRestore

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryBaseline
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch RepairRepresentation RepairSource
open SupplierPipeline VerifierDecoding CloseoutFinal SignedSortKey
open scoped BigOperators

attribute [local irreducible] PoolEntry.ready PoolEntryLoad.word RepairOrdinary.frame


noncomputable def machine := PoolEntryRestore.machine PoolEntry.machine

end NearCubicWires.P1Closure.PoolEntryBaseline

end

section

/-! A.2/A.3 correction 3, part 3: the X/C POOL WRITER LOOP.

The per-occurrence emission is fixed by `PoolRequestWriter`; this file runs
it.  The driver is the campaign's existing counted loop
(`CloseoutRowsDegreeLoop`), instantiated at the occurrence list: one paid
body call per RETAINED OCCURRENCE (not per pool entry), each emitting the
original request word and the frozen one.  Two consequences are proved:

* the accumulated output is exactly `occ.flatMap (entry live)`, the batch's
  own gate stream over `Universal.pool live occ`;
* started at the batch's count header and framed top, the loop's exit output
  is BYTE-EQUAL to `ExtDecompositionBatch.segment (pool live occ) top` - the
  acceptance criterion for the writer.

The loop is charged once per external row (bucket B2): its cost is
`|occ| * (cost + 3) + 3` with `cost` the per-occurrence body budget, so no
`2^{O(L_q^2)}` factor is multiplied into the hot column scan. -/
namespace NearCubicWires.RepairSource.CloseoutRowsPoolWriter
open LocalBitMultitape SupplierPipeline RepairRepresentation ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.CloseoutRowsCircuitBottom
open RepairSource.CloseoutRowsUniversal RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ### Indexing the emission by the driver's counter -/

/-! ### The loop -/

/-! ### The B2 segment bound -/

end
end NearCubicWires.RepairSource.CloseoutRowsPoolWriter

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryOccurrence
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairSource SupplierPipeline
open scoped BigOperators

def copySlots : Fin 3→Fin 131 := ![129,55,130]
def eraseSlots : Fin 3→Fin 131 := ![55,127,128]
noncomputable def copy := RecoveryFocus.machine copySlots PoolEntryCursor.copy
noncomputable def entry := TapeEmbedding.machine 2 PoolEntryBaseline.machine
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine (Composition.machine copy entry) erase


end NearCubicWires.P1Closure.PoolEntryOccurrence

end

section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.PoolEntryLoop
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairSource SupplierPipeline VerifierDecoding
open scoped BigOperators

noncomputable def machine := CloseoutRowsDegreeLoop.machine PoolEntryOccurrence.machine

end NearCubicWires.P1Closure.PoolEntryLoop

end
