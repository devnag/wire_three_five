import Proof.MachineModel.ClosureCompactSize
import Proof.MachineModel.ClosureRadixNative

/-! Generated finite composition of existing arithmetic workers. All seven
numeric parameters and the cache are runtime words, not machine parameters.
Measuring/producing those inputs and the enclosing callback are separate duties.
See generate_metadata.py for the checked finite dependency graph. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactMetadata
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch ExtIncidence
open RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding

def p (b D Q : Nat) := b*(D*Q)+Q
def outer (B n N b : Nat) := CompactSize.value B n N b*256
def F (B n N b D Q : Nat) := RowCommonAllocation.value (N*Q) (p b D Q) (outer B n N b)
noncomputable def capOutput (n p F w N Q : Nat) :=
  Classical.choose (NativeCapacity.capacity_run n p F w N Q)
noncomputable def shortOutput (n w Q : Nat) := Classical.choose (NativeShort.short_run n w Q)

abbrev Store := Fin 162 → List Bool

def input (B n N b D Q w : Nat) (cache : List Bool) : Store := fun i =>
  if i=0 then List.replicate (B) true else if i=1 then UnaryTemplate.tape (n) else if i=2 then UnaryTemplate.tape (N) else if i=3 then List.replicate (b) true else if i=4 then UnaryTemplate.tape (D) else if i=5 then UnaryTemplate.tape (Q) else if i=6 then List.replicate (w) true else if i=7 then cache else []

def slots1 : Fin 18 → Fin 162 := ![0,1,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,3]
noncomputable def phase1 := RecoveryFocus.machine slots1 CompactSize.machine
noncomputable def data1 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots1 (input B n N b D Q w cache) (CompactSize.output B n N b)

noncomputable def joined1 := phase1
def budget1 (B n N b _D _Q _w : Nat) := CompactSize.budget B n N b
def slots2 : Fin 17 → Fin 162 := ![3,20,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
noncomputable def phase2 := RecoveryFocus.machine slots2 RowCommonResources.machine
noncomputable def data2 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots2 (data1 B n N b D Q w cache) (RowCommonResources.output b (CompactSize.value B n N b))

noncomputable def joined2 := Composition.machine joined1 phase2
def budget2 (B n N b D Q w : Nat) := budget1 B n N b D Q w+1+(RowCommonResources.budget b (CompactSize.value B n N b))
def slots3 : Fin 17 → Fin 162 := ![3,4,5,37,38,39,40,41,42,43,44,45,46,47,48,49,50]
noncomputable def phase3 := RecoveryFocus.machine slots3 RowCommonTupleDimensions.machine
noncomputable def data3 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots3 (data2 B n N b D Q w cache) (RowCommonTupleDimensions.output b D Q)

noncomputable def joined3 := Composition.machine joined2 phase3
def budget3 (B n N b D Q w : Nat) := budget2 B n N b D Q w+1+(RowCommonTupleDimensions.budget b D Q)
def slots4 : Fin 17 → Fin 162 := ![43,5,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65]
noncomputable def phase4 := RecoveryFocus.machine slots4 NativeFieldWidth.machine
noncomputable def data4 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots4 (data3 B n N b D Q w cache) (NativeFieldWidth.output (b*(D*Q)) Q)

noncomputable def joined4 := Composition.machine joined3 phase4
def budget4 (B n N b D Q w : Nat) := budget3 B n N b D Q w+1+(NativeFieldWidth.budget (b*(D*Q)) Q)
def slots5 : Fin 17 → Fin 162 := ![3,2,5,66,67,68,69,70,71,72,73,74,75,76,77,78,79]
noncomputable def phase5 := RecoveryFocus.machine slots5 RowCommonTupleDimensions.machine
noncomputable def data5 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots5 (data4 B n N b D Q w cache) (RowCommonTupleDimensions.output b N Q)

noncomputable def joined5 := Composition.machine joined4 phase5
def budget5 (B n N b D Q w : Nat) := budget4 B n N b D Q w+1+(RowCommonTupleDimensions.budget b N Q)
def slots6 : Fin 25 → Fin 162 := ![68,53,32,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101]
noncomputable def phase6 := RecoveryFocus.machine slots6 RowCommonAllocation.machine
noncomputable def data6 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots6 (data5 B n N b D Q w cache) (RowCommonAllocation.output (N*Q) (p b D Q) (outer B n N b))

noncomputable def joined6 := Composition.machine joined5 phase6
def budget6 (B n N b D Q w : Nat) := budget5 B n N b D Q w+1+(RowCommonAllocation.budget (N*Q) (p b D Q) (outer B n N b))
def slots7 : Fin 52 → Fin 162 := ![1,53,100,6,2,5,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147]
noncomputable def phase7 := RecoveryFocus.machine slots7 NativeCapacity.machine
noncomputable def data7 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots7 (data6 B n N b D Q w cache) (capOutput n (p b D Q) (F B n N b D Q) w N Q)

noncomputable def joined7 := Composition.machine joined6 phase7
def budget7 (B n N b D Q w : Nat) := budget6 B n N b D Q w+1+(NativeCapacity.budget n (p b D Q) (F B n N b D Q) w N Q)
def slots8 : Fin 17 → Fin 162 := ![1,6,5,148,149,150,151,152,153,154,155,156,157,158,159,160,161]
noncomputable def phase8 := RecoveryFocus.machine slots8 NativeShort.machine
noncomputable def data8 (B n N b D Q w : Nat) (cache : List Bool) : Store := install slots8 (data7 B n N b D Q w cache) (shortOutput n w Q)

noncomputable def joined8 := Composition.machine joined7 phase8
def budget8 (B n N b D Q w : Nat) := budget7 B n N b D Q w+1+(NativeShort.budget n w Q)
noncomputable def machine := joined8
noncomputable def output := data8
def budget := budget8

end NearCubicWires.P1Closure.CompactMetadata
