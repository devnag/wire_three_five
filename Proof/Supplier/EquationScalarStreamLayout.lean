import Proof.Supplier.EquationScalar

/-! Static seventeen-tape streaming scalar caller. The capacity is actual
unary tape data and does not parameterize this machine's finite control. -/
namespace NearCubicWires.RepairOrdinary.EquationScalarStream
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def moveSlots : Fin 3→Fin 17 := ![0,1,13]
def scalarSlots (j : Fin 12) : Fin 17 := ⟨j.val+1,by omega⟩
def copySlots : Fin 3→Fin 17 := ![10,14,13]
def scratchSlots (j : Fin 13) : Fin 17 := ⟨j.val+1,by omega⟩
def eraseSlots : Fin 15→Fin 17 :=
  Fin.addCases (m:=14) (n:=1) (motive:=fun _=>Fin 17)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>Fin 17) scratchSlots (fun _=>15)) (fun _=>16)
def moveProgram := RecoveryFocus.machine moveSlots PCPFieldMoves.advanceMachine
def scalarProgram (negate : Bool) := RecoveryFocus.machine scalarSlots (EquationScalar.machine negate)
def copyProgram := RecoveryFocus.machine copySlots PCPSerializerReuse.copyMachine
def eraseProgram := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 13)
def first (negate : Bool) := Composition.machine moveProgram (scalarProgram negate)
def tail := Composition.machine copyProgram eraseProgram
def machine (negate : Bool) := Composition.machine (first negate) tail




end
end NearCubicWires.RepairOrdinary.EquationScalarStream
