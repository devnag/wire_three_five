import Proof.Rows.ExpandedThresholdStream
import Proof.Rows.NativeScaleEquation
import Proof.Rows.PowerBank
import Proof.Rows.PowerFactorAway
import Proof.Rows.TopChildReady
import Proof.Rows.NativeCircuitPrepare

/-! Selected-child locator and scaled coefficient mapper share source65,
arity91, and U cap/log62/63. The growing coefficient stream stays at64. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_SelectedPowerBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_TopChildReady.machine

def caps (U : Nat) (i : Fin 94):=if i=65 ∨ i=91 then U else 0
def core (a B p w F U n : Nat) (bits out : List Bool) (i : Fin 94):=
 ZeroPadding.pad (caps U i) (PCJ45bee56da9f34d5a_PowerBank.bank a B p w F U n bits out (List.replicate U false) [] i)
def extras (source : List Bool) (index U : Nat):Fin 5→List Bool:=
 ![source,ZeroPadding.pad U (UnaryTemplate.tape index),List.replicate U false,List.replicate U false,List.replicate U false]
def bank (a B p w F U n index : Nat) (source bits out : List Bool):Fin 99→List Bool:=
 Fin.addCases (m:=94) (n:=5) (motive:=fun _=>List Bool) (core a B p w F U n bits out) (extras source index U)



end
end PCJ45bee56da9f34d5a_SelectedPowerBank
