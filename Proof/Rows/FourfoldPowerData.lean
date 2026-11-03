import Proof.Rows.CircuitPowerRun
import Proof.Rows.FourfoldBaseData

/-! The coefficient traversal uses the same actual selected children as the
canonical-base traversal, with concrete factor and emitted-stream invariants. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
set_option maxRecDepth 120000
namespace PCJ45bee56da9f34d5a_FourfoldPowerData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal
open PCJ45bee56da9f34d5a_FourfoldBaseData
open PCJ45bee56da9f34d5a_SelectedPowerBody (equation)
noncomputable section

def factor (d :Data) (B p :Nat):Nat→Nat
 | 0=>1
 | j+1=>if j<d.count then (factor d B p j*B)%p else factor d B p j

def stream (d :Data) (B p w :Nat):Nat→List Bool
 | 0=>[]
 | j+1=>if h:j<d.count then stream d B p w j++PCJ45bee56da9f34d5a_NativeScaleEquation.result
      (factor d B p j) p w (equation ((d.gates ⟨j,h⟩).get (d.selected ⟨j,h⟩)))
    else stream d B p w j

structure LocalBounds {n :Nat} (gs :List (ExactThresholdGate n)) (i :Fin gs.length) (v w F U :Nat):Prop where
 digit_fit : i.val<2^v
 digit_cost : MatrixUnaryTemplate.budget v i.val<U
 arity_cost : PCPPQueryNatural.budget n<U
 payload_fit : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U
 cursor_cost : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U
 gate_fit : (exactWord (gs.get i)).length+2≤U
 weight_cost : ∀j,C10NativeResidueCallback.coreBudget false ((gs.get i).weight j) w+1≤F
 target_cost : C10NativeResidueCallback.coreBudget true (gs.get i).target w+1≤F

structure Bounds (d :Data) (B p w F U v C P :Nat):Prop where
 positive : 0<p
 prime_fit : 2*p≤2^w
 base_fit : B<2^w
 capacity : 1024*(w+1)^2+2≤U
 payloads : ∀x∈d.words,x.length≤C
 top_cost : ∀j :Fin d.words.length,PCJ45bee56da9f34d5a_TopFrameReentry.budget d.words j C+2≤U
 local_fit : ∀j :Fin d.count,LocalBounds (d.gates j) (d.selected j) v w F U
 cell_cost : ∀j :Fin d.count,PCJ45bee56da9f34d5a_CircuitPowerRun.budget d.words
   ⟨j.val,by simp⟩ C (d.gates j) (d.selected j) w F U v≤P
end
end PCJ45bee56da9f34d5a_FourfoldPowerData
