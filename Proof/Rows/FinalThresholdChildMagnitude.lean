import Proof.Assembly.RowProduction
import Proof.Supplier.RowThresholdSelections

/-! The exact magnitude of one native top child, before canonical stacking.
The actual weights and original target are scanned on an explicit all-true
mask. This is distinct from the frozen-assignment mask used for hardwiring.
The child locator, mask/count/width and retained bank are physical callers. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdChildMagnitude
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.ThresholdAlignedEnvelope
open NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 250000
set_option maxRecDepth 120000

def fields {n : ℕ} (g : ExactThresholdGate n) : List ℤ := List.ofFn g.weight++[g.target]
def items {n : ℕ} (g : ExactThresholdGate n) : List CloseoutRowsPoolWeight.Item :=
  (fields g).map (fun z=>(z,true))
theorem items_word {n : ℕ} (g : ExactThresholdGate n) : CloseoutRowsPoolWeight.word (items g)=exactWord g := by
  simp only [CloseoutRowsPoolWeight.word,items,List.flatMap_map]
  simp [fields,exactWord]
theorem items_magnitude {n : ℕ} (g : ExactThresholdGate n) :
    C10NaturalHardwireScore.selectedSum (items g)+CloseoutRowsPoolMinimum.liveSum (items g)=
      childMagnitude g := by
  have halves (z : Int) : z.toNat+(-z).toNat=z.natAbs := by omega
  simp only [C10NaturalHardwireScore.selectedSum,CloseoutRowsPoolMinimum.liveSum,items,
    List.map_map,Function.comp_def,ite_true,←List.sum_append]
  rw [List.sum_append]
  rw [←List.sum_map_add]
  simp only [halves,fields,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Nat.add_zero,List.map_ofFn,List.sum_ofFn]
  rfl

noncomputable def machine := Composition.machine C10NaturalHardwireScoreInputs.machine
  (RecoveryFocus.machine (![13,14,15,16,17] : Fin 5 → Fin 44) MatrixScoreAccumulate.machine)
def budget {n : ℕ} (g : ExactThresholdGate n) (w C : ℕ) :=
  C10NaturalHardwireScoreInputs.budget (items g) w C+12*w+14

end NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdChildMagnitude
