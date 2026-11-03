import Proof.Supplier.RowNativeFieldSkip
import Proof.Circuits.DecompositionCachedChildAccess

/-! Physical access to a weight or the target of the selected native child.
Coordinates retain occurrence order, with the target at the actual arity. -/
namespace NearCubicWires.RepairOrdinary.RowNativeCoordinate
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields {n : ℕ} (g : ExactThresholdGate n) := List.ofFn g.weight++[g.target]
theorem fields_length {n : ℕ} (g : ExactThresholdGate n) : (fields g).length=n+1 := by simp [fields]
theorem word_fields {n : ℕ} (g : ExactThresholdGate n) : exactWord g=(fields g).flatMap intWord := by
  simp [fields,exactWord]
def prior {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) := ((fields g).take i).flatMap intWord
def suffix {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) := ((fields g).drop (i+1)).flatMap intWord
def value {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n) : ℤ :=
  (fields g)[i]'(by rw [fields_length]; omega)

theorem selected_word {n : ℕ} (g : ExactThresholdGate n) (i : ℕ) (hi : i≤n) :
    exactWord g=prior g i++intWord (value g i hi)++suffix g i := by
  have hlt : i<(fields g).length := by rw [fields_length]; omega
  have h : (fields g).take i++(fields g)[i]::(fields g).drop (i+1)=fields g := by
    rw [←List.drop_eq_getElem_cons hlt]
    exact List.take_append_drop i (fields g)
  have he := congrArg (fun zs : List ℤ => zs.flatMap intWord) h
  simpa only [word_fields,prior,suffix,value,List.flatMap_append,List.flatMap_cons,List.append_assoc] using he.symm

noncomputable def machine := RowNativeFieldSkip.loop

end NearCubicWires.RepairOrdinary.RowNativeCoordinate
