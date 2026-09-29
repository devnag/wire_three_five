import Proof.Supplier.RowTupleLimit

/-! The complete tuple enumerator now derives its terminal field and extent
from the runtime width and degree. The only supplied metadata are width,
degree and the actual cache-size bound; no exponential-length driver is input. -/
namespace NearCubicWires.RepairOrdinary.RowTupleDerivedEnumeration
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open CompetitorRationalProducts RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def productSlots : Fin 4→Fin 40 := ![18,12,29,30]
def limitSlots : Fin 12→Fin 40 := ![29,14,31,32,33,34,35,36,37,38,25,39]
def rowSlots (i : Fin 29) : Fin 40 := i.castAdd 11
noncomputable def product := RecoveryFocus.machine productSlots ClockUnaryProduct.machine
noncomputable def limit := RecoveryFocus.machine limitSlots RowTupleLimit.machine
noncomputable def metadata := Composition.machine product limit
noncomputable def enumeration := RecoveryFocus.machine rowSlots RowTupleColdEnumeration.machine
noncomputable def machine := Composition.machine metadata enumeration
def productTime (w k : ℕ) := 2*(w*(2*k+3)+2)+2
def productInput (w k : ℕ) : Fin 4→List Bool :=
  ![List.replicate w true,CompareMachine.word k,[],[]]
def productOutput (w k : ℕ) : Fin 4→List Bool :=
  ![List.replicate w true,CompareMachine.word k,List.replicate (w*k) true,
    List.replicate (w*(2*k+3)+2) false]

theorem product_ready (w k : ℕ) : ClockJoin.ReadyRun ClockUnaryProduct.machine
    (productTime w k) (productInput w k) (productOutput w k) := by
  obtain ⟨r,hr,h0,h1,h2,h3,hh,hs⟩ := ClockUnaryProduct.product_run w k
  have hi : Fin.addCases (motive := fun _ : Fin (3+1)=>List Bool)
      ![List.replicate w true,false::List.replicate k true,[]] (fun _ : Fin 1=>[])=productInput w k := by
    funext i; fin_cases i <;> rfl
  rw [hi] at hr
  refine ⟨r,hr,?_,hh,hs.le⟩
  funext i; fin_cases i <;> simp [productOutput,h0,h1,h2,h3,CompareMachine.word]

end NearCubicWires.RepairOrdinary.RowTupleDerivedEnumeration
