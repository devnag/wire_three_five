import Proof.MachineModel.OrdinaryMatrixWilliamsHeaderEntry

/-! Produce the actual raw-matrix bit count U*Capacity from the two
retained sentinels, paying their head adjustment and the complete product. -/
namespace NearCubicWires.RepairOrdinary.MatrixWilliamsDimensions
open LocalBitMultitape RecoveryExecution MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def retreat : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => none,
    fun i => if i=0 ∨ i=5 then .left else .stay⟩ else none
noncomputable def countMachine := Composition.machine retreat MatrixTemplateProduct.machine
noncomputable def countEntry (d e : ℕ) : Configuration 12 23 :=
  ⟨countMachine.start,fun i => if i=0 ∨ i=5 then 1 else 0,MatrixTemplateProduct.input d e⟩

theorem count_run (d e : ℕ) : ∃ actual,
    runFrom countMachine (8*d*e+10*d+30) (countEntry d e)=some actual ∧
    actual.final.tapes 0=UnaryTemplate.tape d ∧ actual.final.tapes 5=UnaryTemplate.tape e ∧
    actual.final.tapes 10=UnaryTemplate.tape (d*e) ∧
    (∀ i,actual.final.heads i=0) ∧ actual.steps=8*d*e+10*d+30 := by
  let entry : Configuration 12 2 := ⟨0,fun i => if i=0 ∨ i=5 then 1 else 0,MatrixTemplateProduct.input d e⟩
  let done : Configuration 12 2 := ⟨1,fun _ => 0,MatrixTemplateProduct.input d e⟩
  have hstep : step retreat entry=some done := by
    simp [step,retreat,entry]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  obtain ⟨base,hb,bf,bs⟩ := (Timed.single (by rfl) hstep).run (by rfl)
  obtain ⟨body,hr,b0,b5,b10,bh,bt⟩ := MatrixTemplateProduct.product_run d e
  have hi : initialConfiguration MatrixTemplateProduct.machine (MatrixTemplateProduct.input d e)=
      Composition.restart base.final MatrixTemplateProduct.machine.start := by rw [bf]; rfl
  unfold run at hr
  rw [hi] at hr
  have hj := Composition.run_join retreat MatrixTemplateProduct.machine _ _ _ base body hb hr
  have ht : 1+1+(8*d*e+10*d+28)=8*d*e+10*d+30 := by omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt base body,hj,b0,b5,b10,bh,?_⟩
  change base.steps+1+body.steps=_
  omega

noncomputable def budget (r : Request) := MatrixWilliamsHeaderEntry.budget r+1+(8*r.U*r.Capacity+10*r.U+30)

end NearCubicWires.RepairOrdinary.MatrixWilliamsDimensions
