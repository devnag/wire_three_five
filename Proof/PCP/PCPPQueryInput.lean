import Proof.PCP.PCPPQueryFieldChain

/-! Explicit local framing of query requests. The imported PCPP constructor
keeps its original codec. A physical copy isolates precisely that framed
constructor input and leaves the query cursor at the appended natural index.
The older unframed local query record has no banked inhabitant and is not
used by this adapter. -/
namespace NearCubicWires.RepairRepresentation
open RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.RepairRepresentation

namespace NearCubicWires.RepairOrdinary.PCPPQueryInput
open LocalBitMultitape RecoveryExecution RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 2) : Bool := decide (i=1)
def isolate := MaskedReset.machine Field.machine selected
def entry (source : List Bool) (pos : ℕ) : Configuration 3 5 :=
  Rewind.recording (Field.cfg 0 source pos []) 0
def isolated (source : List Bool) (pos : ℕ) (bits : List Bool) : Configuration 3 5 :=
  ⟨4,![pos,0,0],![source,frame bits,List.replicate (2*bits.length+1) false]⟩

theorem isolate_run (pre bits tail : List Bool) :
    ∃ r,runFrom isolate (4*bits.length+4)
      (entry (pre++frame bits++tail) pre.length)=some r ∧
      r.final=isolated (pre++frame bits++tail) (pre.length+2*bits.length+1) bits ∧
      r.steps=4*bits.length+4 := by
  obtain ⟨base,hb,hbf,hbs⟩ := Field.copy_run pre bits tail []
  have hh : ∀ i,selected i=true → base.final.heads i≤base.steps := by
    intro i hi
    have he : i=1 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    rw [hbf,hbs]
    simp [Field.cfg]
  obtain ⟨r,hr,hf,hs,_⟩ := MaskedReset.reset_run Field.machine selected _ _ base hb hh
  have htime : 2*base.steps+2=4*bits.length+4 := by rw [hbs]; omega
  rw [htime] at hr hs
  refine ⟨r,hr,?_,hs⟩
  rw [hf,hbf,hbs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,selected,Field.cfg,isolated,Fin.addCases]
  · funext i; fin_cases i <;>
      simp [SelectiveReset.finished,Rewind.config,Field.cfg,isolated,Fin.addCases]

def budget (bits tail : List Bool) := 4*(frame bits++tail).length+4*bits.length+7

end NearCubicWires.RepairOrdinary.PCPPQueryInput
