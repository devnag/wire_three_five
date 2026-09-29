import Proof.PCP.PCPPQueryClauseHeader
import Proof.PCP.PCPPQuerySupportSemantics

/-! The physically decoded systematic-bit count drives the complete skip
of the explicit support matrix. The source stops at the literal-list count
header, retaining the query index and reusable natural-field scratch. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseMatrix
open LocalBitMultitape RepairSource.VerifierDecoding PCPPQueryField
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def skipEntry (source : List Bool) (pos arity count : ℕ) :
    Configuration 4 (Fintype.card (RepeatMachine.Control 5)) :=
  ⟨PCPPQueryRows.skip.start,![1,pos,0,1],![UnaryTemplate.tape arity,source,[],UnaryTemplate.tape count]⟩
def skipCapacity (count : ℕ) : Fin 4→ℕ := fun i => if i=3 then count+2 else 0

theorem skip_run (pre : List Bool) (rows : List (List Bool)) (tail : List Bool) (arity : ℕ)
    (hw : ∀ r∈rows,r.length=arity) :
    ∃ r,runFrom PCPPQueryRows.skip (rows.length*(2*arity+7)+3)
      (skipEntry (pre++rows.flatten++tail) pre.length arity rows.length)=some r ∧
      r.final.tapes=![UnaryTemplate.tape arity,pre++rows.flatten++tail,[],UnaryTemplate.tape rows.length] ∧
      r.final.heads=![1,pre.length+rows.flatten.length,0,1] ∧
      r.steps=rows.length*(2*arity+7)+3 := by
  obtain ⟨base,hb,hbf,hbs⟩ := PCPPQueryRows.skip_run arity pre rows tail [] hw
  obtain ⟨r,hr,hf,hs,_⟩ := ZeroPadding.run_config PCPPQueryRows.skip (skipCapacity rows.length) _ _ base hb
  have he : ZeroPadding.config (skipCapacity rows.length)
      (PCPPQueryRows.cfg 0 arity (pre++rows.flatten++tail) pre.length [] rows.length 1)=
      skipEntry (pre++rows.flatten++tail) pre.length arity rows.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,skipCapacity,PCPPQueryRows.cfg,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,
        skipEntry,PCPPQuerySupport.template_pad]
  rw [he] at hr
  refine ⟨r,hr,?_,?_,hs.trans hbs⟩
  · rw [hf,hbf]
    funext i; fin_cases i <;> simp [ZeroPadding.config,skipCapacity,PCPPQueryRows.cfg,
      RepeatMachine.cfg,controlConfig,TapeEmbedding.config,MatrixRawBlock.config,Fin.addCases,PCPPQuerySupport.template_pad]
  · rw [hf,hbf]
    funext i; fin_cases i <;> rfl

def slots : Fin 4→Fin 16 := ![13,0,12,10]
noncomputable def scan := RecoveryFocus.machine slots PCPPQueryRows.skip
noncomputable def machine := Composition.machine PCPPQueryClauseHeader.machine scan
def budget (a b c arity : ℕ) := PCPPQueryClauseHeader.budget a b c+a*(2*arity+7)+4

end NearCubicWires.RepairOrdinary.PCPPQueryClauseMatrix
