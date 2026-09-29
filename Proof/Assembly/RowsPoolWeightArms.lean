import Proof.CaseAnalysis.RowsRawAtomSeek

/-! The actual constant-gate request uses the original native weight at
frozen coordinates and a literal zero at live coordinates. These two
workers consume the SAME width-delimited integer; no integer magnitude
is expanded into unary and no canonical field is parsed again. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos mpos : ℕ) (out : List Bool) : Fin 4→ℕ:=![pos,0,out.length,mpos]
def data (source backing out mask : List Bool) : Fin 4→List Bool:=![source,backing,out,mask]
noncomputable def copy:=TapeEmbedding.machine 1 DecompositionSource.Fields.machine
noncomputable def skip:=TapeEmbedding.machine 1 RowNativeFieldSkip.machine
def zeroSlots : Fin 1→Fin 4:=fun _=>2
noncomputable def zero:=RecoveryFocus.machine zeroSlots (HierarchyFixedWord.raw (intWord 0))
noncomputable def replaced:=Composition.machine skip zero

theorem copy_run (pre tail backing out mask : List Bool) (mpos : ℕ) (z : ℤ) :
    Step copy (DecompositionSource.Fields.cost z) (heads pre.length mpos out)
      (data (pre++intWord z++tail) backing out mask)
      (heads (pre.length+(intWord z).length) mpos (out++intWord z))
      (data (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing) (out++intWord z) mask) := by
  obtain ⟨r,hr,hf,_⟩:=DecompositionSource.Fields.int_run pre tail backing out z
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have all:=h.embed (fun _ : Fin 1=>mpos) (fun _ : Fin 1=>mask)
  apply (all.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

theorem skip_run (pre tail backing out mask : List Bool) (mpos : ℕ) (z : ℤ) :
    Step skip (RowNativeFieldSkip.cost z) (heads pre.length mpos out)
      (data (pre++intWord z++tail) backing out mask)
      (heads (pre.length+(intWord z).length) mpos out)
      (data (pre++intWord z++tail) (DecompositionSource.Fields.saved z backing) out mask) := by
  obtain ⟨r,hr,hf,_⟩:=RowNativeFieldSkip.int_run pre tail backing out z
  have h:=Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)
  have all:=h.embed (fun _ : Fin 1=>mpos) (fun _ : Fin 1=>mask)
  apply (all.congr_in ?_ ?_).congr ?_ ?_
  all_goals funext i;fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
