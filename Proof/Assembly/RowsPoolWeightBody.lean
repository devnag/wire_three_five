import Proof.Assembly.RowsPoolWeightChoice

/-! One original coordinate consumes exactly one live-mask bit. Its native
width scratch is retained for the next actual integer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def advance : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun _ _=>some ⟨1,fun _=>none,fun i=>if i=3 then .right else .stay⟩
noncomputable def body:=Composition.machine choice advance

theorem advance_run (source backing out mask : List Bool) (pos mpos : ℕ) :
    Step advance 1 (heads pos mpos out) (data source backing out mask)
      (heads pos (mpos+1) out) (data source backing out mask):=by
  have h:step advance ⟨0,heads pos mpos out,data source backing out mask⟩=
      some ⟨1,heads pos (mpos+1) out,data source backing out mask⟩:=by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · rfl
  obtain ⟨r,hr,hf,_⟩:=(Timed.single (by rfl) h).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads hf) (congrArg Configuration.tapes hf)

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolWeight
