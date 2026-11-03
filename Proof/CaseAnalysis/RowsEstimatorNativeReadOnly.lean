import Proof.CaseAnalysis.CloseoutRowsEstimatorRetained
import Proof.CaseAnalysis.CaseTwoAddressRetention

/-! The original native cut bytes are read-only throughout the estimator.
Together with the returned zero head this preserves the native C support
needed by the enclosing row-generation bank's own paid clear. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.NativeReadOnly
open LocalBitMultitape RepairRepresentation RepairSource.RecoveryTseitinReadOnly
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem header : NoWrite Header.machine 52:=by
  apply composition
  · intro q bits a ha
    obtain ⟨b,_hb,he⟩:=Option.map_eq_some_iff.mp ha
    subst a
    change (TapeEmbedding.action 3 b).write ((0 : Fin 3).natAdd 52)=none
    simp only [TapeEmbedding.action,Fin.addCases_right]
  · change NoWrite (RecoveryFocus.machine Header.slots Tail.machine) (Header.slots 0)
    apply focus _ (by decide)
    intro q bits a ha
    simp only [Tail.machine] at ha
    split_ifs at ha <;>cases ha <;>rfl


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.NativeReadOnly
