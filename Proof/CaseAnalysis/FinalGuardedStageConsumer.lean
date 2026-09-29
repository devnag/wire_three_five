import Proof.CaseAnalysis.FinalPipeline
import Proof.CaseAnalysis.FinalTailComposeVerdict

/-! Local adapters for paper C.10's syntactic rejection path. They preserve
actual machine, input, exit and fuel. Physical admission/cache and continuation
receipts remain explicit; none is supplied by this module. The fixed onset may
exceed the source's soundness cutoff. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer
open LocalBitMultitape RepairOrdinary RepairOrdinary.CloseoutWitness
open RepairRepresentation CompetitorRationalGap ExtDecompositionBatch
open CloseoutRowsOriginalSchedule SelectedRecoveryIntegration CloseoutLanguage SourceInterfaces
open C10LengthGate C10Verdict C10Fusion
open RepairOrdinary.CloseoutFinalC10Realizes

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-- The existing one-step physical decision switch after the actual admission
admission. Failure writes false and halts; success continues from the exact cache. -/
def admittedInner {t a b : ℕ} (admission : Machine t a) (continuation : Machine t b)
    (admissionFlag result : Fin t) :=
  Composition.machine admission (branch admissionFlag result continuation)

/-- One fixed larger onset, followed by the actual admission/continuation code. -/
def admittedWorker {t a b : ℕ} (onset : ℕ) (admission : Machine t a)
    (continuation : Machine t b) (input lengthFlag admissionFlag result : Fin t) :=
  gated onset input lengthFlag result (admittedInner admission continuation admissionFlag result)

theorem inner_reject {t a b : ℕ} (admission : Machine t a) (continuation : Machine t b)
    (admissionFlag result : Fin t) (preFuel : ℕ)
    (H Hpre : Fin t → ℕ) (T Tpre : Fin t → List Bool)
    (hpre : Step admission preFuel H T Hpre Tpre)
    (hfalse : readTapeBit (Tpre admissionFlag) (Hpre admissionFlag) = false) :
    Step (admittedInner admission continuation admissionFlag result) (preFuel+1+1)
      H T Hpre (exitTapes result Tpre (Hpre result) false) :=
  hpre.seq (branch_reject admissionFlag result continuation Hpre Tpre hfalse)

end
end NearCubicWires.RepairSource.CloseoutFinal.C10GuardedStageConsumer
