import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsDegreeRange

/-! The executed degree loop prints exactly one polynomial's complete
signed-cut word, in the permitted positional order and with every duplicate
monomial occurrence retained. Its output cursor remains at the append end. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPolynomial
open LocalBitMultitape CloseoutRowsLoopLayout CloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := CloseoutRowsDegreeBody.machine worker
noncomputable def machine := CloseoutRowsDegreeLoop.machine body
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n))
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  RepeatMachine.cfg 0 (CloseoutRowsDegreeLoop.entry body gs p F w 0 C rows out) Q 1

end NearCubicWires.RepairOrdinary.CloseoutRowsPolynomial
