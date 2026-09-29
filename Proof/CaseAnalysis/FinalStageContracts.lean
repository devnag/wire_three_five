import Proof.CaseAnalysis.FinalStageWidths
import Proof.Circuits.PolynomialOrdinaryClock

/-! Paper C.10: "The machine passes validity only if the first estimated average
is at most 2ζ and all estimated second moments are at most 1+ζ." C.10.1 accepts
only when the estimated acceptance mean is at least (c_p+s_p)/2. This constructor
fuses those tests, the phase realizations, and halting into the same fixed run.
The supplier obligations are precisely S2's stage contract and the semantic
hypotheses of realizes_of_stage; native parity, decoding, copies, and the tail
are constructed here. The approved R3 fallback uses StageData.budget, bounded
by StageBlock.hfuel. A conditional constructor does not inhabit its premises. -/
namespace NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform

open LocalBitMultitape ExtDecompositionBatch ComponentwisePolynomial
open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation SourceInterfaces SupplierPipeline
open CompetitorRationalGap CloseoutRowsOriginalSchedule
open RepairOrdinary.CloseoutFinalC10Exactness RepairOrdinary.CloseoutFinalC10Realizes
open RepairOrdinary.CloseoutFinalC10WorkerChain RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10WorkerDockSeam RepairOrdinary.CloseoutFinalC10WorkerFold
open RepairOrdinary.CloseoutFinalC10WorkerEmitLoader RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open RepairOrdinary.CloseoutFinalC10StageSeam RepairOrdinary.CloseoutFinalC10SupplierCalls
open RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open C10Verdict C10LengthGate C10TailCompose C10BodyWidths C10TailComposeVerdict

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section



variable (sources : EightSources) (k : ℕ)

/-- The decoded PCPP at the guess.  The oracle is `oracleOf` at the closure
parameters' own general-oracle exponent `p.degree` -- paper C.10's `G`
(`paper.tex:4283`) -- so the branch the machine runs on is the one that passes
the fixed general-circuit size bound (`paper.tex:4292`).  Carrying `p` rather
than a free exponent is what makes `pinnedSym_of_stage` able to present
`SymDecidesFrom`'s size hypothesis at the same `degree` the consumer's
`selected_oracle_small` (`Proof/CaseAnalysis/FinalEncoder.lean`) supplies. -/
def pcppOf {gamma : ℝ} (p : Parameters sources gamma) {n : ℕ} (x : BitInput n) (bits : List Bool) :=
  pcppAt sources k (PolynomialClock.ordinaryClock k) x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits)

def Atoms {gamma : ℝ} (p : Parameters sources gamma) {n : ℕ} (x : BitInput n) (bits : List Bool) :=
  C10TotalDecode.Atom (pcppOf sources k p x bits)

abbrev proofOf {gamma : ℝ} (p : Parameters sources gamma) {n : ℕ} (x : BitInput n) (bits : List Bool) :=
  C10TotalDecode.proofValueOf sources k (PolynomialClock.ordinaryClock k) p x
    (C10TotalDecode.oracleOf sources k (PolynomialClock.ordinaryClock k) p.degree n bits) bits

attribute [local irreducible] pcppOf Atoms

structure StageData {gamma : ℝ} (p : Parameters sources gamma) : Type 1 where
  e : ℕ
  st : Phase → ℕ
  stage : (ph : Phase) → LocalBitMultitape.Machine (218+e) (st ph)
  stageFuel : Phase → ℕ → ℕ
  entryWidth : ℕ → ℕ
  denominator : ℕ → ℕ
  coordinate : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin ((pcppOf sources k p x bits).systematicBits+(pcppOf sources k p x bits).auxiliaryBits) →
      CircuitPolynomial (Atoms sources k p x bits) 1
  supplier : (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ
  answer : (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℕ
  failure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  mass : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  L : ℕ → ℕ
  budget : ℕ → ℕ

attribute [local semireducible] pcppOf Atoms

variable {gamma : ℝ} (p : Parameters sources gamma) (S : StageData sources k p)

abbrev records {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  phaseRecords (S.answer n x bits) (S.denominator n) ph (pcppOf sources k p x bits)
    (S.coordinate n x bits) C10TotalDecode.Atom.systematic

def widthOf {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  foldWidth (CompetitorRationalDecision.width (S.entryWidth n)) (records sources k p S x bits ph)

def emissionFuel {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) : ℕ → ℕ :=
  fun _ => emitFuel (joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length)

def body (ph : Phase) := stagedBody (S.stage ph) emitLoader

def phaseFuel {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) : ℕ :=
  stagedFuel (S.stageFuel ph) (emissionFuel sources k p S x bits ph) (S.entryWidth n)
    (records sources k p S x bits ph).length n

def actualFuel {n : ℕ} (x : BitInput n) (bits : List Bool) : ℕ :=
  workerBudget (Soundness.cutoff (constantsOf sources))
    (fun _ => C10ComposeWidths.innerFuel (phaseFuel sources k p S x bits)
      (widthOf sources k p S x bits) C10TailVerdictUniform.tbud) n

/-- Exactly S2's prepared stage bank, plus the two retained width words. -/
structure StageReady (he : 58 ≤ S.e) {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (bank : Fin 218 → List Bool) (scratch : Fin S.e → List Bool) : Prop where
  hstage : Step (S.stage ph) (S.stageFuel ph n) (fun _ => 0)
    (exitTapes (Fin.castAdd S.e flag)
      ((UAcceptanceCarrier.verifier
        (worker (Soundness.cutoff (constantsOf sources)) (Fin.castAdd S.e inputTape)
          (Fin.castAdd S.e flag) (Fin.castAdd S.e result) (body sources k p S ph))
        (by omega) (Fin.castAdd S.e result)).inputTapes (List.ofFn x) bits) 0 true)
    (fun _ => 0) (Fin.addCases bank scratch)
  hready : DockReady (S.entryWidth n) (records sources k p S x bits ph) bank
  hentry : EmitEntry (joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length) bank
  h0 : bank 0 = frame (List.ofFn x)
  h1 : bank 1 = frame bits
  hemit : emissionFuel sources k p S x bits ph =
    fun _ => emitFuel (joinScalarWidth (S.entryWidth n) (records sources k p S x bits ph).length)
  hwidth : ∀ j, Fin.addCases bank scratch (retained S.e he j) = widthWord (widthOf sources k p S x bits ph) j

structure StageBlock : Prop where
  he : 58 ≤ S.e
  hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, ∃ bank scratch, StageReady sources k p S he x bits ph bank scratch
  hcoordinate : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    CoordinateExpands (pcppOf sources k p x bits) C10TotalDecode.evaluate (proofOf sources k p x bits) (S.coordinate n x bits)
  hsupplier : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ factors, (S.answer n x bits factors : ℚ)/(S.denominator n : ℚ) = S.supplier n x bits factors
  hcount : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ factors, S.answer n x bits factors < 2^(S.entryWidth n)
  hdenominator : ∀ n, Soundness.cutoff (constantsOf sources) ≤ n → S.denominator n < 2^(S.entryWidth n)
  hdenominatorPositive : ∀ n, Soundness.cutoff (constantsOf sources) ≤ n → 0 < S.denominator n
  hcoefficients : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address, CoefficientsFit (S.entryWidth n)
      (siteCalls ph (pcppOf sources k p x bits) (S.coordinate n x bits) C10TotalDecode.Atom.systematic address)
  hfailure : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, 0 ≤ S.failure n x bits ph
  hpoint : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph circuits, |((S.supplier n x bits circuits : ℚ) : ℝ)-conjunctionProbability C10TotalDecode.evaluate circuits| ≤ S.failure n x bits ph
  hmass : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, (((phasePolynomial ph (pcppOf sources k p x bits) (S.coordinate n x bits)
      C10TotalDecode.Atom.systematic).coefficientMass : ℚ) : ℝ) ≤ S.mass n x bits ph
  haccuracy : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, S.failure n x bits ph * S.mass n x bits ph ≤
      ((estimationTolerance (constantsOf sources) (zeta (constantsOf sources)) : ℚ) : ℝ)
  hthreshold : ∀ n, C10ThresholdWidths.thresholdWidth (constantsOf sources) ≤ S.entryWidth n
  hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool), actualFuel sources k p S x bits ≤ S.budget n


end
end NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
