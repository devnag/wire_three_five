import Proof.CaseAnalysis.FinalFuelMajorant
import Proof.CaseAnalysis.FinalLogFitFull
import Proof.CaseAnalysis.FinalResidualLeaves
import Proof.CaseAnalysis.FinalSupplierFuel
import Proof.CaseAnalysis.FinalStageFields

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound (fuelAt actualFuel_eq
  fuelAt_mono)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate
  stageMass)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDock
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitLoader
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmitShape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10BodyWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeVerdict
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode
open NearCubicWires.RepairSource.CloseoutFinal.C10Verdict
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource
open NearCubicWires.RepairSource.CloseoutFinal (constantsOf Parameters Runtime Theorem25Target
  theorem25_of_leaves)
open NearCubicWires.RepairOrdinary.CompetitorSourceAverage
open NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10DecidesUniform
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CircuitRestriction
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.RepairSource.CloseoutFinal.C10Fusion (Pipeline)
open NearCubicWires.RepairSource.CloseoutFinal.C10ComposeWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10StageWidths
open NearCubicWires.RepairSource.CloseoutFinal.C10TailVerdictUniform (tbud tailWidths'_of)
open NearCubicWires.RepairSource.CloseoutFinal.C10ThresholdWidths (thresholdWidth)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierWidth (rowAnswer_le_rowDenominator)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (sources : EightSources) (k : ℕ)

attribute [local irreducible] pcppOf Atoms

/-- **The stage's data at the paper's own per-call fraction.**  Field for field
`StageData` (`Proof/CaseAnalysis/FinalStageContracts.lean`), except that the pair
`answer : ... → List Atom → ℕ` (`:79`) and `denominator : ℕ → ℕ` (`:74`) is replaced
by the numerator/denominator pair `exactFractionRecord`
(`Proof/CaseAnalysis/FinalExactFraction.lean`) consumes: one pair per PCPP
clause address and monomial.  `den` is A.13.9's `|\mathcal E| 2 ^ q`
(`paper.tex:3161`), i.e. `rowDenominator`
(`Proof/CaseAnalysis/FinalSupplierAccuracy.lean`), which is a function of the
request and therefore cannot be a `ℕ → ℕ`. -/
structure StageData' {gamma : ℝ} (p : Parameters sources gamma) :
    Type 1 where
  e : ℕ
  st : Phase → ℕ
  stage : (ph : Phase) → LocalBitMultitape.Machine (218+e) (st ph)
  stageFuel : Phase → ℕ → ℕ
  entryWidth : ℕ → ℕ
  num : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ
  den : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → ℕ
  coordinate : (n : ℕ) → (x : BitInput n) → (bits : List Bool) →
    Fin ((pcppOf sources k p x bits).systematicBits+(pcppOf sources k p x bits).auxiliaryBits) →
      CircuitPolynomial (Atoms sources k p x bits) 1
  supplier : (n : ℕ) → (x : BitInput n) → (bits : List Bool) → List (Atoms sources k p x bits) → ℚ
  failure : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  mass : (n : ℕ) → BitInput n → List Bool → Phase → ℝ
  L : ℕ → ℕ
  budget : ℕ → ℕ

attribute [local semireducible] pcppOf Atoms

variable {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData' sources k p)

/-- The emitted record stream, at A.13.9's own fraction.  `records`
(`Proof/CaseAnalysis/FinalStageContracts.lean`) with `phaseRecords` replaced by
`phaseRecords'` (`Proof/CaseAnalysis/FinalExactFraction.lean`). -/
abbrev records' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  phaseRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits) Atom.systematic
    (exactFractionRecord (2 ^ (pcppOf sources k p x bits).clauseBits) (S.num n x bits)
      (S.den n x bits))

/-- `widthOf` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def widthOf' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :=
  foldWidth (CompetitorRationalDecision.width (S.entryWidth n))
    (records' sources k p S x bits ph)

/-- `emissionFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def emissionFuel' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) : ℕ → ℕ :=
  fun _ => emitFuel (joinScalarWidth (S.entryWidth n) (records' sources k p S x bits ph).length)

/-- `body` (`Proof/CaseAnalysis/FinalStageContracts.lean`), unchanged in kind. -/
def body' (ph : Phase) := stagedBody (S.stage ph) emitLoader

/-- `phaseFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def phaseFuel' {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) : ℕ :=
  stagedFuel (S.stageFuel ph) (emissionFuel' sources k p S x bits ph) (S.entryWidth n)
    (records' sources k p S x bits ph).length n

/-- `actualFuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) at `records'`. -/
def actualFuel' {n : ℕ} (x : BitInput n) (bits : List Bool) : ℕ :=
  workerBudget (Soundness.cutoff (constantsOf sources))
    (fun _ => innerFuel (phaseFuel' sources k p S x bits)
      (widthOf' sources k p S x bits) tbud) n

structure StageReady' (he : 58 ≤ S.e) {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase)
    (bank : Fin 218 → List Bool) (scratch : Fin S.e → List Bool) : Prop where
  hstage : Step (S.stage ph) (S.stageFuel ph n) (fun _ => 0)
    (exitTapes (Fin.castAdd S.e flag)
      ((UAcceptanceCarrier.verifier
        (worker (Soundness.cutoff (constantsOf sources)) (Fin.castAdd S.e inputTape)
          (Fin.castAdd S.e flag) (Fin.castAdd S.e result) (body' sources k p S ph))
        (by omega) (Fin.castAdd S.e result)).inputTapes (List.ofFn x) bits) 0 true)
    (fun _ => 0) (Fin.addCases bank scratch)
  hready : DockReady (S.entryWidth n) (records' sources k p S x bits ph) bank
  hentry : EmitEntry (joinScalarWidth (S.entryWidth n)
    (records' sources k p S x bits ph).length) bank
  h0 : bank 0 = frame (List.ofFn x)
  h1 : bank 1 = frame bits
  hemit : emissionFuel' sources k p S x bits ph =
    fun _ => emitFuel (joinScalarWidth (S.entryWidth n) (records' sources k p S x bits ph).length)
  hwidth : ∀ j, Fin.addCases bank scratch (retained S.e he j) =
    widthWord (widthOf' sources k p S x bits ph) j

structure StageBlock' : Prop where
  he : 58 ≤ S.e
  hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, ∃ bank scratch, StageReady' sources k p S he x bits ph bank scratch
  hcoordinate : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    CoordinateExpands (pcppOf sources k p x bits) evaluate (proofOf sources k p x bits)
      (S.coordinate n x bits)
  hratio : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ address monomial, ((S.num n x bits address monomial : ℚ) /
      (S.den n x bits address monomial : ℚ)) = S.supplier n x bits monomial.factors
  hnum : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address monomial,
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (S.coordinate n x bits) Atom.systematic address).monomials →
      S.num n x bits address monomial < 2^(S.entryWidth n)
  hden : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address monomial,
      monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
        (S.coordinate n x bits) Atom.systematic address).monomials →
      S.den n x bits address monomial < 2^(S.entryWidth n)
  hdenPos : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ address monomial, 0 < S.den n x bits address monomial
  hcoefficients : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph address, CoefficientsFit (S.entryWidth n)
      (siteCalls ph (pcppOf sources k p x bits) (S.coordinate n x bits) Atom.systematic address)
  hfailure : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph, 0 ≤ S.failure n x bits ph
  hpoint : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph circuits, |((S.supplier n x bits circuits : ℚ) : ℝ) -
      conjunctionProbability evaluate circuits| ≤ S.failure n x bits ph
  hmass : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, (((phasePolynomial ph (pcppOf sources k p x bits) (S.coordinate n x bits)
      Atom.systematic).coefficientMass : ℚ) : ℝ) ≤ S.mass n x bits ph
  haccuracy : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    Soundness.cutoff (constantsOf sources) ≤ n →
    ∀ ph, S.failure n x bits ph * S.mass n x bits ph ≤
      ((estimationTolerance (constantsOf sources) (zeta (constantsOf sources)) : ℚ) : ℝ)
  hthreshold : ∀ n, thresholdWidth (constantsOf sources) ≤ S.entryWidth n
  hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
    actualFuel' sources k p S x bits ≤ S.budget n

end

noncomputable section
variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)
  (S : StageData' sources k p)

/-! ## §6 The capstone anti-fork receipt -/

/-! **What is NOT compiled here, stated exactly.**  The three remaining data-level
identities -- `rawRealizes'` vs `rawRealizes`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`), `verdict_of_stage'` vs
`verdict_of_stage` (`:145`), and `machine_of_stage'` vs `machine_of_stage`
(`Proof/CaseAnalysis/FinalPipelineOfStage.lean`) -- are STATED at inputs this file
proves definitionally equal, but each was rejected by Lean as
`(deterministic) timeout at isDefEq` under the strict profile's 250000 heartbeats.
That is a budget fact about the size of the unfolding, not a counterexample, and
raising the limit is prohibited; the identities above `Realizes` are therefore
recorded as UNCHECKED rather than claimed. -/

def shell : StageData sources k p where
  e := S.e
  st := S.st
  stage := S.stage
  stageFuel := S.stageFuel
  entryWidth := S.entryWidth
  denominator := fun _ => 1
  coordinate := S.coordinate
  supplier := S.supplier
  answer := fun _ _ _ _ => 0
  failure := S.failure
  mass := S.mass
  L := S.L
  budget := S.budget

/-- **The record COUNT is blind to the record function.** -/
theorem records'_length_shell {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    (records' sources k p S x bits ph).length
      = (records sources k p (shell sources k p S) x bits ph).length := by
  simp [phaseRecords', phaseRecords, siteRecords, callRecords, shell]

/-- The fold width agrees with the shell's. -/
theorem widthOf'_shell {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    widthOf' sources k p S x bits ph = widthOf sources k p (shell sources k p S) x bits ph := by
  unfold widthOf' widthOf
  rw [foldWidth_eq_joinScalarWidth, foldWidth_eq_joinScalarWidth,
    records'_length_shell sources k p S x bits ph]
  rfl

/-- The phase fuel agrees with the shell's. -/
theorem phaseFuel'_shell {n : ℕ} (x : BitInput n) (bits : List Bool) (ph : Phase) :
    phaseFuel' sources k p S x bits ph = phaseFuel sources k p (shell sources k p S) x bits ph := by
  unfold phaseFuel' phaseFuel emissionFuel' emissionFuel
  rw [records'_length_shell sources k p S x bits ph]
  rfl

/-- **The whole demanded fuel agrees with the shell's**, so no fuel moves on the exact
route: `ENDGAME_RESOURCE.md` §2 has nothing to charge. -/
theorem actualFuel'_shell {n : ℕ} (x : BitInput n) (bits : List Bool) :
    actualFuel' sources k p S x bits = actualFuel sources k p (shell sources k p S) x bits := by
  have hF : phaseFuel' sources k p S x bits = phaseFuel sources k p (shell sources k p S) x bits :=
    funext (fun ph => phaseFuel'_shell sources k p S x bits ph)
  have hW : widthOf' sources k p S x bits = widthOf sources k p (shell sources k p S) x bits :=
    funext (fun ph => widthOf'_shell sources k p S x bits ph)
  unfold actualFuel' actualFuel
  rw [hF, hW]

/-- **`StageBlock'.hfuel` from a call-count cap**, the exact-route form of
`stage_field_hfuel` (`Proof/CaseAnalysis/FinalStageFields.lean`). -/
theorem hfuel'_of_cap (K : ℕ → ℕ)
    (hK : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase),
      (records' sources k p S x bits ph).length ≤ K n)
    (hbudget : ∀ n, fuelAt sources k p (shell sources k p S) n (fun _ => K n) ≤ S.budget n) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel' sources k p S x bits ≤ S.budget n := by
  intro n x bits
  rw [actualFuel'_shell sources k p S x bits,
    actualFuel_eq sources k p (shell sources k p S) x bits]
  refine (fuelAt_mono sources k p (shell sources k p S) n ?_).trans (hbudget n)
  intro ph
  rw [← records'_length_shell sources k p S x bits ph]
  exact hK n x bits ph

attribute [local irreducible] stageNum stageDen stageRowSupplier stageMass stageCoordinate
  stageEntryWidth stageArity stageTarget stageFailure

/-- **The exact-fraction stage data**: A.13.9's own numerator over its own
`|\mathcal E| 2 ^ q` (`paper.tex:3161`), per call, at STAGEFIELDS' witnesses. -/
def exactStageData (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ) (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget : ℕ → ℕ) : StageData' sources k p where
  e := 60 + extra
  st := st
  stage := stage
  stageFuel := stageFuel
  entryWidth := stageEntryWidth sources k p coefficientFloor
  num := stageNum sources k p liveScale
  den := stageDen sources k p liveScale
  coordinate := stageCoordinate sources k p
  supplier := stageRowSupplier sources k p liveScale
  failure := fun n _ _ _ =>
    1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ)
  mass := stageMass sources k p
  L := L
  budget := budget

theorem stageBlock'_of_stageFields (liveScale : ℕ) (coefficientFloor : ℕ → ℕ)
    (enum : S.num = stageNum sources k p liveScale)
    (eden : S.den = stageDen sources k p liveScale)
    (esup : S.supplier = stageRowSupplier sources k p liveScale)
    (ewidth : S.entryWidth = stageEntryWidth sources k p coefficientFloor)
    (ecoord : S.coordinate = stageCoordinate sources k p)
    (emass : S.mass = stageMass sources k p)
    (efail : S.failure = fun n _ _ _ =>
      1 / ((stageTarget sources p (stageArity sources k n) + 1 : ℕ) : ℝ))
    (he : 58 ≤ S.e)
    (ebound : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n)
    (ecoef : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            Atom.systematic address))
    (hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph, ∃ bank scratch, StageReady' sources k p S he x bits ph bank scratch)
    (hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      actualFuel' sources k p S x bits ≤ S.budget n) :
    StageBlock' sources k p S where
  he := he
  hstage := hstage
  hcoordinate := by rw [ecoord]; exact stage_field_hcoordinate sources k p
  hratio := by rw [enum, eden, esup]; exact stage_field_hratio sources k p liveScale
  hnum := by
    rw [enum, ewidth, ecoord]
    intro n x bits hn ph address monomial hmem
    apply lt_of_le_of_lt ?_ (ebound n x bits hn ph address monomial hmem)
    unfold stageNum stageDen
    exact rowAnswer_le_rowDenominator _ _ _
  hden := by rw [eden, ewidth, ecoord]; exact ebound
  hdenPos := by rw [eden]; exact stage_field_hdenPos sources k p liveScale
  hcoefficients := by rw [ewidth, ecoord]; exact ecoef
  hfailure := by
    rw [efail]
    intro n _ _ _ _
    positivity
  hpoint := by
    rw [esup, efail]
    exact fun n x bits hc _ circuits =>
      stage_field_hpoint_row sources k p liveScale n x bits hc circuits
  hmass := by rw [ecoord, emass]; exact stage_field_hmass sources k p
  haccuracy := by
    rw [efail, emass]
    exact fun n x bits hc ph => stage_field_haccuracy_row sources k p n x bits hc ph
  hthreshold := by rw [ewidth]; exact stage_field_hthreshold sources k p coefficientFloor
  hfuel := hfuel

theorem exactStageBlock (liveScale : ℕ) (coefficientFloor : ℕ → ℕ) (extra : ℕ)
    (st : Phase → ℕ)
    (stage : (ph : Phase) → LocalBitMultitape.Machine (218 + (60 + extra)) (st ph))
    (stageFuel : Phase → ℕ → ℕ) (L budget K : ℕ → ℕ) (he : 58 ≤ 60 + extra)
    (ebound : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits))
        (monomial : CircuitMonomial (Atoms sources k p x bits) 4),
        monomial ∈ (siteCalls ph (pcppOf sources k p x bits)
          (stageCoordinate sources k p n x bits) Atom.systematic address).monomials →
        stageDen sources k p liveScale n x bits address monomial
          < 2 ^ stageEntryWidth sources k p coefficientFloor n)
    (ecoef : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ (ph : Phase) (address : Fin (2 ^ (pcppOf sources k p x bits).clauseBits)),
        CoefficientsFit (stageEntryWidth sources k p coefficientFloor n)
          (siteCalls ph (pcppOf sources k p x bits) (stageCoordinate sources k p n x bits)
            Atom.systematic address))
    (hstage : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      ∀ ph, ∃ bank scratch,
        StageReady' sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) he x bits ph bank scratch)
    (hK : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool) (ph : Phase),
      (records' sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) x bits ph).length ≤ K n)
    (hbudget : ∀ n, fuelAt sources k p (shell sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget)) n (fun _ => K n) ≤ budget n) :
    StageBlock' sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) :=
  stageBlock'_of_stageFields sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) liveScale coefficientFloor
    rfl rfl rfl rfl rfl rfl rfl he ebound ecoef hstage
    (hfuel'_of_cap sources k p (exactStageData sources k p liveScale coefficientFloor extra st stage stageFuel L budget) K hK hbudget)

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
