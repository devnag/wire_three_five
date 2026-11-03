import Proof.SourceAssembly.SourceLayout
import Proof.SourceAssembly.SourceRefill

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section code
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

/-- The universe size `sourceTapes` of the layout. -/
abbrev UOf : Nat := (dimsOf mask packets rows sources res p k r).U

theorem UOf_le : UOf mask packets rows sources res p k r ≤ UOf mask packets rows sources res p k r := le_rfl
theorem UOf_le_succ : UOf mask packets rows sources res p k r ≤ UOf mask packets rows sources res p k r + 1 :=
  Nat.le_succ _

/-- The loader's seed on the layout. -/
def seedCode {V : Nat} (hV : UOf mask packets rows sources res p k r ≤ V) :
    MaskSeedCode mask (packets (decompositionOf sources)) V :=
  let d := dimsOf mask packets rows sources res p k r
  SLoad.MaskReady.code mask (packets (decompositionOf sources))
    (d.maskSlots hV) (d.maskSlots_injective hV) (d.pslots hV) (d.pslots_injective hV)
    (d.slot hV) (d.ret hV) (d.scr hV 0) (d.scr hV 1) (d.scr hV 2) (d.scr hV 3) (d.scr hV 4)

def loaderCode {V : Nat} (hV : UOf mask packets rows sources res p k r ≤ V)
    (fin : Σ s, Machine V s) :
    MaskFamilyCode mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources)) V :=
  let d := dimsOf mask packets rows sources res p k r
  SLoad.Prepared.code mask (packets (decompositionOf sources))
    (rows (decompositionOf sources) (printerOf sources))
    (d.maskSlots hV) (d.maskSlots_injective hV) (d.pslots hV) (d.pslots_injective hV)
    (d.slot hV) (d.ret hV) (d.scr hV 0) (d.scr hV 1) (d.scr hV 2) (d.scr hV 3) (d.scr hV 4)
    (d.familySlots hV) (d.familySlots_injective hV) (d.poolSlots hV) (d.poolSlots_injective hV)
    (d.rewindSlots hV) (d.rewindSlots_injective hV)
    (Fin.ext (by
      have h := d.hdesc440
      simp only [Dims.pslots, Dims.pV, Dims.familySlots, Dims.famV, d]
      simp [dimsOf, PCJ38fbfed565f64139_Ready.headerSlots]
      omega))
    (Fin.ext (by
      simp only [Dims.poolSlots, Dims.poolV, Dims.familySlots, Dims.famV, d]
      simp [dimsOf, PCJ38fbfed565f64139_Ready.headerSlots]
      omega))
    (Fin.ext (by
      simp only [Dims.rewindSlots, Dims.rewV, Dims.familySlots, Dims.famV, d]
      simp [dimsOf, PCJ38fbfed565f64139_Ready.descriptor, PCJ38fbfed565f64139_Ready.frameSlots,
        PCJeb9c0f0306e9481c_FramingSpec.target]))
    (d.scr hV 5) (d.scr hV 6) (d.scr hV 7) (d.scr hV 8) (d.scr hV 9) (d.scr hV 10) fin.1 fin.2

def cycleCode {V : Nat} (hV : UOf mask packets rows sources res p k r ≤ V)
    (pre fin : Σ s, Machine V s) :
    MaskFamilyCode mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources)) V :=
  { loaderCode mask packets rows sources res p k r hV fin with
    seed := PCJ6e421fabe2aa4155_SourceRefill.prepend (seedCode mask packets rows sources res p k r hV) pre.2 }

/-- The `app` values of `SourceCode._ha`, verbatim. -/
abbrev appVal (ph : Phase) (i : Fin 6) : Nat :=
  (![(PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes (printerOf sources)+5,
    (CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
      (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res))
      (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
      (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (scratchOf mask packets rows sources res)) ph 81).val,
    (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes (printerOf sources)+10,
    (CloseoutFinalC10RetainedPhaseFold.wordSlots (PCJda54a286946142d3_BranchPhases.offset sources p k r)
      (ControllerSelectedContinuation.bodyTapes sources p k r (scratchOf mask packets rows sources res))
      (PCJda54a286946142d3_BranchPhases.offset_ge sources p k r)
      (PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r (scratchOf mask packets rows sources res)) ph 90).val,
    (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes (printerOf sources)+11,
    (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes (printerOf sources)+12] : Fin 6 → Nat) i

theorem appVal_lt (ph : Phase) (i : Fin 6) :
    appVal mask packets rows sources res p k r ph i < UOf mask packets rows sources res p k r := by
  have h81 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 81
  have h90 := wordSlot_lt sources p k r (scratchOf mask packets rows sources res) ph 90
  simp only [SourceParent.Wd] at h81 h90
  simp only [UOf, Dims.U, Dims.G, Dims.prepT, dimsOf]
  fin_cases i <;> simp [appVal] <;> omega

end code

/-! ## The forced `SourceChoices` -/

structure FreeChoices where
  capIndex : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  r : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  base : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingFuel : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat → Nat
  remainingCoefficient : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  remainingOnset : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  tableCoefficient : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat
  tableDegree : (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
    Parameters sources gamma → Nat

/-- The forced entry width `b`: the entry bank's tape 218 (`run_from_facts`, `append 0`). -/
abbrev bOf (f : FreeChoices) (sources : EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : Parameters sources gamma) (n : Nat) : Nat :=
  C10PartsSchedule.entryWidthSchedule sources
    (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p) (f.r sources gamma hg hh p) n

/-- **Forced B1: `widths`.** The phase width `foldWidth (CRD.width b) entries` depends only on
the NUMBER of the phase polynomial's monomials (`width_forced`). -/
def widthsOf (f : FreeChoices) : (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) →
    (hh : gamma < 1/2) → (p : Parameters sources gamma) → (n : Nat) → BitInput n → List Bool →
    Phase → Nat :=
  fun sources gamma hg hh p n x bits ph =>
    CompetitorSumWidth.width
      (SourceParent.Poly sources p (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p)
        (f.capIndex sources gamma hg hh p + 1)
        (PolynomialClock.ordinaryClock (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p)) n x
        (C10TotalDecode.oracleOf sources (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p)
          (PolynomialClock.ordinaryClock (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p))
          p.degree n bits) bits ph).monomials.length
      (CompetitorRationalDecision.width (bOf f sources gamma hg hh p n))

/-- The reserved prologue-region size, fixed before `n x bits`. -/
abbrev ResChoice := (sources : EightSources) → (gamma : Real) → 0 < gamma → gamma < 1/2 →
  Parameters sources gamma → Nat

/-- The universe of the code at a free choice. -/
abbrev UAt (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (res : ResChoice) (f : FreeChoices)
    (sources : EightSources) (gamma : Real) (hg : 0 < gamma) (hh : gamma < 1/2)
    (p : Parameters sources gamma) : Nat :=
  UOf mask packets rows sources (res sources gamma hg hh p) p
    (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p) (f.r sources gamma hg hh p)

/-- The full `SourceChoices`: the free ones, plus the forced `scratch` and `widths`. -/
def forcedChoices (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (res : ResChoice) (f : FreeChoices) :
    SourceParent.SourceChoices where
  capIndex := f.capIndex
  remainingDegree := f.remainingDegree
  r := f.r
  base := f.base
  scratch := fun sources gamma hg hh p => scratchOf mask packets rows sources (res sources gamma hg hh p)
  remainingFuel := f.remainingFuel
  widths := widthsOf f
  remainingCoefficient := f.remainingCoefficient
  remainingOnset := f.remainingOnset
  tableCoefficient := f.tableCoefficient
  tableDegree := f.tableDegree

end
end NearCubicWires.SourceConstruction
end
