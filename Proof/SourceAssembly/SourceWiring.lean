import Proof.SourceAssembly.SourceCycle
import Proof.SourceAssembly.SourceLayout

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

namespace Dims
variable (d : Dims)

/-- The start of the reserved region. -/
def B : Nat := d.G + d.R1 + 410 + d.w + d.tc
def rw2V (i : Nat) : Nat := if i = 0 then d.F + d.sp else 277 + i
def csV (k : Nat) : Nat :=
  if k = 3 then d.G + (d.R1 - 1) else if k = 1 then d.B + 13 else if k = 2 then d.B + 14
  else if k = 0 then d.B else d.B + (k - 3)
def drvV (k : Nat) : Nat :=
  if k = 3 then d.B + 1 else if k = 5 then d.G + (d.R1 - 1) else if k = 6 then d.B + 2
  else if k = 0 then d.B + 15 else if k = 1 then d.B + 16 else if k = 2 then d.B + 17 else d.B + 18

/-- The extra facts this placement needs. -/
structure Ext : Prop where
  hF : 285 < d.F
  hres : 19 ≤ d.res
  hlast : d.descV + 1 < d.R1

variable {d} (e : d.Ext) {V : Nat} (hV : d.U ≤ V)

def rewind2Slots (i : Fin 3) : Fin V :=
  ⟨d.rw2V i.val, Nat.lt_of_lt_of_le (by
    have := i.isLt; have := d.hsp; have := e.hF; unfold rw2V U G prepT; split_ifs <;> omega) hV⟩
def csSlots (k : Fin 16) : Fin V :=
  ⟨d.csV k.val, Nat.lt_of_lt_of_le (by
    have := k.isLt; have := e.hres; have := e.hlast; unfold csV B U G prepT; split_ifs <;> omega) hV⟩
def drvSlots (k : Fin 7) : Fin V :=
  ⟨d.drvV k.val, Nat.lt_of_lt_of_le (by
    have := k.isLt; have := e.hres; have := e.hlast; unfold drvV B U G prepT; split_ifs <;> omega) hV⟩
def natSlots (i : Fin d.rt) : Fin V :=
  ⟨d.F + i.val, Nat.lt_of_lt_of_le (by have := i.isLt; unfold U G prepT; omega) hV⟩
def lenTape : Fin V := ⟨d.B, Nat.lt_of_lt_of_le (by have := e.hres; unfold B U G prepT; omega) hV⟩

end Dims

/-- Unfold every layout value and close an interval (in)equality. -/
macro "wgeo" : tactic => `(tactic| (simp only [Dims.slot, Dims.maskSlots, Dims.pslots, Dims.poolSlots,
  Dims.ret, Dims.scr, Dims.familySlots, Dims.rewind2Slots, Dims.csSlots, Dims.drvSlots, Dims.natSlots,
  Dims.lenTape, Dims.slotV, Dims.maskV, Dims.pV, Dims.poolV, Dims.retV, Dims.scrV, Dims.famV, Dims.rw2V,
  Dims.csV, Dims.drvV, Dims.B, Dims.G, Fin.val_mk] at * <;> (try split_ifs at *) <;> omega))

namespace Dims

end Dims

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

theorem dims_ext (hres : 19 ≤ res) : (dimsOf mask packets rows sources res p k r).Ext where
  hF := by simp only [dimsOf]; omega
  hres := hres
  hlast := by simp only [dimsOf, rowTapes, rowWork, PCJ38fbfed565f64139_Ready.tapes]; omega

end concrete

end
end NearCubicWires.SourceConstruction
end
