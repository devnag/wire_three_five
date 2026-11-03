import Proof.SourceAssembly.SourceSkelGen

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.RepairOrdinary.CompetitorRawFieldEmit NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation SourceInterfaces RepairSource RepairSource.CloseoutFinal P1TopDown RepairSource.VerifierDecoding RecoveryRootRound RecoveryExecution CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients CompetitorSelectedCount MatrixScoreBatch CompetitorCountMask SupplierPipeline SupplierEstimator SupplierPrime CanonicalFourfoldRowProgram CloseoutRawRows C10ExternalRowLoop C10ThresholdNaturalRowPrint C10ThresholdParityRow C10ThresholdEstimateRowJoin CloseoutFinalC10RowAnswerWord P1Closure P1TopDownPaidReusable P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves
open PCJ1fef9807c6954e94_Native
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source
namespace NearCubicWires.SourceSkeleton
open NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes WorkspaceSelectedAdmission.originalTapes
  WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

section code
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
  (res : Nat) (hres : 19 ≤ res) {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

theorem hrawR {V : Nat} (hV : (dimsOf mask packets rows sources res p k r).U ≤ V) :
    (dimsOf mask packets rows sources res p k r).pslots hV
        (packets (decompositionOf sources)).ordinary.program.outputTape =
      (dimsOf mask packets rows sources res p k r).familySlots hV
        ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources)
          (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 262).castAdd 1) :=
  Fin.ext (by
    have h := (dimsOf mask packets rows sources res p k r).hdesc440
    simp only [Dims.pslots, Dims.pV, Dims.familySlots, Dims.famV]
    simp [dimsOf, PCJ38fbfed565f64139_Ready.headerSlots]
    omega)

theorem hpoolR {V : Nat} (hV : (dimsOf mask packets rows sources res p k r).U ≤ V) :
    (dimsOf mask packets rows sources res p k r).poolSlots hV 34 =
      (dimsOf mask packets rows sources res p k r).familySlots hV
        ((PCJ38fbfed565f64139_Ready.headerSlots (printerOf sources)
          (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork) 0).castAdd 1) :=
  Fin.ext (by
    simp only [Dims.poolSlots, Dims.poolV, Dims.familySlots, Dims.famV]
    simp [dimsOf, PCJ38fbfed565f64139_Ready.headerSlots]
    omega)

theorem hsrcR {V : Nat} (hV : (dimsOf mask packets rows sources res p k r).U ≤ V) :
    Dims.rewind2Slots (dims_ext mask packets rows sources res p k r hres) hV 0 =
      (dimsOf mask packets rows sources res p k r).familySlots hV
        ((PCJ38fbfed565f64139_Ready.descriptor (printerOf sources)
          (rowWork (rows (decompositionOf sources) (printerOf sources)).privateWork)).castAdd 1) :=
  Fin.ext (by
    simp only [Dims.rewind2Slots, Dims.rw2V, Dims.familySlots, Dims.famV]
    simp [dimsOf, PCJ38fbfed565f64139_Ready.descriptor, PCJ38fbfed565f64139_Ready.frameSlots,
      PCJeb9c0f0306e9481c_FramingSpec.target])

/-- **One cycle on the concrete layout** (any reserved region `res ≥ 19`): S's `Cycle.cycleCode` with `SourceWiring`'s placement, for a prologue
`pre` on any universe `V ≥ U` (`U` for the refill cycle, `U+1` for the first cycle). -/
def skelCycleR {V s : Nat} (hV : (dimsOf mask packets rows sources res p k r).U ≤ V) (pre : Machine V s) :
    MaskFamilyCode mask (packets (decompositionOf sources))
      (rows (decompositionOf sources) (printerOf sources)) V :=
  Cycle.cycleCode mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources))
    ((dimsOf mask packets rows sources res p k r).maskSlots hV)
    ((dimsOf mask packets rows sources res p k r).maskSlots_injective hV)
    ((dimsOf mask packets rows sources res p k r).pslots hV)
    ((dimsOf mask packets rows sources res p k r).pslots_injective hV)
    ((dimsOf mask packets rows sources res p k r).slot hV)
    ((dimsOf mask packets rows sources res p k r).ret hV)
    ((dimsOf mask packets rows sources res p k r).scr hV 0)
    ((dimsOf mask packets rows sources res p k r).scr hV 1)
    ((dimsOf mask packets rows sources res p k r).scr hV 2)
    ((dimsOf mask packets rows sources res p k r).scr hV 3)
    ((dimsOf mask packets rows sources res p k r).scr hV 4)
    ((dimsOf mask packets rows sources res p k r).familySlots hV)
    ((dimsOf mask packets rows sources res p k r).familySlots_injective hV)
    ((dimsOf mask packets rows sources res p k r).poolSlots hV)
    ((dimsOf mask packets rows sources res p k r).poolSlots_injective hV)
    (Dims.rewind2Slots (dims_ext mask packets rows sources res p k r hres) hV)
    (rewind2_injective (dims_ext mask packets rows sources res p k r hres) hV)
    (hrawR mask packets rows sources res p k r hV) (hpoolR mask packets rows sources res p k r hV)
    (hsrcR mask packets rows sources res hres p k r hV)
    ((dimsOf mask packets rows sources res p k r).scr hV 5)
    ((dimsOf mask packets rows sources res p k r).scr hV 6)
    ((dimsOf mask packets rows sources res p k r).scr hV 7)
    ((dimsOf mask packets rows sources res p k r).scr hV 8)
    ((dimsOf mask packets rows sources res p k r).scr hV 9)
    ((dimsOf mask packets rows sources res p k r).scr hV 10) pre
    (Dims.csSlots (dims_ext mask packets rows sources res p k r hres) hV) (Dims.natSlots hV)
    (Dims.drvSlots (dims_ext mask packets rows sources res p k r hres) hV)

/-- The source universe at `res := resOf D`. -/
abbrev UR : Nat := UOf mask packets rows sources res p k r

def skelCodeR (ph : Phase) (refill : Σ s, Machine (UR mask packets rows sources res p k r) s)
    (preF : Σ s, Machine (UR mask packets rows sources res p k r + 1) s) :
    RCFive.Source.SourceCode mask selector packets rows sources p k r
      (scratchOf mask packets rows sources res) ph where
  a := printerOf sources
  prepT := prepTOf mask packets rows sources res
  _hsize := rfl
  sourceTapes := UOf mask packets rows sources res p k r
  slots := fun i => ⟨PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155 + i.val, by
    have := i.isLt; simp only [UOf, Dims.U, Dims.G, Dims.prepT, dimsOf]; omega⟩
  _hs := fun _ => rfl
  enc := fun i => ⟨if i.val=5 then (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes (printerOf sources)-5
       else (PCJda54a286946142d3_BranchPhases.offset sources p k r)+1155+r_tapes (printerOf sources)+(if i.val<5 then i.val else i.val-1), by
    have := i.isLt
    simp only [UOf, Dims.U, Dims.G, Dims.prepT, dimsOf]
    split_ifs <;> omega⟩
  _he := fun _ => rfl
  app := fun i => ⟨appVal mask packets rows sources res p k r ph i,
    appVal_lt mask packets rows sources res p k r ph i⟩
  _ha := fun _ => rfl
  refillCode := skelCycleR mask packets rows sources res hres p k r (UOf_le mask packets rows sources res p k r)
    refill.2
  firstCode := skelCycleR mask packets rows sources res hres p k r (UOf_le_succ mask packets rows sources res p k r)
    preF.2
  _refillSource := Fin.ext (by
    simp [skelCycleR, Cycle.cycleCode, SLoad.Prepared.code, MaskFamilyCode.base, FamilyCode.cached,
      Dims.rewind2Slots, Dims.rw2V, dimsOf, PCJc4297ab269d8423a_Source.sourcePort])
  _firstSource := Fin.ext (by
    simp [skelCycleR, Cycle.cycleCode, SLoad.Prepared.code, MaskFamilyCode.base, FamilyCode.cached,
      Dims.rewind2Slots, Dims.rw2V, dimsOf, PCJc4297ab269d8423a_Source.sourcePort])
  whole := fun i => ⟨i.val, by
    have h := dims_U mask packets rows sources res p k r
    have := i.isLt
    simp only [UOf] at this
    omega⟩
  _hwhole := fun _ => rfl

end code

/-! ## The mode-indexed code family at the forced choices, any reserved-region choice -/

/-- A per-`(mode, ph)` machine on the source universe at reserved region `res` (the refill prologue family). -/
abbrev RefillFamR (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (res : ResChoice) (f : FreeChoices) :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → Bool → Phase →
    Σ s, Machine (UAt mask packets rows res f sources gamma hg hh p) s

/-- A per-`(mode, ph)` machine on the source universe plus the loop counter (the first prologue family). -/
abbrev FirstFamR (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (res : ResChoice) (f : FreeChoices) :=
  (sources : EightSources) → (gamma : Real) → (hg : 0 < gamma) → (hh : gamma < 1/2) →
    (p : Parameters sources gamma) → Bool → Phase →
    Σ s, Machine (UAt mask packets rows res f sources gamma hg hh p + 1) s

/-- **The concrete `CodeFamily`** at any reserved-region choice (`res ≥ 19`): one `skelCodeR` per `(sources, p, mode, ph)`. -/
def skelFamilyR (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (res : ResChoice)
    (hres : ∀ sources gamma hg hh p, 19 ≤ res sources gamma hg hh p) (f : FreeChoices)
    (refill : RefillFamR mask packets rows res f) (first : FirstFamR mask packets rows res f) :
    SourceParent.CodeFamily mask selector packets rows (forcedChoices mask packets rows res f) :=
  fun sources gamma hg hh p mode ph =>
    skelCodeR mask packets rows sources (res sources gamma hg hh p) (hres sources gamma hg hh p) p
      (SourceParent.kOf f.capIndex f.remainingDegree sources gamma hg hh p) (f.r sources gamma hg hh p) ph
      (refill sources gamma hg hh p mode ph) (first sources gamma hg hh p mode ph)

/-- The reserved region with room for the rest layout's twenty prologue residents and an extra `xR` (SI's init workspace,
anything else fixed per parameter tuple): `39 + restPc + xR`. -/
def resOfX {a : DecompositionAlgorithm} (D : RestData a) (xR : Nat) : Nat := 39 + restPc D.se.extra D.sp.extra D.gW + xR

/-- The reserved-region choice of `(D, xR)`. -/
abbrev resChoiceX (D : RestFam) (xR : SourceBudget.ParNat) : ResChoice :=
  fun sources gamma hg hh p => resOfX (D sources gamma hg hh p) (xR sources gamma hg hh p)

theorem resChoiceX_ge (D : RestFam) (xR : SourceBudget.ParNat) (sources : EightSources) (gamma : Real) (hg : 0 < gamma)
    (hh : gamma < 1/2) (p : Parameters sources gamma) : 19 ≤ resChoiceX D xR sources gamma hg hh p := by
  show 19 ≤ resOfX (D sources gamma hg hh p) (xR sources gamma hg hh p)
  unfold resOfX; omega

/-- S's `RestExt2` holds at `resOfX` (ten prologue residents), for the refill prologue `Rest.refillPro`. -/
theorem restExt2X (mask : MaskProducer) {selector : CyclicChoice.Laws}
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
    (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources)
    (D : RestData (decompositionOf sources)) (xR : Nat) {gamma : Real} (p : Parameters sources gamma) (k r : Nat) :
    (dimsOf mask packets rows sources (resOfX D xR) p k r).RestExt2 D.se.extra D.sp.extra D.gW where
  ext1 :=
    { ext := dims_ext mask packets rows sources (resOfX D xR) p k r (by unfold resOfX; omega)
      hres := by show 19 + restPc D.se.extra D.sp.extra D.gW + 5 ≤ resOfX D xR; unfold resOfX; omega }
  hres2 := by show 19 + restPc D.se.extra D.sp.extra D.gW + 10 ≤ resOfX D xR; unfold resOfX; omega

end
end NearCubicWires.SourceSkeleton
end
