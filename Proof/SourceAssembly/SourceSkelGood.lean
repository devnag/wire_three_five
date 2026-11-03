import Proof.SourceAssembly.SourceSkelChain

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
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section good
variable {mask : MaskProducer} {selector : CyclicChoice.Laws}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector}
  {rows : PCJc4297ab269d8423a_Source.RowLibrary selector}
  {sources : EightSources} {gamma : Real} {p : Parameters sources gamma} {k r scratch : Nat} {ph : Phase}
  (code : RCFive.Source.SourceCode mask selector packets rows sources p k r scratch ph) (b : Nat) {Atom : Type}
  (vd : RCFive.Source.CallValues Atom code.sourceTapes)

/-- `_hrefill`'s `family`: the row family on the slots ; the entry emitter on `enc` ; the append on `app`. -/
abbrev famOf := Composition.machine (RecoveryFocus.machine code.slots (f_machine code.a))
  (Composition.machine (RecoveryFocus.machine code.enc e_machine)
    (RecoveryFocus.machine code.app CloseoutFinalC10SingleAppend.machine))

/-- `_hrefill`'s `fuel j` (the call's family fuel). -/
abbrev fuelOf (j : Nat) : Nat :=
  f_budget code.a (vd.S j) (vd.rowWidth j) b (vd.xs j).length + 1 +
    (2 * vd.D j + 4 + 1 + (2 * e_emitCost b + 2) + 1 +
      CloseoutFinalC10AppendPositioning.budget b (vd.phasePrefix ++ vd.entries.take j).length)

/-- `_hrefill`'s `outH j` at the call's start heads `H`. -/
abbrev outHOf (j : Nat) (H : Fin code.sourceTapes → Nat) : Fin code.sourceTapes → Nat :=
  dockH code.slots H (r_outputH code.a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) (vd.xs j))

/-- `_hrefill`'s `outA j Z` at the call's start bank `A`. -/
abbrev outAOf (j : Nat) (A : Fin code.sourceTapes → List Bool) (Z : Fin 10 → List Bool) :
    Fin code.sourceTapes → List Bool :=
  install code.app
    (install code.enc (install code.slots A
      (r_outputT code.a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) b (vd.xs j) Z))
     (e_bank b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩ (vd.D j) (vd.cap j)
       (ZeroPadding.pad (vd.D j) (Stream.entryWord b ⟨vd.coefficient j, vd.total j, vd.denominator j⟩))))
    (CloseoutFinalC10AppendPositioning.tapes b (vd.D j) (vd.logSize j) (vd.resetSize j)
      ⟨vd.coefficient j, vd.total j, vd.denominator j⟩
      ((vd.phasePrefix ++ vd.entries.take j) ++ [⟨vd.coefficient j, vd.total j, vd.denominator j⟩]))

/-- `_hrefill`'s `reserve`. -/
abbrev reserveOf : Fin code.sourceTapes → Nat := fun i =>
  if (PCJda54a286946142d3_BranchPhases.offset sources p k r + 1155) ≤ i.val then vd.reserveSize else 0

/-- The family input on the slots at call `j` (`_hA`'s right side). -/
abbrev inTOf (j : Nat) : Fin (r_tapes code.a) → List Bool := fun i =>
  r_inputT code.a (vd.ds j) (vd.S j) (vd.R j) (vd.B j) (vd.rowWidth j) b (vd.xs j).length i

/-- **What `_hrefill` demands between call `j` and call `j+1`** (`A'` is the next call's UNPADDED bank), plus the next
family input heads on the slots (`_hH` at `j+1`). -/
def goodOf (j : Nat) (H : Fin code.sourceTapes → Nat) (A : Fin code.sourceTapes → List Bool)
    (H' : Fin code.sourceTapes → Nat) (A' : Fin code.sourceTapes → List Bool) : Prop :=
  (∀ Z, Step (famOf code) (fuelOf code b vd j) H A (outHOf code vd j H) (outAOf code b vd j A Z) →
    MaskFamilyCode.Prepared code.refillCode (vd.ds (j+1)) vd.refillCost (outHOf code vd j H) H'
      (fun i => ZeroPadding.pad (reserveOf code vd i) (outAOf code b vd j A Z i))
      (fun i => ZeroPadding.pad (reserveOf code vd i) (A' i))) ∧
  (∀ i, H' (code.slots i) = r_inputH code.a (vd.ds (j+1)) (vd.S (j+1)) (vd.R (j+1)) (vd.B (j+1)) (vd.xs (j+1)).length i)

variable {N : Nat} {Inv : Nat → (Fin code.sourceTapes → Nat) → (Fin code.sourceTapes → List Bool) → Prop}

/-- The per-call values with the chain's banks. -/
abbrev chainVals (seam : SeamSpec N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd))
    (H0 : Fin code.sourceTapes → Nat) (A0 : Fin code.sourceTapes → List Bool) :
    RCFive.Source.CallValues Atom code.sourceTapes :=
  { vd with
    H := fun j => (callChain N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd) seam H0 A0 j).1
    A := fun j => (callChain N (fun _ => 0) code.slots (inTOf code b vd) Inv (goodOf code b vd) seam H0 A0 j).2 }

end good

section bridge
open NearCubicWires.SourceParent NearCubicWires.SourcePhase NearCubicWires.SourceConstruction
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size SelectedRecoveryIntegration.outer

end bridge

end
end NearCubicWires.SourceSkeleton
end
