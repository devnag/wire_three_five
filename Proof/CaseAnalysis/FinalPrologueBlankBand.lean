import Proof.CaseAnalysis.FinalSupplierCountStage
import Proof.CaseAnalysis.FinalSeedEngine

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10PrologueBlankBand

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The prologue's exit, read by tape number

`Prologue` (`Proof/CaseAnalysis/FinalPrologueUniform.lean`) states its exit as
`Fin.addCases` over the bank and the one extra counter tape.  Both halves are read
here by tape number, which is the only form the docking of §4 can use. -/

/-! ## §2 The free invariant, and why it is worth nothing

`BlankFrom L` for `L` at or above the bank's width is deliverable from ANY
prologue, because `bank` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) reads its
scratch only at tape numbers below the width.  The same fact is exactly why such
an invariant hands a round no blank tape. -/

/-! ## §4 The repair: widen the bank, keep the prologue

`Step.dock` (`ExtDecompositionBatch/Layout.lean:89`) moves a run into a wider
layout at the SAME fuel, and `install_other`
(`Proof/Amplification/RecoveryReadyCalls.lean`) leaves every tape outside the image exactly as
it entered.  The prologue's entry bank is blank on the whole scratch band, so the
fresh tapes leave blank, and the leftover workspace is blank from the OLD bank's
width up. -/

/-! ## §5 What the consumer gets

`bank_blank_of_blankFrom` is the shape every docked engine of the corpus demands
(`A (slots j) = []`); `hpre_of_prologueBlank` is `callsReady_of_rounds`'s `hpre`
binder verbatim at the blank-band invariant; `callsReady_of_rounds_blankBand`
reaches `RepairSource.CloseoutFinal.C10SupplierStage.CallsReady`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`). -/


end NearCubicWires.RepairOrdinary.CloseoutFinalC10PrologueBlankBand
