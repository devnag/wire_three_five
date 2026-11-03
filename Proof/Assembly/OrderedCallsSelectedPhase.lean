import Proof.Assembly.OrderedCallsCappedFold
import Proof.Assembly.SelectedPhases

/-! The actual selected phase, including its physical entry, counted clause
loop, and derived retained fold. All entry and clause execution assumptions
and fold input conditions remain explicit at the same consecutive bank. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true

namespace PCJ2f4bbfb841674a7c_.SelectedPhase
open NearCubicWires NearCubicWires.P1TopDown NearCubicWires.LocalBitMultitape
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceInterfaces

noncomputable def selected_phase :
open NearCubicWires NearCubicWires.P1TopDown NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.SourceInterfaces in
∀ (sources : EightSources) (gamma : Real) (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((NearCubicWires.RepairSource.SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool),
 let pcpp := pcppAt sources k clock x oracle
 let Atom := C10TotalDecode.Atom pcpp
 let constants := NearCubicWires.RepairSource.CloseoutFinal.constantsOf sources
 let coordinate := PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits
 let systematicAtom := C10TotalDecode.Atom.systematic (pcpp := pcpp)
 let evaluate := C10TotalDecode.evaluate (pcpp := pcpp)
 let proofValue := P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits
 ∀ (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase),
 let mass : Real := ((CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass : Rat)
 let L := PCJda54a286946142d3_BranchPhases.offset sources p k r
 let B := ControllerSelectedContinuation.bodyTapes sources p k r scratch
 let hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
 let hFresh := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
 let t := PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch
 let body := PCJda54a286946142d3_BranchPhases.body sources p k r scratch
 let driver := PCJda54a286946142d3_BranchPhases.driver sources p k r scratch
 ∀ (supplier : List Atom → Rat)
    (failure : Real)
    (b : Nat)
    (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Nat → Fin B → Nat)
    (A : Nat → Fin B → List Bool)
    (entryFuel N cost : Nat)
    (hin middleH : Fin t → Nat) (tin middle : Fin t → List Bool)
    (_hfailure : 0 ≤ failure)
    (_hpoint : ∀ monomial ∈ (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials, |((supplier monomial.factors : Rat) : Real) - NearCubicWires.SupplierPipeline.conjunctionProbability evaluate monomial.factors| ≤ failure)
    (_hbudget : failure * mass ≤ ((NearCubicWires.RepairSource.CompetitorRationalGap.estimationTolerance constants (NearCubicWires.RepairSource.CompetitorRationalGap.zeta constants) : Rat) : Real))
    (_hcalls : PCJ2f4bbfb841674a7c_.OrderedCalls supplier (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials entries)
    (_hvalid : ∀ entry ∈ entries, NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid b entry)
    (_hHw : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i) = 0)
    (_hHf : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i) = 0)
    (_hdriver : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 218) = List.replicate b true)
    (_hcount : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 90) = NearCubicWires.RepairSource.VerifierDecoding.CompareMachine.word entries.length)
    (_hstream : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 81) = NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.words b entries)
    (_hblank : ∀ i : Fin 278, 2 ≤ i.val → i.val < 215 → i.val ≠ 81 → i.val ≠ 90 → A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hfresh : ∀ i : Fin 278, 219 ≤ i.val → A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i)=[])
    (_hrecord : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)=[])
    (_hlog : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 218)=[])
    (_hentry : Step (RecoveryFocus.machine body (PCJda54a286946142d3_BranchPhases.phaseEntry sources p k r scratch mode ph).2)
      entryFuel hin tin middleH middle)
    (_hhead : ∀ i, middleH (body i)=H 0 i)
    (_htape : ∀ i, middle (body i)=A 0 i)
    (_hdriver : middleH driver=1)
    (_hword : middle driver=UnaryTemplate.tape N)
    (_hround : ∀ j, j<N → Step (PCJda54a286946142d3_BranchPhases.clause sources p k r scratch site mode ph).2
       cost (H j) (A j) (H (j+1)) (A (j+1))),
 CloseoutFinalC10Realizes.Realizes ph constants pcpp proofValue evaluate
   (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site mode ph).2
   (entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length)) hin tin
   (body (CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215))
   (CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries)
 := by
  intro sources gamma p k den r scratch clock n x oracle bits pcpp Atom constants coordinate
    systematicAtom evaluate proofValue site mode ph mass L B hL hFresh t body driver
    supplier failure b entries H A entryFuel N cost hin middleH tin middle
    hfailure hpoint hbudget hcalls hvalid hHw hHf hwidthDriver hcount hstream hblank hfresh
    hrecord hlog hentry hhead htape hdriver hword hround
  let R := PCJ2f4bbfb841674a7c_.CappedFold.capped_fold sources gamma p k den clock n x oracle bits
    ph L B hL hFresh supplier failure b entries (H N) (A N)
    hfailure hpoint hbudget hcalls hvalid hHw hHf hwidthDriver hcount hstream hblank hfresh
    hrecord hlog
  exact ControllerSelectedLayout.phase_realizes
    (RecoveryFocus.machine body
      (PCJda54a286946142d3_BranchPhases.phaseEntry sources p k r scratch mode ph).2)
    (PCJda54a286946142d3_BranchPhases.clause sources p k r scratch site mode ph).2
    (CloseoutFinalC10RetainedPhaseFold.machine L B hL hFresh ph)
    (CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph 215)
    (CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries)
    entryFuel N cost (CloseoutFinalC10RetainedPhaseFold.fuel b entries.length)
    body driver (PCJda54a286946142d3_BranchPhases.body_injective sources p k r scratch)
    (PCJda54a286946142d3_BranchPhases.body_ne_driver sources p k r scratch)
    H A hin middleH tin middle hentry hhead htape hdriver hword hround R

end PCJ2f4bbfb841674a7c_.SelectedPhase
