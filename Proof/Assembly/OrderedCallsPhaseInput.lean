import Proof.Assembly.OrderedCallsPhaseLoop

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ2f4bbfb841674a7c_.PhaseConstruction
open NearCubicWires P1TopDown LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairSource RepairSource.CloseoutFinal SourceInterfaces
noncomputable section
attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size
variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
 (k den r scratch : Nat) (clock : OrdinaryClock (fun n => n^(k+2))) (n : Nat) (x : BitInput n)
 (oracle : BooleanCircuit ((SelectedRecoveryIntegration.outer sources k clock).result.pcp.nativeWidth n))
 (bits : List Bool)
 (site : Bool → CloseoutRowsOriginalSchedule.Phase → Σ states,
   Machine (ControllerSelectedContinuation.bodyTapes sources p k r scratch) states)
 (mode : Bool) (ph : CloseoutRowsOriginalSchedule.Phase)
 (hin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → Nat)
 (tin : Fin (PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch) → List Bool)
 (fuel width : Nat)

def Input : Prop :=
 let pcpp := pcppAt sources k clock x oracle
 let Atom := C10TotalDecode.Atom pcpp
 let constants := NearCubicWires.RepairSource.CloseoutFinal.constantsOf sources
 let coordinate := PCJd04de0277f804fcc_.coordinate sources k clock p den x oracle bits
 let systematicAtom := C10TotalDecode.Atom.systematic (pcpp := pcpp)
 let evaluate := C10TotalDecode.evaluate (pcpp := pcpp)
 let mass : Real := ((CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).coefficientMass : Rat)
 let L := PCJda54a286946142d3_BranchPhases.offset sources p k r
 let B := ControllerSelectedContinuation.bodyTapes sources p k r scratch
 let hL := PCJda54a286946142d3_BranchPhases.offset_ge sources p k r
 let hFresh := PCJda54a286946142d3_BranchPhases.fresh_lt sources p k r scratch
 let t := PCJda54a286946142d3_BranchPhases.tapes sources p k r scratch
 let body := PCJda54a286946142d3_BranchPhases.body sources p k r scratch
 let driver := PCJda54a286946142d3_BranchPhases.driver sources p k r scratch
 ∃ (supplier : List Atom → Rat)
    (failure : Real)
    (b : Nat)
    (entries : List NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry)
    (H : Nat → Fin B → Nat)
    (A : Nat → Fin B → List Bool)
    (entryFuel : Nat)
    (N : Nat)
    (cost : Nat)
    (middleH : Fin t → Nat)
    (middle : Fin t → List Bool)
    (_hfailure : 0 ≤ failure)
    (_hpoint : ∀ monomial ∈ (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials, |((supplier monomial.factors : Rat) : Real) - NearCubicWires.SupplierPipeline.conjunctionProbability evaluate monomial.factors| ≤ failure)
    (_hbudget : failure * mass ≤ ((NearCubicWires.RepairSource.CompetitorRationalGap.estimationTolerance constants (NearCubicWires.RepairSource.CompetitorRationalGap.zeta constants) : Rat) : Real))
    (_hcalls : PCJ2f4bbfb841674a7c_.OrderedCalls supplier (NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness.phasePolynomial ph pcpp coordinate systematicAtom).monomials entries)
    (_hvalid : ∀ entry ∈ entries, NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream.Entry.Valid b entry)
    (_hHw : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph i) = 0)
    (_hHf : ∀ i, H N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.foldSlots L B hL hFresh ph i) = 0)
    (_hwidthDriver : A N (NearCubicWires.RepairOrdinary.CloseoutFinalC10RetainedPhaseFold.wordSlots L B hL hFresh ph 218) = List.replicate b true)
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
    (_hN : N=2^pcpp.clauseBits)
    (siteFuel : Nat)
    (_hcost : 4*N+PCPPQueryCachedBounds.callBudget (CloseoutLanguage.selectedPCPP sources)
       ((req sources k clock x oracle).circuit.size+(req sources k clock x oracle).arity)+siteFuel+21≤cost)
    (_loop : PCJ30aa6f1b7c2a4221_.SiteLoop sources p k r scratch site mode ph
       (CloseoutLanguage.selectedPCPP sources) (req sources k clock x oracle) H A siteFuel),
 fuel=entryFuel+1+(N*(cost+3)+3+1+CloseoutFinalC10RetainedPhaseFold.fuel b entries.length) ∧
 width=CloseoutFinalC10WorkerFold.foldWidth (CompetitorRationalDecision.width b) entries

variable {sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width}

@[irreducible] noncomputable def Input.realize
 (I : Input sources p k den r scratch clock n x oracle bits site mode ph hin tin fuel width) :
 CloseoutFinalC10Realizes.Realizes ph (constantsOf sources) (pcppAt sources k clock x oracle)
   (P1Independent.CappedDecode.proofValueOf sources k clock p den x oracle bits)
   (C10TotalDecode.evaluate (pcpp := pcppAt sources k clock x oracle))
   (PCJda54a286946142d3_BranchPhases.phase sources p k r scratch site mode ph).2
   fuel hin tin
   (PCJ374c44bb8b7f47d9_.S.ports sources p k r scratch ph)
   width := by
 classical
 apply Classical.choice
 dsimp only [Input] at I
 obtain ⟨supplier,failure,b,entries,H,A,entryFuel,N,cost,middleH,middle,hfailure,hpoint,hbudget,hcalls,hvalid,hHw,hHf,hwidthDriver,hcount,hstream,hblank,hfresh,hrecord,hlog,hentry,hhead,htape,hdriver,hword,hN,siteFuel,hcost,loop,hf,hw⟩ := I
 rw [hf,hw]
 refine ⟨?_⟩
 exact PCJ2f4bbfb841674a7c_.PhaseLoop.selected_phase sources gamma p k den r scratch clock n x oracle bits
   site mode ph supplier failure b entries H A entryFuel N cost hin middleH tin middle
   hfailure hpoint hbudget hcalls hvalid hHw hHf hwidthDriver hcount hstream hblank hfresh
   hrecord hlog hentry hhead htape hdriver hword hN siteFuel hcost loop

end
end PCJ2f4bbfb841674a7c_.PhaseConstruction
