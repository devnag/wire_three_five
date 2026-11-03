import Proof.CaseAnalysis.FinalEnvelopeCounter
import Proof.CaseAnalysis.FinalSupplierCall

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 Two frame readings of the loop bank -/

/-! ## §2 Threading one round's choice into a family -/

/-! ## §3 The round bank, and the residual -/

/-- **The loop bank at round `k`, as a function of ONE scratch snapshot.**
`loopBank` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) reads the scratch
family only at `k`; saying so is what lets the round obligation quantify over
the incoming scratch instead of over a whole family. -/
noncomputable def roundBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) (k : ℕ) : Fin (218 + (60 + extra)) → List Bool :=
  bank
    (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k))
    (CompareMachine.word
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length)
    (List.replicate entryWidth true) input witness s

/-- The two agree, definitionally. -/
theorem loopBank_roundBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k
      = roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness (scratch k) k := rfl

/-- **Round zero is branch-free**: the empty record stream and
`CompareMachine.word 0` (`Proof/PCP/VerifierDecodingCompare.lean`).  This is the
seam with the prologue -- the right-hand side names no `answer`, no `pcpp`, no
`coordinate`. -/
theorem roundBank_zero (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (s : ℕ → List Bool) :
    roundBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness s 0
      = bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness s := rfl

/-! ## §4 The residual IS `hbody`, both ranges -/

/-! ## §5 The consumer: `CallsReady`, from the prologue and the emitter -/

/-! ## §6 What one round charges the body with, tape by tape -/

end NearCubicWires.RepairSource.CloseoutFinal.C10SiteBodyUniform
