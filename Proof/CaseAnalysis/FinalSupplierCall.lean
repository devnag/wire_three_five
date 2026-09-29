import Proof.CaseAnalysis.FinalSupplierStage

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteRecords)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The bank `CallsReady` describes, written once -/

/-- **The prologue's exit bank, as a function of the tape NUMBER.**  Every
clause of `C10SupplierStage.CallsReady` is one branch of this `if`-chain, and
nothing else of the `278`-tape prefix is written. -/
def bankAt (stream count driver input witness : List Bool) (scratch : ℕ → List Bool)
    (v : ℕ) : List Bool :=
  if v = 0 then frame input
  else if v = 1 then frame witness
  else if v = 81 then stream
  else if v = 90 then count
  else if v = 216 then [true]
  else if v = 218 then driver
  else if 278 ≤ v then scratch v
  else []

/-- The same, at any bank width. -/
def bank {t : ℕ} (stream count driver input witness : List Bool) (scratch : ℕ → List Bool)
    (i : Fin t) : List Bool :=
  bankAt stream count driver input witness scratch i.val

/-! ## §2 The clause-address prefixes of the phase's record stream -/

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-- The encoded stream splits along the address list exactly as the record list
does: appending a clause address's records appends its words. -/
theorem words_append (b : ℕ) (xs ys : List Entry) :
    CloseoutRowsEstimatorCoefficients.Stream.words b (xs ++ ys)
      = CloseoutRowsEstimatorCoefficients.Stream.words b xs
        ++ CloseoutRowsEstimatorCoefficients.Stream.words b ys := by
  unfold CloseoutRowsEstimatorCoefficients.Stream.words
  rw [List.flatMap_append]

/-! ## §3 The loop's bank family -/

/-- **The call loop.**  The prologue, the clause-address driver at
`N := 2 ^ pcpp.clauseBits`, and the corpus's paid head reset. -/
noncomputable def callMachine (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs) :=
  Rewind.machine (Composition.machine pre (RepeatMachine.machine body (fun _ _ => true)))

/-- **The budget.**  `Rewind`'s `2*n+2` over `Step.seq`'s one bridge step over
`CloseoutRowsOriginalClauseLoop.run`'s `N*(cost+3)+3`. -/
def callFuel (preFuel clauseBits cost : ℕ) : ℕ :=
  2 * (preFuel + 1 + (2 ^ clauseBits * (cost + 3) + 3)) + 2

/-! ## §5 The two scratch extensions -/

/-! ## §6 `call_run` -- the clause-address loop, run -/

/-! ## §7 `callsReady_of_call` -- literally S0's `CallsReady` -/

/-! ## §8 The consumer-side check -/


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
