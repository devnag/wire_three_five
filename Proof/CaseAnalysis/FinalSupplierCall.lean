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

/-- The gate's exit tapes, by tape number: `wflag` is `216`. -/
theorem entryOf_apply (e : ℕ) (input witness : List Bool) (i : Fin (218 + e)) :
    C10TailCompose.entryOf (C10TailCompose.wflag e) input witness i =
      if i.val = 216 then [true]
      else if i.val = 0 then frame input
      else if i.val = 1 then frame witness else [] := by
  by_cases h : i.val = 216
  · have hi : i = C10TailCompose.wflag e :=
      Fin.ext (by rw [h, C10TailCompose.wflag_val])
    simp [C10TailCompose.entryOf, hi]
  · have hi : i ≠ C10TailCompose.wflag e := by
      intro hh
      exact h (by rw [hh, C10TailCompose.wflag_val])
    simp [C10TailCompose.entryOf, hi, h]

/-- **The entry bank IS the gate's exit bank.**  The empty stream, the empty
counter, the empty driver word and empty scratch. -/
theorem bank_entryOf (e : ℕ) (input witness : List Bool) :
    (bank [] [] [] input witness (fun _ => []) : Fin (218 + e) → List Bool)
      = C10TailCompose.entryOf (C10TailCompose.wflag e) input witness := by
  funext i
  rw [entryOf_apply]
  show bankAt [] [] [] input witness (fun _ => []) i.val = _
  unfold bankAt
  split_ifs <;> first | rfl | omega

/-- **One more tape.**  Both the loop's address counter and the head reset's
mark tape land at index `>= 278`, i.e. in the scratch region, so the bank
expression is unchanged. -/
theorem bank_succ {t : ℕ} (ht : 278 ≤ t) (stream count driver input witness top : List Bool)
    (sc1 sc2 : ℕ → List Bool) (h : ∀ j, j < t → sc1 j = sc2 j) (htop : sc2 t = top) :
    Fin.addCases (motive := fun _ => List Bool)
        (bank stream count driver input witness sc1 : Fin t → List Bool)
        (fun _ : Fin 1 => top)
      = (bank stream count driver input witness sc2 : Fin (t + 1) → List Bool) := by
  funext i
  refine Fin.addCases (m := t) (n := 1) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.addCases_left]
    show bankAt stream count driver input witness sc1 j.val
        = bankAt stream count driver input witness sc2 j.val
    unfold bankAt
    split_ifs <;> first | rfl | exact h j.val j.isLt
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd t j : Fin (t + 1)).val = t := by
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      show t + j.val = t
      omega
    show (fun _ : Fin 1 => top) j
        = bankAt stream count driver input witness sc2 (Fin.natAdd t j : Fin (t + 1)).val
    rw [hv]
    show top = bankAt stream count driver input witness sc2 t
    unfold bankAt
    rw [if_neg (by omega : ¬ (t = 0)), if_neg (by omega : ¬ (t = 1)),
      if_neg (by omega : ¬ (t = 81)), if_neg (by omega : ¬ (t = 90)),
      if_neg (by omega : ¬ (t = 216)), if_neg (by omega : ¬ (t = 218)), if_pos ht]
    exact htop.symm

/-- `C10SupplierStage.wordsBank` reads this bank by tape number. -/
theorem wordsBank_bank (extra : ℕ) (stream count driver input witness : List Bool)
    (scratch : ℕ → List Bool) (j : Fin (219 + CloseoutFinalC10WordsStage.s)) :
    C10SupplierStage.wordsBank (extra + 2)
        (bank stream count driver input witness scratch) j
      = bankAt stream count driver input witness scratch j.val := rfl

/-! ## §2 The clause-address prefixes of the phase's record stream -/

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-- **The records of the first `k` clause addresses.**  `phaseRecords` is
`univ.toList.flatMap (siteRecords ...)`; this is the same `flatMap` over the
first `k` entries of that address list, i.e. the content of tape `81` after `k`
rounds of the loop. -/
noncomputable def prefixRecords (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ) : List Entry :=
  ((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.take k).flatMap
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)

/-- **The records of clause address number `k`**: what round `k` of the loop
must append. -/
noncomputable def addressRecords (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (k : ℕ) : List Entry :=
  (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1).flatMap
    (siteRecords answer denominator phase pcpp coordinate systematicAtom)

/-- The encoded stream splits along the address list exactly as the record list
does: appending a clause address's records appends its words. -/
theorem words_append (b : ℕ) (xs ys : List Entry) :
    CloseoutRowsEstimatorCoefficients.Stream.words b (xs ++ ys)
      = CloseoutRowsEstimatorCoefficients.Stream.words b xs
        ++ CloseoutRowsEstimatorCoefficients.Stream.words b ys := by
  unfold CloseoutRowsEstimatorCoefficients.Stream.words
  rw [List.flatMap_append]

/-! ## §3 The loop's bank family -/

/-- **The bank after `k` rounds**: the first `k` clause addresses' calls encoded
on tape `81`, their count on tape `90`, the driver word on `218`, the gate's
tapes `0`/`1`/`216` untouched, the rest of `0 .. 277` blank. -/
noncomputable def loopBank (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) : Fin (218 + (60 + extra)) → List Bool :=
  bank
    (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k))
    (CompareMachine.word
      (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length)
    (List.replicate entryWidth true) input witness (scratch k)

theorem loopBank_eq (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) (k : ℕ) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch k
      = bank
        (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k))
        (CompareMachine.word
          (prefixRecords answer denominator phase pcpp coordinate systematicAtom k).length)
        (List.replicate entryWidth true) input witness (scratch k) := rfl

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

def rowFuel (preFuel cost : ℕ) : ℕ := 2 * cost + 2 * preFuel + 18

/-! ## §5 The two scratch extensions -/

/-- The address counter's tape, at index `218 + (60 + extra)`. -/
def outerScratch (extra : ℕ) (base : ℕ → List Bool) (loopWord : List Bool) (j : ℕ) :
    List Bool :=
  if j = 218 + (60 + extra) then loopWord else base j

/-- The head-reset mark tape, at index `218 + (60 + extra) + 1`. -/
def finalScratch (extra : ℕ) (base : ℕ → List Bool) (loopWord counter : List Bool) (j : ℕ) :
    List Bool :=
  if j = 218 + (60 + extra) + 1 then counter else outerScratch extra base loopWord j

/-! ## §6 `call_run` -- the clause-address loop, run -/

/-! ## §7 `callsReady_of_call` -- literally S0's `CallsReady` -/

/-! ## §8 The consumer-side check -/


end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
