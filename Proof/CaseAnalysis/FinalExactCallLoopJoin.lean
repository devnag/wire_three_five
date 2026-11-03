import Proof.CaseAnalysis.FinalStageJoin

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactCallLoopJoin

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactFractionProbe
  (phaseRecords' exactFractionRecord)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactRecordLoop
  (prefixRecords' prefixRecords'_saturate prefixBank Rounds' callsReady_of_rounds')
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactStagePackage
  (StageData' records' exactStageData)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor
  (CursorInv cursorWord cursorWord_saturate cursorWidth clauseEnvelope)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields (stageEntryWidth stageDen)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageJoin (exactStageBlock_at_uniform_caps)
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry)
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule (clauseBitsSchedule widthAt)
open NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound (fuelAt)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank callFuel callMachine)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierStage
  (CallsReady stage stageFuel stageStates)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

section Abstract

variable {Atom : Type}

theorem rounds'_of_cursor (extra : ℕ) {bs : ℕ} (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth width envelope cursorTape : ℕ)
    (pfx : ℕ → List Entry) (input witness : List Bool)
    (Rest : (ℕ → List Bool) → Prop)
    (hsat : ∀ j : ℕ, envelope ≤ j → pfx j = pfx envelope)
    (hsite : ∀ j : ℕ, j < envelope → ∀ s : ℕ → List Bool,
      CursorInv width envelope cursorTape Rest j s →
      ∃ s' : ℕ → List Bool, CursorInv width envelope cursorTape Rest (j + 1) s' ∧
        Step body cost (fun _ => 0)
          (prefixBank extra entryWidth (pfx j) input witness s)
          (fun _ => 0)
          (prefixBank extra entryWidth (pfx (j + 1)) input witness s'))
    (hidle : ∀ s : ℕ → List Bool,
      s cursorTape = cursorWord width envelope envelope → Rest s →
      ∃ s' : ℕ → List Bool, s' cursorTape = cursorWord width envelope envelope ∧ Rest s' ∧
        Step body cost (fun _ => 0)
          (prefixBank extra entryWidth (pfx envelope) input witness s)
          (fun _ => 0)
          (prefixBank extra entryWidth (pfx envelope) input witness s')) :
    Rounds' extra body cost entryWidth pfx input witness
      (CursorInv width envelope cursorTape Rest) := by
  intro j s hinv
  rcases Nat.lt_or_ge j envelope with hj | hj
  · exact hsite j hj s hinv
  · have hcur : s cursorTape = cursorWord width envelope envelope := by
      rw [hinv.1, cursorWord_saturate width envelope j hj]
    obtain ⟨s', hcur', hrest', hstep⟩ := hidle s hcur hinv.2
    refine ⟨s', ⟨?_, hrest'⟩, ?_⟩
    · rw [hcur', (cursorWord_saturate width envelope (j + 1) (by omega)).symm]
    · rw [hsat j hj, hsat (j + 1) (by omega)]
      exact hstep

end Abstract

/-! ## §2 The same at the exact-fraction record family and the paper's own envelope -/

section Primed

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-- **`Rounds'` at the exact-fraction prefix family.**  `hsat` is
`prefixRecords'_saturate` (`Proof/CaseAnalysis/FinalExactRecordLoop.lean`) at
both ends, and `hfit` is the only premise it needs: `paper.tex:4516`'s
branch-independent clause index dominates this branch's own `clauseBits`. -/
theorem rounds'_at_clauseEnvelope (extra : ℕ) {bs : ℕ}
    (body : Machine (218 + (60 + extra)) bs)
    (cost entryWidth cursorTape clauseDegree q : ℕ)
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (input witness : List Bool) (Rest : (ℕ → List Bool) → Prop)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hsite : ∀ j : ℕ, j < clauseEnvelope clauseDegree q → ∀ s : ℕ → List Bool,
      CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest j s →
      ∃ s' : ℕ → List Bool,
        CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest
          (j + 1) s' ∧
        Step body cost (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record j) input witness s)
          (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record (j + 1))
            input witness s'))
    (hidle : ∀ s : ℕ → List Bool,
      s cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
        (clauseEnvelope clauseDegree q) → Rest s →
      ∃ s' : ℕ → List Bool,
        s' cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
          (clauseEnvelope clauseDegree q) ∧ Rest s' ∧
        Step body cost (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record
              (clauseEnvelope clauseDegree q)) input witness s)
          (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record
              (clauseEnvelope clauseDegree q)) input witness s')) :
    Rounds' extra body cost entryWidth
      (prefixRecords' phase pcpp coordinate systematicAtom record) input witness
      (CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest) := by
  have henv : 2 ^ pcpp.clauseBits ≤ clauseEnvelope clauseDegree q :=
    Nat.pow_le_pow_right (by omega) hfit
  refine rounds'_of_cursor extra body cost entryWidth (cursorWidth clauseDegree q)
    (clauseEnvelope clauseDegree q) cursorTape
    (prefixRecords' phase pcpp coordinate systematicAtom record) input witness Rest ?_ hsite hidle
  intro j hj
  rw [prefixRecords'_saturate phase pcpp coordinate systematicAtom record (le_trans henv hj),
    prefixRecords'_saturate phase pcpp coordinate systematicAtom record henv]

/-! ## §3 `CallsReady` from the bounded family, the idle round, and the prologue -/

/-- **`callsReady_of_cursor` (`Proof/CaseAnalysis/FinalRoundCursor.lean`) at
A.13.9's own per-call denominator.**  One application of `callsReady_of_rounds'`
(`Proof/CaseAnalysis/FinalExactRecordLoop.lean`), so the object produced is
byte-for-byte the `CallsReady`
(`Proof/CaseAnalysis/FinalSupplierStage.lean`) that `stage_run'`
(`Proof/CaseAnalysis/FinalExactRecordLoop.lean`) consumes, at the stream the
loop actually delivers.

`AddressDeterminacy` (`Proof/CaseAnalysis/FinalRoundEmitter.lean`) is not
mentioned here or anywhere below it: the cursor replaces it, which matters
because `f32.md` §0e #9 records that hypothesis as probably FALSE on this
route. -/
theorem callsReady'_of_cursor (extra : ℕ) {ps bs : ℕ}
    (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs)
    (phase : Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (record : Fin (2 ^ pcpp.clauseBits) → CircuitMonomial Atom 4 → Entry)
    (entryWidth callCount preFuel cost clauseDegree q cursorTape : ℕ)
    (input witness : List Bool) (Rest : (ℕ → List Bool) → Prop)
    (hlen : (phaseRecords' phase pcpp coordinate systematicAtom record).length = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree q)
    (hsite : ∀ j : ℕ, j < clauseEnvelope clauseDegree q → ∀ s : ℕ → List Bool,
      CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest j s →
      ∃ s' : ℕ → List Bool,
        CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest
          (j + 1) s' ∧
        Step body cost (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record j) input witness s)
          (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record (j + 1))
            input witness s'))
    (hidle : ∀ s : ℕ → List Bool,
      s cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
        (clauseEnvelope clauseDegree q) → Rest s →
      ∃ s' : ℕ → List Bool,
        s' cursorTape = cursorWord (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q)
          (clauseEnvelope clauseDegree q) ∧ Rest s' ∧
        Step body cost (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record
              (clauseEnvelope clauseDegree q)) input witness s)
          (fun _ => 0)
          (prefixBank extra entryWidth
            (prefixRecords' phase pcpp coordinate systematicAtom record
              (clauseEnvelope clauseDegree q)) input witness s'))
    (hpre : ∃ w : ℕ → List Bool,
      CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest 0 w ∧
      Step pre preFuel (fun _ => 0)
        (bank [] [] [] input witness (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree q)))) :
    CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel preFuel (clauseWidth clauseDegree q) cost) entryWidth callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words entryWidth
        (phaseRecords' phase pcpp coordinate systematicAtom record))
      input witness :=
  callsReady_of_rounds' extra pre body phase pcpp coordinate systematicAtom record
    entryWidth callCount preFuel cost clauseDegree q input witness
    (CursorInv (cursorWidth clauseDegree q) (clauseEnvelope clauseDegree q) cursorTape Rest)
    hlen hfit
    (rounds'_at_clauseEnvelope extra body cost entryWidth cursorTape clauseDegree q phase pcpp
      coordinate systematicAtom record input witness Rest hfit hsite hidle)
    hpre

end Primed

section Stage

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-- The exact-fraction record of a `StageData'`, named so the round obligations
below fit on the page.  This IS what `records'`
(`Proof/CaseAnalysis/FinalExactStagePackage.lean`) is built from. -/
def exactRecord (S : StageData' sources k p) {n : ℕ} (x : BitInput n) (bits : List Bool) :
    Fin (2 ^ (pcppOf sources k p x bits).clauseBits) →
      CircuitMonomial (Atoms sources k p x bits) 4 → Entry :=
  exactFractionRecord (2 ^ (pcppOf sources k p x bits).clauseBits) (S.num n x bits)
    (S.den n x bits)

theorem exactHcalls_of_cursor (S : StageData' sources k p)
    (e : ℕ) {ps bs : Phase → ℕ}
    (pre : (ph : Phase) → Machine (218 + (60 + e) + 1) (ps ph))
    (body : (ph : Phase) → Machine (218 + (60 + e)) (bs ph))
    (entryWidth preFuel cost q : ℕ → ℕ) (clauseDegree cursorTape : ℕ)
    (Rest : ℕ → Phase → (ℕ → List Bool) → Prop)
    (hfit : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n →
      (pcppOf sources k p x bits).clauseBits ≤ clauseWidth clauseDegree (q n))
    (hsite : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph : Phase,
      ∀ j : ℕ, j < clauseEnvelope clauseDegree (q n) → ∀ s : ℕ → List Bool,
        CursorInv (cursorWidth clauseDegree (q n)) (clauseEnvelope clauseDegree (q n))
          cursorTape (Rest n ph) j s →
        ∃ s' : ℕ → List Bool,
          CursorInv (cursorWidth clauseDegree (q n)) (clauseEnvelope clauseDegree (q n))
            cursorTape (Rest n ph) (j + 1) s' ∧
          Step (body ph) (cost n) (fun _ => 0)
            (prefixBank e (entryWidth n)
              (prefixRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits)
                Atom.systematic (exactRecord sources k p S x bits) j)
              (List.ofFn x) bits s)
            (fun _ => 0)
            (prefixBank e (entryWidth n)
              (prefixRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits)
                Atom.systematic (exactRecord sources k p S x bits) (j + 1))
              (List.ofFn x) bits s'))
    (hidle : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph : Phase,
      ∀ s : ℕ → List Bool,
        s cursorTape = cursorWord (cursorWidth clauseDegree (q n))
          (clauseEnvelope clauseDegree (q n)) (clauseEnvelope clauseDegree (q n)) →
        Rest n ph s →
        ∃ s' : ℕ → List Bool,
          s' cursorTape = cursorWord (cursorWidth clauseDegree (q n))
            (clauseEnvelope clauseDegree (q n)) (clauseEnvelope clauseDegree (q n)) ∧
          Rest n ph s' ∧
          Step (body ph) (cost n) (fun _ => 0)
            (prefixBank e (entryWidth n)
              (prefixRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits)
                Atom.systematic (exactRecord sources k p S x bits)
                (clauseEnvelope clauseDegree (q n))) (List.ofFn x) bits s)
            (fun _ => 0)
            (prefixBank e (entryWidth n)
              (prefixRecords' ph (pcppOf sources k p x bits) (S.coordinate n x bits)
                Atom.systematic (exactRecord sources k p S x bits)
                (clauseEnvelope clauseDegree (q n))) (List.ofFn x) bits s'))
    (hpre : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph : Phase,
      ∃ w : ℕ → List Bool,
        CursorInv (cursorWidth clauseDegree (q n)) (clauseEnvelope clauseDegree (q n))
          cursorTape (Rest n ph) 0 w ∧
        Step (pre ph) (preFuel n) (fun _ => 0)
          (bank [] [] [] (List.ofFn x) bits (fun _ => []))
          (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
          (Fin.addCases (motive := fun _ => List Bool)
            (bank [] (CompareMachine.word 0) (List.replicate (entryWidth n) true)
              (List.ofFn x) bits w)
            (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q n))))) :
    ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
      Soundness.cutoff (constantsOf sources) ≤ n → ∀ ph : Phase,
        CallsReady (e + 2) (callMachine e (pre ph) (body ph))
          (callFuel (preFuel n) (clauseWidth clauseDegree (q n)) (cost n))
          (entryWidth n)
          (records' sources k p S x bits ph).length
          (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth n)
            (records' sources k p S x bits ph))
          (List.ofFn x) bits := by
  intro n x bits hn ph
  exact callsReady'_of_cursor e (pre ph) (body ph) ph (pcppOf sources k p x bits)
    (S.coordinate n x bits) Atom.systematic (exactRecord sources k p S x bits)
    (entryWidth n) (records' sources k p S x bits ph).length (preFuel n) (cost n)
    clauseDegree (q n) cursorTape (List.ofFn x) bits (Rest n ph) rfl (hfit n x bits hn)
    (hsite n x bits hn ph) (hidle n x bits hn ph) (hpre n x bits hn ph)

/-! ## §5 `hfit` is not open: it is `clauseBits_le_schedule`, up to ONE onset

`clauseBits_le_schedule`
(`Proof/CaseAnalysis/FinalClauseBitsUniform.lean`) already proves `hfit` at
`paper.tex:4516`'s own schedule, from `Parameters.clauses`
(`Proof/CaseAnalysis/FinalResidualLeaves.lean`) alone.  What it carries and
`hcalls` does not is an ONSET: `hcalls`'s guard is
`Soundness.cutoff (constantsOf sources)`.  The gap between the two is named here
and NOT smuggled -- it is the same gap `stage_field_hfuel`'s and
`stageReady_at_polyFuel`'s `hfit` carry (`Proof/CaseAnalysis/FinalClauseBitsUniform.lean`
§8), so it is SHARED, not new. -/

/-! ## §6 The plug, TYPE-CHECKED rather than transcribed -/

end Stage

end


end NearCubicWires.RepairOrdinary.CloseoutFinalC10ExactCallLoopJoin
