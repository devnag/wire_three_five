import Proof.MachineModel.CanonicalTaggedListValidationProgram
import Proof.Circuits.RegisterBounds

/-!
# Fixed-arity canonical tagged tuples

All fixed records in the recovery witness use the same tagged-list codec.  This
module deconstructs exactly `arity` canonical cells in one pass and returns the
fields in a private reverse-pair accumulator.  The arity is an immediate in
the program text, never caller data; malformed tags, short/long lists, and
nonzero terminators all reach the single zero result.
-/

namespace NearCubicWires.CanonicalTaggedTupleProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds

/-- Private reverse-pair representation used only between fixed compiler
stages.  It is not an accepted public witness encoding. -/
def reversePairFields : List ℕ → ℕ :=
  List.foldl Nat.pair 0

/-- Total semantic view of the fixed tuple loop. -/
def decodeTaggedTupleAux :
    ℕ → ℕ → ℕ → Option ℕ
  | 0, cursor, accumulator =>
      if cursor = 0 then some accumulator else none
  | remaining + 1, cursor, accumulator =>
      if cursor = 0 then
        none
      else
        let outer := Nat.unpair cursor
        if outer.1 = 1 then
          let payload := Nat.unpair outer.2
          decodeTaggedTupleAux remaining payload.2
            (Nat.pair accumulator payload.1)
        else
          none

def decodeTaggedTuple (arity raw : ℕ) : Option ℕ :=
  decodeTaggedTupleAux arity raw 0

def taggedTupleOutput (arity raw : ℕ) : ℕ :=
  match decodeTaggedTuple arity raw with
  | some fields => Nat.pair 1 fields
  | none => 0

@[simp] theorem decodeTaggedTupleAux_encode
    (values : List ℕ) (accumulator : ℕ) :
    decodeTaggedTupleAux values.length (encodeTaggedList values)
        accumulator =
      some (values.foldl Nat.pair accumulator) := by
  induction values generalizing accumulator with
  | nil =>
      simp [decodeTaggedTupleAux, encodeTaggedList]
  | cons value values inductionHypothesis =>
      have hnonzero :
          Nat.pair 1 (Nat.pair value (encodeTaggedList values)) ≠ 0 := by
        have hleft :=
          Nat.left_le_pair 1
            (Nat.pair value (encodeTaggedList values))
        omega
      simp [encodeTaggedList, decodeTaggedTupleAux, hnonzero,
        inductionHypothesis]

@[simp] theorem decodeTaggedTuple_encode (values : List ℕ) :
    decodeTaggedTuple values.length (encodeTaggedList values) =
      some (reversePairFields values) := by
  exact decodeTaggedTupleAux_encode values 0

private theorem decodeTaggedTupleAux_eq_some_iff
    (arity raw accumulator fields : ℕ) :
    decodeTaggedTupleAux arity raw accumulator = some fields ↔
      ∃ values,
        values.length = arity ∧
        encodeTaggedList values = raw ∧
        values.foldl Nat.pair accumulator = fields := by
  constructor
  · induction arity generalizing raw accumulator fields with
    | zero =>
        intro hdecode
        simp only [decodeTaggedTupleAux] at hdecode
        split at hdecode
        · rename_i hzero
          simp only [Option.some.injEq] at hdecode
          subst fields
          exact ⟨[], rfl, hzero.symm, rfl⟩
        · simp at hdecode
    | succ arity inductionHypothesis =>
        intro hdecode
        simp only [decodeTaggedTupleAux] at hdecode
        split at hdecode
        · simp at hdecode
        · rename_i hcursor
          split at hdecode
          · rename_i htag
            let outer := Nat.unpair raw
            let payload := Nat.unpair outer.2
            obtain ⟨values, hlength, hcode, hfields⟩ :=
              (inductionHypothesis
                (raw := payload.2)
                (accumulator := Nat.pair accumulator payload.1)
                (fields := fields))
                hdecode
            refine
              ⟨payload.1 :: values, by simp [hlength], ?_, ?_⟩
            · rw [encodeTaggedList, hcode]
              calc
                Nat.pair 1
                    (Nat.pair payload.1 payload.2) =
                    Nat.pair outer.1 outer.2 := by
                  rw [htag, Nat.pair_unpair]
                _ = raw := Nat.pair_unpair raw
            · simpa using hfields
          · simp at hdecode
  · rintro ⟨values, hlength, hcode, hfields⟩
    subst arity
    subst raw
    rw [decodeTaggedTupleAux_encode, hfields]

theorem decodeTaggedTuple_eq_some_iff
    (arity raw fields : ℕ) :
    decodeTaggedTuple arity raw = some fields ↔
      ∃ values,
        values.length = arity ∧
        encodeTaggedList values = raw ∧
        reversePairFields values = fields := by
  simpa [decodeTaggedTuple, reversePairFields] using
    decodeTaggedTupleAux_eq_some_iff arity raw 0 fields

theorem taggedTupleOutput_ne_zero_iff
    (arity raw : ℕ) :
    taggedTupleOutput arity raw ≠ 0 ↔
      ∃ values,
        values.length = arity ∧ encodeTaggedList values = raw := by
  constructor
  · intro hnonzero
    cases hdecode : decodeTaggedTuple arity raw with
    | none =>
        simp [taggedTupleOutput, hdecode] at hnonzero
    | some fields =>
        obtain ⟨values, hlength, hcode, _⟩ :=
          (decodeTaggedTuple_eq_some_iff arity raw fields).mp hdecode
        exact ⟨values, hlength, hcode⟩
  · rintro ⟨values, hlength, hcode⟩
    have hdecode :
        decodeTaggedTuple arity raw =
          some (reversePairFields values) := by
      subst arity
      subst raw
      exact decodeTaggedTuple_encode values
    simp only [taggedTupleOutput, hdecode]
    have hpositive :
        0 < Nat.pair 1 (reversePairFields values) :=
      (show 0 < 1 by omega).trans_le
        (Nat.left_le_pair 1 (reversePairFields values))
    exact hpositive.ne'

/-! ## Fixed tuple deconstructor -/

end NearCubicWires.CanonicalTaggedTupleProgram
