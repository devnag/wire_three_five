import Proof.Circuits.CallableRelocation
import Proof.MachineModel.CanonicalBitSerialModProgram
import Proof.MachineModel.CanonicalNatValidationProgram
import Proof.MachineModel.CanonicalTaggedTupleProgram
import Proof.Circuits.CanonicalWitnessCodec
import Proof.MachineModel.PreserveRightProgram
import Proof.Circuits.RegisterBounds
import Proof.Foundations.VerifiedLinker

/-!
# Total canonical-rational validation

A legal coefficient has one public representation: a two-cell tagged tuple
containing a canonical signed numerator and a positive canonical denominator.
This module validates that representation with one fixed interpreter pipeline.
Reducedness is decided by an executable Euclidean controller whose only
remainder implementation is the shared bit-serial modulo program.
-/

namespace NearCubicWires.CanonicalRationalValidationProgram

open NearCubicWires
open NearCubicWires.CallableRelocation
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalNatValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RegisterBounds
open NearCubicWires.VerifiedLinker

/-! ## Euclidean gcd with one relocated modulo implementation -/

/-! ## The polynomial charge of the Euclidean controller

Each Euclidean step charges one relocated bit-serial remainder, whose budget is
linear in the numerator's binary width.  What remains is the step count: a
remainder is at most half of its own dividend, so two steps at least halve the
second operand and the controller runs for at most `2 * natBitLength right + 2`
steps.  Neither factor contains an operand magnitude. -/

/-! ## Fixed rational-field projection and canonical Nat stages -/

def rationalTupleOutput (raw : ℕ) : ℕ :=
  taggedTupleOutput 2 raw

def rationalTupleFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleOutput raw)).1

def rationalTupleFields (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleOutput raw)).2

def rationalNumeratorFrame (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleFields raw)).1

def rationalNumeratorCode (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalNumeratorFrame raw)).2

def rationalDenominatorCode (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalTupleFields raw)).2

def rationalSign (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalNumeratorCode raw)).1

def rationalMagnitudeCode (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalNumeratorCode raw)).2

def rationalMagnitudeValidation (raw : ℕ) : ℕ :=
  canonicalNatValidationOutput (rationalMagnitudeCode raw)

def rationalDenominatorValidation (raw : ℕ) : ℕ :=
  canonicalNatValidationOutput (rationalDenominatorCode raw)

def rationalMagnitudeValue (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalMagnitudeValidation raw)).2

def rationalDenominatorValue (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalDenominatorValidation raw)).2

def rationalGcdValue (raw : ℕ) : ℕ :=
  Nat.gcd (rationalMagnitudeValue raw) (rationalDenominatorValue raw)

def rationalMagnitudeFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalMagnitudeValidation raw)).1

def rationalDenominatorFlag (raw : ℕ) : ℕ :=
  (Nat.unpair (rationalDenominatorValidation raw)).1

def rationalValidationAccepts (raw : ℕ) : Prop :=
  rationalTupleFlag raw ≠ 0 ∧
  rationalMagnitudeFlag raw ≠ 0 ∧
  rationalDenominatorFlag raw ≠ 0 ∧
  rationalDenominatorValue raw ≠ 0 ∧
  rationalGcdValue raw = 1 ∧
  (rationalSign raw = 0 ∨
    (rationalSign raw = 1 ∧ rationalMagnitudeValue raw ≠ 0))

/-! ## Unique total rational validator -/

theorem rationalValidationAccepts_encodeCanonicalRational
    (coefficient : ℚ) :
    rationalValidationAccepts (encodeCanonicalRational coefficient) := by
  have hgcd : coefficient.num.natAbs.gcd coefficient.den = 1 :=
    coefficient.reduced.gcd_eq_one
  have htuple :
      rationalTupleOutput (encodeCanonicalRational coefficient) =
        Nat.pair 1
          (Nat.pair (Nat.pair 0 (encodeInt coefficient.num))
            (encodeNat coefficient.den)) := by
    unfold rationalTupleOutput taggedTupleOutput encodeCanonicalRational
    rw [show (2 : ℕ) =
      [encodeInt coefficient.num, encodeNat coefficient.den].length by rfl]
    rw [decodeTaggedTuple_encode]
    rfl
  by_cases hnegative : coefficient.num < 0
  · have hmagnitude : coefficient.num.natAbs ≠ 0 := by
      exact Int.natAbs_ne_zero.mpr (by omega)
    simp [rationalValidationAccepts, rationalTupleFlag, htuple,
      rationalTupleFields,
      rationalNumeratorFrame, rationalNumeratorCode, rationalDenominatorCode,
      rationalSign, rationalMagnitudeCode, rationalMagnitudeFlag,
      rationalMagnitudeValidation, rationalMagnitudeValue,
      rationalDenominatorFlag, rationalDenominatorValidation,
      rationalDenominatorValue, rationalGcdValue, encodeInt,
      hnegative, hmagnitude, coefficient.den_nz, hgcd]
  · simp [rationalValidationAccepts, rationalTupleFlag, htuple,
      rationalTupleFields,
      rationalNumeratorFrame, rationalNumeratorCode, rationalDenominatorCode,
      rationalSign, rationalMagnitudeCode, rationalMagnitudeFlag,
      rationalMagnitudeValidation, rationalMagnitudeValue,
      rationalDenominatorFlag, rationalDenominatorValidation,
      rationalDenominatorValue, rationalGcdValue, encodeInt,
      hnegative, coefficient.den_nz, hgcd]

theorem rationalValidationAccepts_iff_decodeCanonicalRational
    (raw : ℕ) :
    rationalValidationAccepts raw ↔
      ∃ coefficient, decodeCanonicalRational raw = some coefficient := by
  constructor
  · rintro ⟨htupleFlag, hmagnitudeFlag, hdenominatorFlag,
      hdenominatorNonzero, hgcd, hsign⟩
    have htupleOutput : rationalTupleOutput raw ≠ 0 := by
      intro hzero
      apply htupleFlag
      simp [rationalTupleFlag, hzero]
    obtain ⟨values, hlength, hcode⟩ :=
      (taggedTupleOutput_ne_zero_iff 2 raw).mp htupleOutput
    cases values with
    | nil => simp at hlength
    | cons numeratorCode rest =>
        cases rest with
        | nil => simp at hlength
        | cons denominatorCode rest =>
            cases rest with
            | cons extra tail => simp at hlength
            | nil =>
                have hraw :
                    raw =
                      encodeTaggedList [numeratorCode, denominatorCode] :=
                  hcode.symm
                subst raw
                have htuple :
                    rationalTupleOutput
                        (encodeTaggedList
                          [numeratorCode, denominatorCode]) =
                      Nat.pair 1
                        (Nat.pair (Nat.pair 0 numeratorCode)
                          denominatorCode) := by
                  unfold rationalTupleOutput taggedTupleOutput
                  rw [show (2 : ℕ) =
                    [numeratorCode, denominatorCode].length by rfl]
                  rw [decodeTaggedTuple_encode]
                  rfl
                have hmagnitudeFlag' :
                    (Nat.unpair
                      (canonicalNatValidationOutput
                        (Nat.unpair numeratorCode).2)).1 ≠ 0 := by
                  simpa [rationalMagnitudeFlag, rationalMagnitudeValidation,
                    rationalMagnitudeCode, rationalNumeratorCode,
                    rationalNumeratorFrame, rationalTupleFields, htuple] using
                    hmagnitudeFlag
                have hmagnitudeOutput :
                    canonicalNatValidationOutput
                        (Nat.unpair numeratorCode).2 ≠ 0 := by
                  intro hzero
                  apply hmagnitudeFlag'
                  simp [hzero]
                obtain ⟨magnitude, hmagnitudeDecode⟩ :=
                  (canonicalNatValidationOutput_ne_zero_iff
                    (Nat.unpair numeratorCode).2).mp hmagnitudeOutput
                have hdenominatorFlag' :
                    (Nat.unpair
                      (canonicalNatValidationOutput denominatorCode)).1 ≠ 0 := by
                  simpa [rationalDenominatorFlag,
                    rationalDenominatorValidation, rationalDenominatorCode,
                    rationalTupleFields, htuple] using hdenominatorFlag
                have hdenominatorOutput :
                    canonicalNatValidationOutput denominatorCode ≠ 0 := by
                  intro hzero
                  apply hdenominatorFlag'
                  simp [hzero]
                obtain ⟨denominator, hdenominatorDecode⟩ :=
                  (canonicalNatValidationOutput_ne_zero_iff
                    denominatorCode).mp hdenominatorOutput
                have hmagnitudeValidation :=
                  canonicalNatValidationOutput_of_decode hmagnitudeDecode
                have hdenominatorValidation :=
                  canonicalNatValidationOutput_of_decode hdenominatorDecode
                have hmagnitudeValue :
                    rationalMagnitudeValue
                        (encodeTaggedList
                          [numeratorCode, denominatorCode]) =
                      magnitude := by
                  simp [rationalMagnitudeValue, rationalMagnitudeValidation,
                    rationalMagnitudeCode, rationalNumeratorCode,
                    rationalNumeratorFrame, rationalTupleFields, htuple,
                    hmagnitudeValidation]
                have hdenominatorValue :
                    rationalDenominatorValue
                        (encodeTaggedList
                          [numeratorCode, denominatorCode]) =
                      denominator := by
                  simp [rationalDenominatorValue,
                    rationalDenominatorValidation, rationalDenominatorCode,
                    rationalTupleFields, htuple, hdenominatorValidation]
                have hdenominatorNonzero' : denominator ≠ 0 := by
                  simpa [hdenominatorValue] using hdenominatorNonzero
                have hgcd' : magnitude.gcd denominator = 1 := by
                  simpa [rationalGcdValue, hmagnitudeValue,
                    hdenominatorValue] using hgcd
                have hsign' :
                    (Nat.unpair numeratorCode).1 = 0 ∨
                      ((Nat.unpair numeratorCode).1 = 1 ∧ magnitude ≠ 0) := by
                  simpa [rationalSign, rationalNumeratorCode,
                    rationalNumeratorFrame, rationalTupleFields, htuple,
                    hmagnitudeValue] using hsign
                have hmagnitudeCode :
                    encodeNat magnitude = (Nat.unpair numeratorCode).2 :=
                  encodeNat_of_decode hmagnitudeDecode
                have hdenominatorCode :
                    encodeNat denominator = denominatorCode :=
                  encodeNat_of_decode hdenominatorDecode
                have hfinish (numerator : ℤ)
                    (hnatAbs : numerator.natAbs = magnitude)
                    (hnumeratorCode : encodeInt numerator = numeratorCode) :
                    ∃ coefficient,
                      decodeCanonicalRational
                          (encodeTaggedList
                            [numeratorCode, denominatorCode]) =
                        some coefficient := by
                  have hreduced : numerator.natAbs.Coprime denominator := by
                    rw [hnatAbs]
                    exact Nat.coprime_iff_gcd_eq_one.mpr hgcd'
                  let coefficient : ℚ :=
                    { num := numerator
                      den := denominator
                      den_nz := hdenominatorNonzero'
                      reduced := hreduced }
                  refine ⟨coefficient, ?_⟩
                  have hcanonical :
                      encodeCanonicalRational coefficient =
                        encodeTaggedList
                          [numeratorCode, denominatorCode] := by
                    simp only [encodeCanonicalRational, coefficient]
                    rw [hnumeratorCode, hdenominatorCode]
                  rw [← hcanonical]
                  exact decodeCanonicalRational_encode coefficient
                rcases hsign' with hsignZero |
                    ⟨hsignOne, hmagnitudeNonzero⟩
                · apply hfinish (magnitude : ℤ)
                  · simp
                  · calc
                      encodeInt (magnitude : ℤ) =
                          Nat.pair 0 (encodeNat magnitude) := by
                            simp [encodeInt]
                      _ = Nat.pair (Nat.unpair numeratorCode).1
                          (Nat.unpair numeratorCode).2 := by
                            rw [hsignZero, hmagnitudeCode]
                      _ = numeratorCode := Nat.pair_unpair numeratorCode
                · apply hfinish (-(magnitude : ℤ))
                  · simp
                  · calc
                      encodeInt (-(magnitude : ℤ)) =
                          Nat.pair 1 (encodeNat magnitude) := by
                            simp [encodeInt, hmagnitudeNonzero]
                      _ = Nat.pair (Nat.unpair numeratorCode).1
                          (Nat.unpair numeratorCode).2 := by
                            rw [hsignOne, hmagnitudeCode]
                      _ = numeratorCode := Nat.pair_unpair numeratorCode
  · rintro ⟨coefficient, hdecode⟩
    have hcode := encodeCanonicalRational_of_decode hdecode
    rw [← hcode]
    exact rationalValidationAccepts_encodeCanonicalRational coefficient

end NearCubicWires.CanonicalRationalValidationProgram
