import Proof.Foundations.TseitinCNF

/-!
# Canonical SAT prefix self-reduction

This module implements the one reusable search primitive required by the
C.12 recovery layer.  Starting from one canonical CNF, it asks whether the
current prefix can be extended with zero; only when that query is
unsatisfiable does it commit one.  The result is the reversed bit list of the
lexicographically first model prefix.  Formula construction and every SAT
query occur inside one fixed `NPOracleProgram`.
-/

namespace NearCubicWires.CanonicalSATSelfReduction

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.TseitinCNF

def prefixUnitClause (value : Bool) (index : ℕ) : EncodedClause :=
  if value then positiveUnit index else negativeUnit index

def constrainPrefixBit
    (value : Bool) (index : ℕ) (formula : EncodedCNF) : EncodedCNF :=
  prefixUnitClause value index :: formula

def canonicalSatBit (formula : EncodedCNF) : Bool :=
  encodedSat (Encodable.encode formula)

structure PrefixSATResult where
  constrainedFormula : EncodedCNF
  reverseBits : List Bool

def prefixSATScan :
    ℕ → ℕ → EncodedCNF → List Bool → PrefixSATResult
  | 0, _index, formula, reverseBits =>
      ⟨formula, reverseBits⟩
  | count + 1, index, formula, reverseBits =>
      let zeroFormula := constrainPrefixBit false index formula
      if canonicalSatBit zeroFormula then
        prefixSATScan count (index + 1) zeroFormula
          (false :: reverseBits)
      else
        let oneFormula := constrainPrefixBit true index formula
        prefixSATScan count (index + 1) oneFormula
          (true :: reverseBits)

def prefixSATChoices : ℕ → ℕ → EncodedCNF → List Bool
  | 0, _index, _formula => []
  | count + 1, index, formula =>
      let zeroFormula := constrainPrefixBit false index formula
      if canonicalSatBit zeroFormula then
        false :: prefixSATChoices count (index + 1) zeroFormula
      else
        true :: prefixSATChoices count (index + 1)
          (constrainPrefixBit true index formula)

def recoveredPrefix (count : ℕ) (formula : EncodedCNF) : List Bool :=
  prefixSATChoices count 0 formula

def constrainPrefixChoices :
    ℕ → EncodedCNF → List Bool → EncodedCNF
  | _index, formula, [] => formula
  | index, formula, value :: rest =>
      constrainPrefixChoices (index + 1)
        (constrainPrefixBit value index formula) rest

@[simp] theorem prefixSATChoices_length
    (count index : ℕ) (formula : EncodedCNF) :
    (prefixSATChoices count index formula).length = count := by
  induction count generalizing index formula with
  | zero =>
      rfl
  | succ count ih =>
      unfold prefixSATChoices
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        simp only [List.length_cons, ih]
      · rw [if_neg hzero]
        simp only [List.length_cons, ih]

theorem prefixSATScan_constrainedFormula_eq
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool) :
    (prefixSATScan count index formula reverseBits).constrainedFormula =
      constrainPrefixChoices index formula
        (prefixSATChoices count index formula) := by
  induction count generalizing index formula reverseBits with
  | zero =>
      rfl
  | succ count ih =>
      unfold prefixSATScan prefixSATChoices
      by_cases hzero :
          canonicalSatBit (constrainPrefixBit false index formula) = true
      · rw [if_pos hzero]
        simpa only [hzero, if_pos, constrainPrefixChoices] using
          ih (index + 1) (constrainPrefixBit false index formula)
            (false :: reverseBits)
      · rw [if_neg hzero]
        simpa only [hzero, Bool.false_eq_true, if_false,
          constrainPrefixChoices] using
          ih (index + 1) (constrainPrefixBit true index formula)
            (true :: reverseBits)

@[simp] theorem recoveredPrefix_length
    (count : ℕ) (formula : EncodedCNF) :
    (recoveredPrefix count formula).length = count :=
  prefixSATChoices_length count 0 formula

/-! ## Fixed interpreter -/

private theorem encode_list_tail_le
    {α : Type} [Encodable α] (head : α) (tail : List α) :
    Encodable.encode tail ≤ Encodable.encode (head :: tail) := by
  rw [Encodable.encode_list_cons]
  have hpair :=
    Nat.right_le_pair (Encodable.encode head) (Encodable.encode tail)
  omega

/-! ## Semantic self-reduction contract -/

@[simp] theorem formulaEval_constrainPrefixBit
    (assignment : ℕ → Bool) (value : Bool) (index : ℕ)
    (formula : EncodedCNF) :
    formulaEval assignment (constrainPrefixBit value index formula) = true ↔
      assignment index = value ∧ formulaEval assignment formula = true := by
  cases value <;> cases hbit : assignment index <;>
    simp [constrainPrefixBit, prefixUnitClause, formulaEval,
      hbit]

private theorem constrainPrefixBit_code_mono
    (value : Bool) (index : ℕ) (formula : EncodedCNF) :
    Encodable.encode formula ≤
      Encodable.encode (constrainPrefixBit value index formula) := by
  unfold constrainPrefixBit
  exact encode_list_tail_le _ _

/-- Prefix clauses preserve the SAT opcode's syntactic guard whenever the
queried variable already lies inside the original canonical code bound. -/
theorem constrainPrefixBit_wellSized
    (value : Bool) (index : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hindex : index < natBitLength (Encodable.encode formula)) :
    wellSizedCNFEncoding
        (Encodable.encode (constrainPrefixBit value index formula))
        (constrainPrefixBit value index formula) = true := by
  have hcode :
      Encodable.encode formula ≤
        Encodable.encode (constrainPrefixBit value index formula) :=
    constrainPrefixBit_code_mono value index formula
  have hindexNew :
      index <
        natBitLength
          (Encodable.encode (constrainPrefixBit value index formula)) :=
    lt_of_lt_of_le hindex (natBitLength_mono hcode)
  rw [wellSizedCNFEncoding, Bool.and_eq_true]
  constructor
  · exact decide_eq_true
      (list_length_le_encoded_bitLength
        (constrainPrefixBit value index formula))
  · rw [wellSizedCNFEncoding, Bool.and_eq_true] at hwell
    have hold := hwell.2
    unfold constrainPrefixBit
    rw [List.all_cons, Bool.and_eq_true]
    constructor
    · cases value <;>
        simp [prefixUnitClause, positiveUnit, negativeUnit, triple,
          positive, negative]
      all_goals
        simpa [constrainPrefixBit, prefixUnitClause, positiveUnit,
          negativeUnit, triple, positive, negative] using hindexNew
    · rw [List.all_eq_true] at hold ⊢
      intro clause hclause
      have hclauseOld := hold clause hclause
      rw [Bool.and_eq_true] at hclauseOld ⊢
      refine ⟨hclauseOld.1, ?_⟩
      rw [List.all_eq_true] at hclauseOld ⊢
      intro literal hliteral
      exact decide_eq_true <|
        (of_decide_eq_true (hclauseOld.2 literal hliteral)).trans_le
          (natBitLength_mono hcode)

def FormulaSatisfiable (formula : EncodedCNF) : Prop :=
  ∃ assignment : ℕ → Bool, formulaEval assignment formula = true

theorem FormulaSatisfiable.of_constrainPrefixChoices
    (index : ℕ) (formula : EncodedCNF) (choices : List Bool)
    (hsatisfiable :
      FormulaSatisfiable
        (constrainPrefixChoices index formula choices)) :
    FormulaSatisfiable formula := by
  induction choices generalizing index formula with
  | nil =>
      exact hsatisfiable
  | cons value rest ih =>
      have hconstrained :
          FormulaSatisfiable (constrainPrefixBit value index formula) :=
        ih (index + 1) (constrainPrefixBit value index formula)
          hsatisfiable
      rcases hconstrained with ⟨assignment, haccepts⟩
      exact
        ⟨assignment,
          (formulaEval_constrainPrefixBit assignment value index formula
            |>.mp haccepts).2⟩

theorem canonicalSatBit_eq_true_iff
    (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true) :
    canonicalSatBit formula = true ↔ FormulaSatisfiable formula := by
  exact encodedSat_encode_eq_true_iff formula hwell

theorem satisfiable_constrain_other
    (index : ℕ) (formula : EncodedCNF)
    (hsatisfiable : FormulaSatisfiable formula)
    (hzero : ¬FormulaSatisfiable
      (constrainPrefixBit false index formula)) :
    FormulaSatisfiable (constrainPrefixBit true index formula) := by
  rcases hsatisfiable with ⟨assignment, haccepts⟩
  refine ⟨assignment, ?_⟩
  rw [formulaEval_constrainPrefixBit]
  refine ⟨?_, haccepts⟩
  cases hbit : assignment index with
  | false =>
      exact False.elim <| hzero
        ⟨assignment,
          formulaEval_constrainPrefixBit assignment false index formula
            |>.mpr ⟨hbit, haccepts⟩⟩
  | true =>
      rfl

theorem prefixSATScan_preserves_satisfiable
    (count index : ℕ) (formula : EncodedCNF)
    (reverseBits : List Bool)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange :
      index + count ≤ natBitLength (Encodable.encode formula))
    (hsatisfiable : FormulaSatisfiable formula) :
    FormulaSatisfiable
      (prefixSATScan count index formula reverseBits).constrainedFormula := by
  induction count generalizing index formula reverseBits with
  | zero =>
      exact hsatisfiable
  | succ count ih =>
      let zeroFormula := constrainPrefixBit false index formula
      have hindex :
          index < natBitLength (Encodable.encode formula) := by
        omega
      have hzeroWell :
          wellSizedCNFEncoding (Encodable.encode zeroFormula)
              zeroFormula = true := by
        exact constrainPrefixBit_wellSized false index formula hwell hindex
      have hzeroRange :
          index + 1 + count ≤
            natBitLength (Encodable.encode zeroFormula) := by
        have hmono :=
          natBitLength_mono
            (constrainPrefixBit_code_mono false index formula)
        have hmono' :
            natBitLength (Encodable.encode formula) ≤
              natBitLength (Encodable.encode zeroFormula) := by
          simpa only [zeroFormula] using hmono
        omega
      by_cases hzero : canonicalSatBit zeroFormula = true
      · have hzeroSat : FormulaSatisfiable zeroFormula :=
          (canonicalSatBit_eq_true_iff zeroFormula hzeroWell).mp hzero
        have hrec :=
          ih (index + 1) zeroFormula (false :: reverseBits)
            hzeroWell hzeroRange hzeroSat
        simpa [prefixSATScan, zeroFormula, hzero] using hrec
      · let oneFormula := constrainPrefixBit true index formula
        have hzeroNotSat : ¬FormulaSatisfiable zeroFormula := by
          intro hzeroSat
          exact hzero
            ((canonicalSatBit_eq_true_iff zeroFormula hzeroWell).mpr
              hzeroSat)
        have honeSat : FormulaSatisfiable oneFormula :=
          satisfiable_constrain_other index formula hsatisfiable hzeroNotSat
        have honeWell :
            wellSizedCNFEncoding (Encodable.encode oneFormula)
                oneFormula = true := by
          exact constrainPrefixBit_wellSized true index formula hwell hindex
        have honeRange :
            index + 1 + count ≤
              natBitLength (Encodable.encode oneFormula) := by
          have hmono :=
            natBitLength_mono
              (constrainPrefixBit_code_mono true index formula)
          have hmono' :
              natBitLength (Encodable.encode formula) ≤
                natBitLength (Encodable.encode oneFormula) := by
            simpa only [oneFormula] using hmono
          omega
        have hrec :=
          ih (index + 1) oneFormula (true :: reverseBits)
            honeWell honeRange honeSat
        simpa [prefixSATScan, zeroFormula, oneFormula, hzero] using hrec

theorem recoveredPrefixFormula_satisfiable
    (count : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange : count ≤ natBitLength (Encodable.encode formula))
    (hsatisfiable : FormulaSatisfiable formula) :
    FormulaSatisfiable
      (prefixSATScan count 0 formula []).constrainedFormula := by
  exact prefixSATScan_preserves_satisfiable count 0 formula []
    hwell (by simpa using hrange) hsatisfiable

theorem recoveredPrefix_satisfiable
    (count : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange : count ≤ natBitLength (Encodable.encode formula))
    (hsatisfiable : FormulaSatisfiable formula) :
    FormulaSatisfiable
      (constrainPrefixChoices 0 formula (recoveredPrefix count formula)) := by
  unfold recoveredPrefix
  rw [← prefixSATScan_constrainedFormula_eq count 0 formula []]
  exact recoveredPrefixFormula_satisfiable count formula
    hwell hrange hsatisfiable

/-- The fixed zero-first self-reduction returns the lexicographically first
satisfiable prefix.  The range hypothesis is exactly what keeps every dynamic
SAT query inside the interpreter's canonical syntactic guard. -/
theorem prefixSATChoices_lexLeast
    (count index : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange :
      index + count ≤ natBitLength (Encodable.encode formula))
    (candidate : List Bool)
    (hlength : candidate.length = count)
    (hcandidate :
      FormulaSatisfiable
        (constrainPrefixChoices index formula candidate)) :
    CanonicalBoolListLE
      (prefixSATChoices count index formula) candidate := by
  induction count generalizing index formula candidate with
  | zero =>
      have hc : candidate = [] := List.eq_nil_of_length_eq_zero hlength
      subst candidate
      exact le_refl []
  | succ count ih =>
      cases candidate with
      | nil =>
          simp at hlength
      | cons candidateHead candidateTail =>
          have htailLength : candidateTail.length = count := by
            simp only [List.length_cons] at hlength
            omega
          let zeroFormula := constrainPrefixBit false index formula
          have hindex :
              index < natBitLength (Encodable.encode formula) := by
            omega
          have hzeroWell :
              wellSizedCNFEncoding (Encodable.encode zeroFormula)
                  zeroFormula = true :=
            constrainPrefixBit_wellSized false index formula hwell hindex
          have hzeroRange :
              index + 1 + count ≤
                natBitLength (Encodable.encode zeroFormula) := by
            have hmono :
                natBitLength (Encodable.encode formula) ≤
                  natBitLength (Encodable.encode zeroFormula) := by
              simpa only [zeroFormula] using
                natBitLength_mono
                  (constrainPrefixBit_code_mono false index formula)
            omega
          by_cases hzero : canonicalSatBit zeroFormula = true
          · cases candidateHead with
            | false =>
                have htail :=
                  ih (index + 1) zeroFormula hzeroWell hzeroRange
                    candidateTail htailLength hcandidate
                simpa only [prefixSATChoices, zeroFormula, hzero, if_pos,
                  CanonicalBoolListLE] using
                    (List.cons_le_cons false htail)
            | true =>
                simp only [prefixSATChoices, zeroFormula, hzero, if_pos,
                  CanonicalBoolListLE]
                exact le_of_lt (List.Lex.rel (by decide))
          · cases candidateHead with
            | false =>
                exfalso
                have hzeroSat : FormulaSatisfiable zeroFormula := by
                  exact FormulaSatisfiable.of_constrainPrefixChoices
                    (index + 1) zeroFormula candidateTail hcandidate
                exact hzero
                  ((canonicalSatBit_eq_true_iff zeroFormula hzeroWell).mpr
                    hzeroSat)
            | true =>
                let oneFormula := constrainPrefixBit true index formula
                have honeWell :
                    wellSizedCNFEncoding (Encodable.encode oneFormula)
                        oneFormula = true :=
                  constrainPrefixBit_wellSized true index formula hwell hindex
                have honeRange :
                    index + 1 + count ≤
                      natBitLength (Encodable.encode oneFormula) := by
                  have hmono :
                      natBitLength (Encodable.encode formula) ≤
                        natBitLength (Encodable.encode oneFormula) := by
                    simpa only [oneFormula] using
                      natBitLength_mono
                        (constrainPrefixBit_code_mono true index formula)
                  omega
                have htail :=
                  ih (index + 1) oneFormula honeWell honeRange
                    candidateTail htailLength hcandidate
                simpa only [prefixSATChoices, zeroFormula, oneFormula,
                  hzero, Bool.false_eq_true, if_false,
                  CanonicalBoolListLE] using
                    (List.cons_le_cons true htail)

theorem recoveredPrefix_lexLeast
    (count : ℕ) (formula : EncodedCNF)
    (hwell :
      wellSizedCNFEncoding (Encodable.encode formula) formula = true)
    (hrange : count ≤ natBitLength (Encodable.encode formula))
    (candidate : List Bool)
    (hlength : candidate.length = count)
    (hcandidate :
      FormulaSatisfiable
        (constrainPrefixChoices 0 formula candidate)) :
    CanonicalBoolListLE (recoveredPrefix count formula) candidate := by
  exact prefixSATChoices_lexLeast count 0 formula hwell
    (by simpa using hrange) candidate hlength hcandidate

end NearCubicWires.CanonicalSATSelfReduction
