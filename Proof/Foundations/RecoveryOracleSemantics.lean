import Proof.Foundations.NestedBalancedCNFSATEncoding
import Proof.Foundations.SourceCore

/-! Production statement vocabulary for the corrected recovery oracle.
These are the banked bounded-validation semantics and proofs, lifted without
changing their algorithms or resource claims. In particular the finite verifier
never expands the binary prefix count. Its ordinary encoded-length realization
and the register-to-ordinary simulator are separate LOCAL obligations.
-/
namespace NearCubicWires.RepairSource.RecoveryOracle
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open TseitinCNF BalancedCNFSATEncoding NestedBalancedCNFSATEncoding

structure CompactRequest where
  base : EncodedCNF
  committed : Nat
  count : Nat

def CompactRequest.variables (request : CompactRequest) : List Nat :=
  (request.base.flatten.map Prod.snd).eraseDups

def CompactRequest.assignment (request : CompactRequest) (witness : List Bool)
    (index : Nat) : Bool :=
  if index < request.count then request.committed.testBit index
  else witness.getD (request.variables.idxOf index) false

/-- Scans only explicit base clauses and a finite assignment witness. -/
def compactVerifier (request : CompactRequest) (witness : List Bool) : Bool :=
  witness.length = request.variables.length &&
    request.base.all (fun clause => clause.length = 3) &&
    formulaEval (request.assignment witness) request.base

def compactMeaning (request : CompactRequest) : Prop :=
  request.base.all (fun clause => clause.length = 3) = true ∧
    ∃ assignment : Nat → Bool,
      (∀ index < request.count, assignment index = request.committed.testBit index) ∧
      formulaEval assignment request.base = true

theorem assignment_on_base (request : CompactRequest) (assignment : Nat → Bool)
    (hp : ∀ index < request.count, assignment index = request.committed.testBit index)
    {clause : List (Bool × Nat)} (hc : clause ∈ request.base)
    {literal : Bool × Nat} (hl : literal ∈ clause) :
    request.assignment (request.variables.map assignment) literal.2 = assignment literal.2 := by
  have hv : literal.2 ∈ request.variables := by
    simp only [CompactRequest.variables, List.mem_eraseDups, List.mem_map]
    exact ⟨literal, List.mem_flatten.mpr ⟨clause, hc, hl⟩, rfl⟩
  by_cases hindex : literal.2 < request.count
  · simp [CompactRequest.assignment, hindex, hp _ hindex]
  · simp [CompactRequest.assignment, hindex, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_idxOf hv]

theorem compactVerifier_iff (request : CompactRequest) :
    (∃ witness : List Bool, compactVerifier request witness = true) ↔ compactMeaning request := by
  constructor
  · rintro ⟨witness, h⟩
    simp only [compactVerifier, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.2, request.assignment witness,
      (by intro index hi; simp [CompactRequest.assignment, hi]), h.2⟩
  · rintro ⟨hthree, assignment, hp, heval⟩
    refine ⟨request.variables.map assignment, ?_⟩
    simp only [compactVerifier, List.length_map, decide_true, Bool.true_and, hthree]
    have hcongr : formulaEval (request.assignment (request.variables.map assignment)) request.base =
        formulaEval assignment request.base := by
      unfold formulaEval clauseEval
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.any_eq_true]
      apply forall_congr'
      intro clause
      apply imp_congr_right
      intro hc
      apply exists_congr
      intro literal
      apply and_congr_right
      intro hl
      simp [literalEval, assignment_on_base request assignment hp hc hl]
    exact hcongr.trans heval

theorem prefix_eval_iff (request : CompactRequest) (assignment : Nat → Bool) :
    formulaEval assignment
      (balancedPrefixClauses request.count request.committed ++ request.base) = true ↔
      (∀ index < request.count, assignment index = request.committed.testBit index) ∧
        formulaEval assignment request.base = true := by
  simp only [formulaEval, List.all_append, Bool.and_eq_true, balancedPrefixClauses,
    List.all_map, List.all_reverse, List.all_eq_true, List.mem_range]
  apply and_congr
  · apply forall_congr'
    intro index
    apply imp_congr_right
    intro _
    cases hcommitted : request.committed.testBit index <;>
      cases hvalue : assignment index <;>
      simp [balancedPrefixUnitClause, clauseEval, literalEval, hcommitted, hvalue]
  · rfl

theorem prefix_three (request : CompactRequest) :
    (balancedPrefixClauses request.count request.committed ++ request.base).all
      (fun clause => clause.length = 3) =
    request.base.all (fun clause => clause.length = 3) := by
  simp [balancedPrefixClauses, balancedPrefixUnitClause]

theorem compactVerifier_expanded_iff (request : CompactRequest) :
    (∃ witness : List Bool, compactVerifier request witness = true) ↔
      (balancedPrefixClauses request.count request.committed ++ request.base).all
        (fun clause => clause.length = 3) = true ∧
      ∃ assignment : Nat → Bool,
        formulaEval assignment
          (balancedPrefixClauses request.count request.committed ++ request.base) = true := by
  rw [compactVerifier_iff, prefix_three]
  simp only [compactMeaning, prefix_eval_iff]




end NearCubicWires.RepairSource.RecoveryOracle
