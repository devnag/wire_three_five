import Proof.Foundations.BooleanCircuitSizePadding
import Proof.Foundations.CaseOnePadding
import Proof.Foundations.PhysicalRecovery
import Proof.Foundations.ProjectionPCPPadding
import Proof.Foundations.RefuterClockClosure

/-!
# Outer-PCP Case-1/Case-2 extraction

This module performs the semantic split that occurs only after the fixed weak
machine has forced a hierarchy YES word.  It uses the genuine projection PCP:
absence of a small accepting oracle circuit yields a worst-case-hard proof
function for the STV branch, while an accepting circuit is passed to the
pointwise PCPP and gives one canonical honest occurrence table.
-/

namespace NearCubicWires.OuterPCPRecovery

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.RecoveryPipeline
open NearCubicWires.SourceInterfaces
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.RefuterClockClosure
open NearCubicWires.CaseOnePadding
open NearCubicWires.CircuitRestriction
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.PhysicalRecovery

/-- The native random string presented to one projected oracle query. -/
def projectedInput
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (query : Fin (pcp.queryCount n)) :
    BitInput (pcp.nativeWidth n) :=
  fun bit => (pcp.queryAddressBits input query bit).eval randomness

/-- Evaluate the outer verifier after substituting one Boolean oracle
circuit.  The circuit is shared across every query and random row. -/
def acceptsOracleCircuit
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (randomness : BitInput (pcp.nativeWidth n)) : Bool :=
  (pcp.decision input randomness).eval fun query =>
    circuit.eval (projectedInput pcp input randomness query)

/-- Regard a native PCP proof table as its address-bit Boolean function. -/
def proofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (proof : BitInput (2 ^ pcp.nativeWidth n)) :
    BoolFunction (pcp.nativeWidth n) :=
  fun address => proof (binaryAddress address)

/-- The canonical truth-table ABI enumerates a PCP proof in its native
numeric address order.  This is the variable order used by C.12's zero-first
self-reduction. -/
@[simp] theorem boolFunctionTable_proofFunction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (proof : BitInput (2 ^ pcp.nativeWidth n)) :
    boolFunctionTable (proofFunction pcp proof) = List.ofFn proof := by
  apply List.ext_getElem
  · simp [boolFunctionTable]
  · intro index hleft _hright
    have hindex : index < 2 ^ pcp.nativeWidth n := by
      simpa [boolFunctionTable] using hleft
    simp only [boolFunctionTable, List.getElem_map, List.getElem_range,
      proofFunction, List.getElem_ofFn]
    rw [binaryAddress_testBit hindex]

/- The bounded syntax below is both the finite source for canonical selection
and the typed description decoded by C.12.  Child indices carry their
topological bound in their type, so an invalid DAG never enters the candidate
set. -/
inductive BoundedBooleanNode (n bound : ℕ) where
  | const (value : Bool)
  | input (index : Fin n)
  | not (child : Fin bound)
  | and (left right : Fin bound)
  | or (left right : Fin bound)
  deriving Fintype

def BoundedBooleanNode.toNode {n bound : ℕ} :
    BoundedBooleanNode n bound → BooleanNode n
  | .const value => .const value
  | .input index => .input index
  | .not child => .not child.val
  | .and left right => .and left.val right.val
  | .or left right => .or left.val right.val

@[simp] theorem BoundedBooleanNode.toNode_wellFormed
    {n bound : ℕ} (node : BoundedBooleanNode n bound) :
    node.toNode.WellFormedAt bound := by
  cases node <;> simp [BoundedBooleanNode.toNode,
    BooleanNode.WellFormedAt]

def boundedBooleanNodeOfWellFormed {n index : ℕ}
    (node : BooleanNode n) (hwell : node.WellFormedAt index) :
    BoundedBooleanNode n index :=
  match node with
  | .const value => .const value
  | .input inputIndex => .input inputIndex
  | .not child => .not ⟨child, hwell⟩
  | .and left right => .and ⟨left, hwell.1⟩ ⟨right, hwell.2⟩
  | .or left right => .or ⟨left, hwell.1⟩ ⟨right, hwell.2⟩

@[simp] theorem boundedBooleanNode_toNode_ofWellFormed
    {n index : ℕ} (node : BooleanNode n)
    (hwell : node.WellFormedAt index) :
    (boundedBooleanNodeOfWellFormed node hwell).toNode = node := by
  cases node <;> rfl

structure BoundedCircuitKeySource (n bound : ℕ) where
  nodeCount : Fin (bound + 1)
  nodes :
    (index : Fin nodeCount.val) → BoundedBooleanNode n index.val
  output : Fin nodeCount.val
  deriving Fintype

def BoundedCircuitKeySource.toCircuit {n bound : ℕ}
    (source : BoundedCircuitKeySource n bound) : BooleanCircuit n where
  nodes :=
    List.ofFn fun index =>
      (source.nodes index).toNode
  output :=
    ⟨source.output.val, by
      simpa only [List.length_ofFn] using source.output.isLt⟩
  wellFormed := by
    intro index
    rw [List.get_ofFn]
    convert
      BoundedBooleanNode.toNode_wellFormed
        (source.nodes
          (Fin.cast (by simp only [List.length_ofFn]) index)) using 1
    exact
      (Fin.val_cast (by simp only [List.length_ofFn]) index).symm

@[simp] theorem BoundedCircuitKeySource.toCircuit_size_le
    {n bound : ℕ} (source : BoundedCircuitKeySource n bound) :
    source.toCircuit.size ≤ bound := by
  simpa [BoundedCircuitKeySource.toCircuit, BooleanCircuit.size] using
    Nat.le_of_lt_succ source.nodeCount.isLt

def boundedCircuitKeySourceOfCircuit {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    BoundedCircuitKeySource n bound where
  nodeCount := ⟨circuit.nodes.length, by
    simpa [BooleanCircuit.size] using Nat.lt_succ_of_le hsize⟩
  nodes := fun index =>
    boundedBooleanNodeOfWellFormed (circuit.nodes.get index)
      (circuit.wellFormed index)
  output := circuit.output

private theorem booleanCircuit_ext {n : ℕ}
    (left right : BooleanCircuit n)
    (hnodes : left.nodes = right.nodes)
    (houtput : left.output.val = right.output.val) :
    left = right := by
  cases left with
  | mk leftNodes leftOutput leftWellFormed =>
      cases right with
      | mk rightNodes rightOutput rightWellFormed =>
          simp only at hnodes houtput
          subst rightNodes
          have hfin : leftOutput = rightOutput :=
            Fin.ext houtput
          subst rightOutput
          rfl

@[simp] theorem boundedCircuitKeySource_toCircuit_ofCircuit
    {n bound : ℕ} (circuit : BooleanCircuit n)
    (hsize : circuit.size ≤ bound) :
    (boundedCircuitKeySourceOfCircuit circuit hsize).toCircuit =
      circuit := by
  cases circuit with
  | mk nodes output wellFormed =>
      let constructed :=
        (boundedCircuitKeySourceOfCircuit
          { nodes := nodes
            output := output
            wellFormed := wellFormed } hsize).toCircuit
      have hnodes : constructed.nodes = nodes := by
        apply List.ext_getElem
        · simp [constructed, BoundedCircuitKeySource.toCircuit,
            boundedCircuitKeySourceOfCircuit]
        · intro index _hleft _hright
          simp [constructed, BoundedCircuitKeySource.toCircuit,
            boundedCircuitKeySourceOfCircuit]
      apply booleanCircuit_ext constructed
        { nodes := nodes
          output := output
          wellFormed := wellFormed } hnodes
      rfl

/-! ### Fixed structural description block -/

/-- False-first unary rank bits.  For values at most `limit`, ordinary list
lexicographic order is exactly numeric order, with no container-code order
leaking into C.12's SAT variables. -/
def orderedNatBits (limit value : ℕ) : List Bool :=
  (List.range limit).map fun index => decide (index < value)

@[simp] theorem orderedNatBits_length (limit value : ℕ) :
    (orderedNatBits limit value).length = limit := by
  simp [orderedNatBits]

def boundedCircuitFieldLimit (n bound : ℕ) : ℕ :=
  n + bound + 1

def boundedNodeDescriptionBits {n : ℕ} (bound : ℕ) :
    BooleanNode n → List Bool
  | .const value =>
      orderedNatBits 6 0 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) value.toNat ++
        orderedNatBits (boundedCircuitFieldLimit n bound) 0
  | .input index =>
      orderedNatBits 6 1 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) index.val ++
        orderedNatBits (boundedCircuitFieldLimit n bound) 0
  | .not child =>
      orderedNatBits 6 2 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) child ++
        orderedNatBits (boundedCircuitFieldLimit n bound) 0
  | .and left right =>
      orderedNatBits 6 3 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) left ++
        orderedNatBits (boundedCircuitFieldLimit n bound) right
  | .or left right =>
      orderedNatBits 6 4 ++
        orderedNatBits (boundedCircuitFieldLimit n bound) left ++
        orderedNatBits (boundedCircuitFieldLimit n bound) right

def boundedOutputDescriptionBits
    (n bound output : ℕ) : List Bool :=
  orderedNatBits 6 5 ++
    orderedNatBits (boundedCircuitFieldLimit n bound) output ++
    orderedNatBits (boundedCircuitFieldLimit n bound) 0

def boundedPaddingDescriptionBits
    (n bound : ℕ) : List Bool :=
  orderedNatBits 6 6 ++
    orderedNatBits (boundedCircuitFieldLimit n bound) 0 ++
    orderedNatBits (boundedCircuitFieldLimit n bound) 0

def boundedCircuitDescriptionWidth (n bound : ℕ) : ℕ :=
  (bound + 1) * (6 + 2 * boundedCircuitFieldLimit n bound)

/-- Direct decoder-order description: typed node rows, one output sentinel,
then padding sentinels.  A longer valid DAG compares before a shorter one at
the first node/output boundary, exactly as its structural field list does. -/
def canonicalBoundedCircuitDescription {n : ℕ}
    (bound : ℕ) (circuit : BooleanCircuit n) : List Bool :=
  ((circuit.nodes.map (boundedNodeDescriptionBits bound)) ++
      [boundedOutputDescriptionBits n bound circuit.output.val] ++
      List.replicate (bound - circuit.size)
        (boundedPaddingDescriptionBits n bound)).flatten

@[simp] theorem boundedNodeDescriptionBits_length {n bound : ℕ}
    (node : BooleanNode n) :
    (boundedNodeDescriptionBits bound node).length =
      6 + 2 * boundedCircuitFieldLimit n bound := by
  cases node <;> simp [boundedNodeDescriptionBits] <;> omega

@[simp] theorem boundedOutputDescriptionBits_length (n bound output : ℕ) :
    (boundedOutputDescriptionBits n bound output).length =
      6 + 2 * boundedCircuitFieldLimit n bound := by
  simp [boundedOutputDescriptionBits]
  omega

@[simp] theorem boundedPaddingDescriptionBits_length (n bound : ℕ) :
    (boundedPaddingDescriptionBits n bound).length =
      6 + 2 * boundedCircuitFieldLimit n bound := by
  simp [boundedPaddingDescriptionBits]
  omega

@[simp] theorem sum_nodeDescriptionLengths {n bound : ℕ}
    (nodes : List (BooleanNode n)) :
    (nodes.map
      (List.length ∘ boundedNodeDescriptionBits bound)).sum =
        nodes.length *
          (6 + 2 * boundedCircuitFieldLimit n bound) := by
  induction nodes with
  | nil =>
      simp
  | cons node rest ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply,
        boundedNodeDescriptionBits_length, List.length_cons, ih]
      ring

theorem canonicalBoundedCircuitDescription_length {n bound : ℕ}
    (circuit : BooleanCircuit n) (hsize : circuit.size ≤ bound) :
    (canonicalBoundedCircuitDescription bound circuit).length =
      boundedCircuitDescriptionWidth n bound := by
  have hlength : circuit.nodes.length ≤ bound := by
    simpa only [BooleanCircuit.size] using hsize
  simp only [canonicalBoundedCircuitDescription, List.length_flatten,
    List.map_append, List.sum_append, List.map_map,
    sum_nodeDescriptionLengths, List.map_singleton, List.sum_singleton,
    boundedOutputDescriptionBits_length, List.map_replicate,
    List.sum_replicate, nsmul_eq_mul,
    boundedPaddingDescriptionBits_length,
    boundedCircuitDescriptionWidth, BooleanCircuit.size]
  have hpartition :
      circuit.nodes.length + (bound - circuit.nodes.length) = bound :=
    Nat.add_sub_of_le hlength
  calc
    circuit.nodes.length *
          (6 + 2 * boundedCircuitFieldLimit n bound) +
        (6 + 2 * boundedCircuitFieldLimit n bound) +
        (bound - circuit.nodes.length) *
          (6 + 2 * boundedCircuitFieldLimit n bound) =
        (circuit.nodes.length + (bound - circuit.nodes.length) + 1) *
          (6 + 2 * boundedCircuitFieldLimit n bound) := by ring
    _ = (bound + 1) *
          (6 + 2 * boundedCircuitFieldLimit n bound) := by
      rw [hpartition]

theorem acceptsOracleCircuit_of_proof
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (proof : BitInput (2 ^ pcp.nativeWidth n))
    (hproof : ∀ randomness, pcp.accepts input proof randomness)
    (circuit : BooleanCircuit (pcp.nativeWidth n))
    (hcircuit : circuit.eval = proofFunction pcp proof) :
    ∀ randomness, acceptsOracleCircuit pcp input circuit randomness := by
  intro randomness
  unfold acceptsOracleCircuit
  rw [hcircuit]
  unfold proofFunction
  rw [show
    (fun query =>
      proof (binaryAddress (projectedInput pcp input randomness query))) =
    (fun query =>
      proof (binaryAddress fun bit =>
        (pcp.queryAddressBits input query bit).eval randomness)) by
      rfl]
  exact hproof randomness

/-- The zero-first truth table among perfectly accepting outer proofs.  The
order is the native `Fin` address order proved by
`boolFunctionTable_proofFunction`, exactly matching C.12's prefix variables. -/
structure CanonicalAcceptingProof
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) where
  proof : BitInput (2 ^ pcp.nativeWidth n)
  accepts : ∀ randomness, pcp.accepts input proof randomness
  minimal : ∀ candidate,
    (∀ randomness, pcp.accepts input candidate randomness) →
      CanonicalBoolListLE (List.ofFn proof) (List.ofFn candidate)

theorem existsCanonicalAcceptingProof
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (complete :
      ∃ proof, ∀ randomness, pcp.accepts input proof randomness) :
    Nonempty (CanonicalAcceptingProof pcp input) := by
  classical
  letI : LinearOrder (BitInput (2 ^ pcp.nativeWidth n)) :=
    LinearOrder.lift' List.ofFn List.ofFn_injective
  let eligible : Finset (BitInput (2 ^ pcp.nativeWidth n)) :=
    Finset.univ.filter fun proof =>
      ∀ randomness, pcp.accepts input proof randomness
  have heligible : eligible.Nonempty := by
    rcases complete with ⟨proof, haccepts⟩
    exact ⟨proof, by simp [eligible, haccepts]⟩
  let proof := eligible.min' heligible
  have haccepts : ∀ randomness, pcp.accepts input proof randomness := by
    have hmember := eligible.min'_mem heligible
    simpa only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] using
      hmember
  refine
    ⟨{ proof := proof
       accepts := haccepts
       minimal := ?_ }⟩
  intro candidate hcandidate
  exact eligible.min'_le candidate (by simp [eligible, hcandidate])

/-! ## Canonical representatives for executable recovery -/

/-- The zero-first typed description among small oracle circuits accepting
every outer row.  The fixed row block is the exact C.12 SAT-variable order;
numeric container encodings play no role in selection. -/
structure CanonicalAcceptingOracle
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) where
  circuit : BooleanCircuit (pcp.nativeWidth n)
  sizeBounded : circuit.size ≤ sizeBound (pcp.nativeWidth n)
  accepts : ∀ randomness,
    acceptsOracleCircuit pcp input circuit randomness
  minimal : ∀ candidate : BooleanCircuit (pcp.nativeWidth n),
    candidate.size ≤ sizeBound (pcp.nativeWidth n) →
      (∀ randomness,
        acceptsOracleCircuit pcp input candidate randomness) →
      canonicalBoundedCircuitDescription
          (sizeBound (pcp.nativeWidth n)) circuit ≤
        canonicalBoundedCircuitDescription
          (sizeBound (pcp.nativeWidth n)) candidate

theorem existsCanonicalAcceptingOracle
    {machine : TimedDecisionMachine} {timeBound sizeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n)
    (existsSmall :
      ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ sizeBound (pcp.nativeWidth n) ∧
          ∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness) :
    Nonempty
      (CanonicalAcceptingOracle (sizeBound := sizeBound) pcp input) := by
  classical
  let bound := sizeBound (pcp.nativeWidth n)
  let candidateDescriptions : Finset (List Bool) :=
    Finset.univ.image
      (fun source : BoundedCircuitKeySource (pcp.nativeWidth n) bound =>
        canonicalBoundedCircuitDescription bound source.toCircuit)
  have description_mem_candidates
      (circuit : BooleanCircuit (pcp.nativeWidth n))
      (hsize : circuit.size ≤ bound) :
      canonicalBoundedCircuitDescription bound circuit ∈
        candidateDescriptions := by
    apply Finset.mem_image.mpr
    refine
      ⟨boundedCircuitKeySourceOfCircuit circuit hsize,
        Finset.mem_univ _, ?_⟩
    rw [boundedCircuitKeySource_toCircuit_ofCircuit]
  let eligibleDescriptions : Finset (List Bool) :=
    candidateDescriptions.filter fun description =>
      ∃ circuit : BooleanCircuit (pcp.nativeWidth n),
        circuit.size ≤ bound ∧
          (∀ randomness,
            acceptsOracleCircuit pcp input circuit randomness) ∧
          canonicalBoundedCircuitDescription bound circuit =
            description
  have heligible : eligibleDescriptions.Nonempty := by
    rcases existsSmall with ⟨circuit, hsize, haccepts⟩
    refine
      ⟨canonicalBoundedCircuitDescription bound circuit, ?_⟩
    apply Finset.mem_filter.mpr
    exact
      ⟨description_mem_candidates circuit hsize,
        circuit, hsize, haccepts, rfl⟩
  let selectedDescription := eligibleDescriptions.min' heligible
  have hselected := eligibleDescriptions.min'_mem heligible
  have hselectedSpec := (Finset.mem_filter.mp hselected).2
  rcases hselectedSpec with
    ⟨circuit, hsize, haccepts, hdescription⟩
  refine
    ⟨{ circuit := circuit
       sizeBounded := hsize
       accepts := haccepts
       minimal := ?_ }⟩
  intro candidate hcandidateSize hcandidateAccepts
  rw [hdescription]
  apply eligibleDescriptions.min'_le
  apply Finset.mem_filter.mpr
  exact
    ⟨description_mem_candidates candidate hcandidateSize,
      candidate, hcandidateSize, hcandidateAccepts, rfl⟩

/-! ## Genuine hierarchy-PCP instantiation -/

/-- The outer PCP attached to the timed hierarchy machine returned by the
fixed-refuter source.  Its runner bounds and semantic guarantees are retained
for the weak-machine and resource ledgers. -/
structure HierarchyOuterPCP {bound : ℕ → ℕ}
    (source : ExecutableRefuterSource bound) where
  runnerDegree : ℕ
  queryExponent : ℕ
  substitutionExponent : ℕ
  pcp : ExecutableProjectionPCP source.hierarchyMachine bound
  proofExponent : ℕ
  substitution : ExecutableProjectionSubstitution pcp
  shapeDegree : pcp.shape.degree ≤ runnerDegree
  queryDegree : pcp.query.degree ≤ runnerDegree
  decisionDegree : pcp.decisionRunner.degree ≤ runnerDegree
  substitutionDegree : substitution.runner.degree ≤ runnerDegree
  queryCountBound : ∀ n, pcp.queryCount n ≤ pcp.shape.budget n
  compactQueryCountBound : ∀ n,
    pcp.queryCount n ≤
      pcp.shape.coefficient *
        (pcp.nativeWidth n + 1) ^ queryExponent
  decisionLengthBound : ∀ n input randomness,
    (pcp.decision (n := n) input randomness).clauses.length ≤
      pcp.decisionRunner.budget (pcp.decisionRequest input randomness)
  proofSizeBound : ∀ n,
    2 ^ pcp.nativeWidth n ≤
      pcp.shape.coefficient * bound n *
        logScale (bound n) ^ proofExponent
  substitutionSizeBound : ∀ request,
    (substitution.circuit request).size ≤
      substitution.sizeCoefficient *
        (pcp.nativeWidth request.inputArity +
          request.oracle.size + 1) ^ substitutionExponent
  complete : ∀ n input, source.hierarchyMachine.accepts n input →
    ∃ proof, ∀ randomness,
      pcp.toSemantic.accepts input proof randomness
  sound : ∀ n input, ¬source.hierarchyMachine.accepts n input →
    ∀ proof, pcp.toSemantic.acceptanceFraction input proof ≤
      1 / ((n + 1 : ℕ) : ℝ) ^ 10

/-! ## Canonical Case-2 honest table -/

/-- The first block of an occurrence-table input is the PCPP input. -/
def occurrenceInput {inputArity clauseBits : ℕ}
    (input : BitInput (inputArity + clauseBits + 1)) :
    BitInput inputArity :=
  fun index => input ⟨index.val, by omega⟩

/-- The second block is the power-of-two clause address. -/
def occurrenceClauseAddress {inputArity clauseBits : ℕ}
    (input : BitInput (inputArity + clauseBits + 1)) :
    BitInput clauseBits :=
  fun index => input ⟨inputArity + index.val, by omega⟩

/-- The final bit selects the left or right literal occurrence. -/
def occurrencePosition {inputArity clauseBits : ℕ}
    (input : BitInput (inputArity + clauseBits + 1)) : Bool :=
  input ⟨inputArity + clauseBits, by omega⟩

/-- Project a branch-independent occurrence address onto the native PCPP
layout.  Extra clause-address bits are ignored, while the position bit is
taken from the end of the padded layout rather than accidentally shifted into
the native clause-address block. -/
def projectPaddedOccurrenceInput
    {inputArity nativeClauseBits paddedClauseBits : ℕ}
    (hclause : nativeClauseBits ≤ paddedClauseBits)
    (input : BitInput (inputArity + paddedClauseBits + 1)) :
    BitInput (inputArity + nativeClauseBits + 1) :=
  fun index =>
    if hprefix : index.val < inputArity + nativeClauseBits then
      input ⟨index.val, by omega⟩
    else
      input ⟨inputArity + paddedClauseBits, by omega⟩

end NearCubicWires.OuterPCPRecovery
