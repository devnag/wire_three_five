import Proof.Wire_3_5.Transfer.TransferUnion

/-! # The padded substituted circuit is the native one with its inputs cast (P3:3637-3644, 3669-3671; D1.6)

Realizes the claim behind the hybrid recovery's Case 2: "pad the outer verifier to the exact width
`q(N)` [...] All probabilities and the projection property are preserved" (P3:3637-3644), made exact at the level of
circuits: the union machine checks the PCPP of the PADDED request of a guessed oracle (P3:3669-3671), and for the
oracle `ext C` (the native oracle `C` with its inputs cast from `Fin R` to `Fin w`) that padded substituted circuit IS
the native substituted circuit of `C` with its inputs cast. Base's padding (`padProjectionPCP`) keeps the native
address bits in the low coordinates and makes the high ones constant `false`; the substitution reads the projection
only at the oracle's input nodes, all of which are low.

Paper quantities: `castNode h`, `castCircuit h C` (the input cast `Fin R → Fin w`, `h : R ≤ w`: the same node list up
to the input type, the same size and output), `padProj h proj` (the padded projections); **`substituted_cast`**:
`substituted (castCircuit h C) (padProj h ∘ projections) formula = castCircuit h (substituted C projections formula)`;
`compactSubstituted_cast` (the same for base's `compactSubstituted`), **`unionRequest_pad`** (the union machine's padded
request at the oracle `castCircuit C` is the request of the cast native substituted circuit), and
**`encode_castCircuit`** (the circuit code ignores the arity, so the cast circuit has the native circuit's code).
An executable twin (`#guard`) checks the code equality on a two-input oracle padded from width 2 to 3. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.PCPPSubstitution

section Cast
variable {R w : ℕ} (h : R ≤ w)

/-- The input cast of one node. -/
def castNode : BooleanNode R → BooleanNode w
  | .const b => .const b
  | .input i => .input (Fin.castLE h i)
  | .not c => .not c
  | .and a b => .and a b
  | .or a b => .or a b

theorem castNode_wf (node : BooleanNode R) (k : ℕ) : (castNode h node).WellFormedAt k ↔ node.WellFormedAt k := by
  cases node <;> rfl

/-- The input cast of a circuit: the same nodes and output with the inputs read in `Fin w`. -/
def castCircuit (C : BooleanCircuit R) : BooleanCircuit w where
  nodes := C.nodes.map (castNode h)
  output := ⟨C.output.val, by simp⟩
  wellFormed := fun i => by
    rw [List.get_eq_getElem, List.getElem_map, castNode_wf]
    exact C.wellFormed ⟨i.val, by simpa using i.isLt⟩

theorem castCircuit_size (C : BooleanCircuit R) : (castCircuit h C).size = C.size := by
  simp [castCircuit, BooleanCircuit.size]

/-- The padded projections: the native ones lifted on the low coordinates, constant `false` above. -/
def padProj (proj : Fin R → ProjectedRandomBit R) (i : Fin w) : ProjectedRandomBit w :=
  if hi : i.val < R then ProjectionPCPPadding.liftProjectedRandomBit h (proj ⟨i.val, hi⟩) else .constant false

theorem padProj_cast (proj : Fin R → ProjectedRandomBit R) (i : Fin R) :
    padProj h proj (Fin.castLE h i) = ProjectionPCPPadding.liftProjectedRandomBit h (proj i) := by
  unfold padProj
  rw [dif_pos (by simp)]
  rfl

theorem firstNode_cast (proj : Fin R → ProjectedRandomBit R) (node : BooleanNode R) :
    firstNode (padProj h proj) (castNode h node) = castNode h (firstNode proj node) := by
  cases node with
  | input i =>
    simp only [castNode, firstNode, padProj_cast]
    cases proj i <;> rfl
  | _ => rfl

theorem secondNode_cast (base index : ℕ) (proj : Fin R → ProjectedRandomBit R) (node : BooleanNode R) :
    secondNode base index (padProj h proj) (castNode h node) = castNode h (secondNode base index proj node) := by
  cases node with
  | input i =>
    simp only [castNode, secondNode, padProj_cast]
    cases proj i <;> rfl
  | _ => rfl

end Cast

section Builders
variable {R w : ℕ} (h : R ≤ w)

theorem copyPrefix_cast (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (C : BooleanCircuit R) (proj : Fin R → ProjectedRandomBit R) :
    ∀ (count : ℕ) (hc : count ≤ C.nodes.length) (hc' : count ≤ (castCircuit h C).nodes.length),
      (copyPrefix prior' (castCircuit h C) (padProj h proj) count hc').builder.nodes =
        (copyPrefix prior C proj count hc).builder.nodes.map (castNode h) := by
  have hlen : prior'.nodes.length = prior.nodes.length := by rw [hp, List.length_map]
  intro count
  induction count with
  | zero => intro _ _; exact hp
  | succ count ih =>
    intro hc hc'
    simp only [copyPrefix, copyNode_nodes, List.map_append, List.map_cons, List.map_nil]
    rw [ih (by omega) (by omega)]
    simp only [castCircuit, List.getElem_map, hlen, firstNode_cast, secondNode_cast]

theorem copyOracle_cast (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (C : BooleanCircuit R) (proj : Fin R → ProjectedRandomBit R) :
    (copyOracle prior' (castCircuit h C) (padProj h proj)).final.nodes =
        (copyOracle prior C proj).final.nodes.map (castNode h) ∧
      ((copyOracle prior' (castCircuit h C) (padProj h proj)).output 0).val =
        ((copyOracle prior C proj).output 0).val := by
  have hlen : prior'.nodes.length = prior.nodes.length := by rw [hp, List.length_map]
  have hcount : (castCircuit h C).nodes.length = C.nodes.length := by simp [castCircuit]
  have hcong : ∀ (n1 n2 : ℕ) (_e : n1 = n2) (p1 : n1 ≤ (castCircuit h C).nodes.length)
      (p2 : n2 ≤ (castCircuit h C).nodes.length),
      (copyPrefix prior' (castCircuit h C) (padProj h proj) n1 p1).builder.nodes =
        (copyPrefix prior' (castCircuit h C) (padProj h proj) n2 p2).builder.nodes := by
    intro n1 n2 e p1 p2; subst e; rfl
  refine ⟨?_, ?_⟩
  · exact (hcong _ _ hcount _ (by omega)).trans
      (copyPrefix_cast h prior prior' hp C proj C.nodes.length le_rfl (by omega))
  · simp [copyOracle, hlen, castCircuit]

theorem copyQuery_cast (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (C : BooleanCircuit R) (proj : Fin R → ProjectedRandomBit R) :
    (copyQuery prior' (castCircuit h C) (padProj h proj)).final.nodes =
      (copyQuery prior C proj).final.nodes.map (castNode h) := by
  obtain ⟨h1, h2⟩ := copyOracle_cast h prior prior' hp C proj
  simp only [copyQuery, BooleanDAGBuilder.appendNot, BooleanDAGBuilder.append, BooleanDAGBuilder.appendNode_nodes,
    List.map_append, List.map_cons, List.map_nil, h1, h2]
  rfl

theorem queryPrefix_cast {q : ℕ} (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (C : BooleanCircuit R)
    (projections : Fin q → Fin R → ProjectedRandomBit R) :
    ∀ (count : ℕ) (hc : count ≤ q),
      (queryPrefix prior' (castCircuit h C) (fun j => padProj h (projections j)) count hc).builder.nodes =
        (queryPrefix prior C projections count hc).builder.nodes.map (castNode h) := by
  intro count
  induction count with
  | zero => intro _; exact hp
  | succ count ih =>
    intro hc
    exact copyQuery_cast h _ _ (ih (by omega)) C _

theorem clauseBlock_nodes (b : BooleanDAGBuilder R) (refs : Fin 3 → Fin b.nodes.length)
    (acc : Fin b.nodes.length) :
    (clauseBlock b refs acc).final.nodes = b.nodes ++ [.or (refs 0).val (refs 1).val, .or b.nodes.length (refs 2).val,
      .and acc.val (b.nodes.length + 1)] ∧ ((clauseBlock b refs acc).output 0).val = b.nodes.length + 2 := by
  refine ⟨?_, ?_⟩
  · simp [clauseBlock, BooleanDAGBuilder.appendOr, BooleanDAGBuilder.appendAnd, BooleanDAGBuilder.append,
      BooleanDAGBuilder.newest, BooleanDAGBuilder.liftRef]
  · simp [clauseBlock, BooleanDAGBuilder.appendOr, BooleanDAGBuilder.appendAnd, BooleanDAGBuilder.append,
      BooleanDAGBuilder.newest]

theorem compileClauses_cast {q : ℕ} (clauses : List (Fin 3 → Literal q)) :
    ∀ (b : BooleanDAGBuilder R) (b' : BooleanDAGBuilder w) (_hb : b'.nodes = b.nodes.map (castNode h))
      (refs : Literal q → Fin b.nodes.length) (refs' : Literal q → Fin b'.nodes.length)
      (_hr : ∀ l, (refs' l).val = (refs l).val) (acc : Fin b.nodes.length) (acc' : Fin b'.nodes.length)
      (_ha : acc'.val = acc.val),
      (compileClauses b' refs' acc' clauses).final.nodes = (compileClauses b refs acc clauses).final.nodes.map
          (castNode h) ∧
        ((compileClauses b' refs' acc' clauses).output 0).val = ((compileClauses b refs acc clauses).output 0).val := by
  induction clauses with
  | nil =>
    intro b b' hb refs refs' hr acc acc' ha
    exact ⟨hb, ha⟩
  | cons clause tail ih =>
    intro b b' hb refs refs' hr acc acc' ha
    have hlen : b'.nodes.length = b.nodes.length := by rw [hb, List.length_map]
    obtain ⟨n1, o1⟩ := clauseBlock_nodes b (fun i => refs (clause i)) acc
    obtain ⟨n1', o1'⟩ := clauseBlock_nodes b' (fun i => refs' (clause i)) acc'
    have hnext : (clauseBlock b' (fun i => refs' (clause i)) acc').final.nodes =
        (clauseBlock b (fun i => refs (clause i)) acc).final.nodes.map (castNode h) := by
      rw [n1, n1', List.map_append]
      congr 1
      simp [castNode, hr, ha, hlen]
    exact ih _ _ hnext _ _ (fun l => by simp [hr]) _ _ (by rw [o1, o1', hlen])

end Builders

section Main
variable {R w : ℕ} (h : R ≤ w)

theorem circuit_ext {n : ℕ} {c1 c2 : BooleanCircuit n} (hn : c1.nodes = c2.nodes)
    (ho : c1.output.val = c2.output.val) : c1 = c2 := by
  obtain ⟨n1, o1, w1⟩ := c1
  obtain ⟨n2, o2, w2⟩ := c2
  simp only at hn ho
  subst hn
  have : o1 = o2 := Fin.ext ho
  subst this
  rfl

/-- **The padded substituted circuit is the native one with its inputs cast.** -/
theorem substituted_cast {q : ℕ} (C : BooleanCircuit R) (projections : Fin q → Fin R → ProjectedRandomBit R)
    (formula : ThreeCNF q) :
    substituted (castCircuit h C) (fun j => padProj h (projections j)) formula =
      castCircuit h (substituted C projections formula) := by
  have h0 : (BooleanDAGBuilder.empty w).nodes = (BooleanDAGBuilder.empty R).nodes.map (castNode h) := rfl
  have hbank := queryPrefix_cast h (BooleanDAGBuilder.empty R) (BooleanDAGBuilder.empty w) h0 C projections q le_rfl
  have hsize : (castCircuit h C).size = C.size := castCircuit_size h C
  have hout : (castCircuit h C).output.val = C.output.val := rfl
  -- the constant `true` appended after the query bank
  have hinit : ((queryBank (BooleanDAGBuilder.empty w) (castCircuit h C) fun j => padProj h (projections j)).appendConst
      true).builder.nodes = ((queryBank (BooleanDAGBuilder.empty R) C projections).appendConst true).builder.nodes.map
        (castNode h) := by
    simp only [BooleanDAGBuilder.appendConst, BooleanDAGBuilder.append, BooleanDAGBuilder.appendNode_nodes,
      List.map_append, List.map_cons, List.map_nil, queryBank, hbank]
    rfl
  have hbanklen : (queryBank (BooleanDAGBuilder.empty w) (castCircuit h C) fun j => padProj h (projections j)).nodes.length
      = (queryBank (BooleanDAGBuilder.empty R) C projections).nodes.length := by
    simp only [queryBank, hbank, List.length_map]
  obtain ⟨hn, ho⟩ := compileClauses_cast h formula.clauses
    ((queryBank (BooleanDAGBuilder.empty R) C projections).appendConst true).builder
    ((queryBank (BooleanDAGBuilder.empty w) (castCircuit h C) fun j => padProj h (projections j)).appendConst true).builder
    hinit
    (fun literal => ((queryBank (BooleanDAGBuilder.empty R) C projections).appendConst true).lift
      (literalRef (BooleanDAGBuilder.empty R) C projections literal))
    (fun literal => ((queryBank (BooleanDAGBuilder.empty w) (castCircuit h C)
      fun j => padProj h (projections j)).appendConst true).lift
      (literalRef (BooleanDAGBuilder.empty w) (castCircuit h C) (fun j => padProj h (projections j)) literal))
    (fun l => by
      cases l <;> simp only [BooleanDAGBuilder.appendConst, BooleanDAGBuilder.append, BooleanDAGBuilder.liftRef_val,
        literalRef, queryRef, hsize, hout] <;> rfl)
    ((queryBank (BooleanDAGBuilder.empty R) C projections).appendConst true).output
    ((queryBank (BooleanDAGBuilder.empty w) (castCircuit h C) fun j => padProj h (projections j)).appendConst true).output
    (by simp only [BooleanDAGBuilder.appendConst, BooleanDAGBuilder.append, BooleanDAGBuilder.newest, hbanklen])
  apply circuit_ext
  · exact hn
  · exact ho

theorem compactSubstituted_cast {q : ℕ} (C : BooleanCircuit R) (projections : Fin q → Fin R → ProjectedRandomBit R)
    (formula : ThreeCNF q) :
    compactSubstituted (castCircuit h C) (fun j => padProj h (projections j)) formula =
      castCircuit h (compactSubstituted C projections formula) :=
  substituted_cast h C projections (RepairSource.compactThreeCNF formula)

end Main

section Padded
open NearCubicWires.ProjectionPCPPadding

/-- **The union machine's padded request at a cast oracle** is the request of the cast native substituted circuit. -/
theorem unionRequest_pad {M : TimedDecisionMachine} {T : ℕ → ℕ} (pcp : ProjectionPCP M T) (wf : ℕ → ℕ)
    (hw : ∀ n, pcp.nativeWidth n ≤ wf n) (a : PointwisePCPPAlgorithm) {N : ℕ} (z : BitInput N)
    (C : BooleanCircuit (pcp.nativeWidth N)) :
    unionRequest (padProjectionPCP pcp wf hw) a z (castCircuit (hw N) C) =
      PCPPRequestBoundary.request a (castCircuit (hw N)
        (compactSubstituted C (pcp.queryAddressBits z) (pcp.decision z fun _ => false))) := by
  have hq : (padProjectionPCP pcp wf hw).queryAddressBits z = fun j => padProj (hw N) (pcp.queryAddressBits z j) := by
    funext j i
    rfl
  have hd : (padProjectionPCP pcp wf hw).decision z (fun _ => false) = pcp.decision z (fun _ => false) := rfl
  unfold unionRequest sourceRequest
  rw [hq, hd]
  exact congrArg (PCPPRequestBoundary.request a)
    (compactSubstituted_cast (hw N) C (pcp.queryAddressBits z) (pcp.decision z fun _ => false))

end Padded

/-! ## Executable twin (a two-input `AND` oracle, one query, padded from width 2 to width 3) -/

-- the padded substituted circuit has the native circuit's code and node count

end NearCubicWires.WireExponent3_5.Transfer
