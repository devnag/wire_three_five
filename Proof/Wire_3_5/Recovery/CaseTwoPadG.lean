import Proof.Wire_3_5.Assembly.Free
import Proof.Wire_3_5.Recovery.CaseTwoPad

/-! # The union machine's padded request at a general-width oracle (P3:3637-3644, 3669-3671)

Realizes, for the union machine's guessed oracle of the padded width `q = w(N) ≥ R(N)`, "pad the outer verifier to
the exact width `q(N)` [...] All probabilities and the projection property are preserved" (P3:3637-3644) together
with "the union machine [...] checks the PCPP of the substituted circuit of the guessed oracle" (P3:3669-3671): base's
padding (`padProjectionPCP`) keeps the native address bits in the low coordinates and makes the high ones constant
`false`, so the substitution reads a guessed oracle `O` of width `q` only through its low inputs. Exactly:
* **`restrictHigh R O`** (`h : R ≤ q`): `O` with every input `i ≥ R` replaced by the constant `false` (same node count,
  same output); **`substituted_restrict`**: `substituted O (padProj h ∘ projections) formula =
  castCircuit h (substituted (restrictHigh R O) projections formula)` (M15's `substituted_cast` is the case
  `O = castCircuit h C`, `restrictHigh R O = C`);
* **`padSubstituted`** (G1): the cast of base's NATIVE substituted circuit (`PCPPNativeHierarchyNodes.circuit`) at
  `restrictHigh O`;
* **`unionRequest_padG`** (G2): the union setup's padded request at any `O : BooleanCircuit (wf N)` is the request of
  `padSubstituted … O` (base's compaction idempotence and `normalized_hierarchy`, as in the Theorem 2.5 repository's
  `Selected.normalized_polynomial_run`);
* at the pinned setup `Split.setupF` (both `S₂` branches): **`setupF_width`** (the padded width is the ledger's
  `q(N) = nativeWidth kclk (gateApad l) N` past a cutoff) and **`setupF_request_rec`** / **`setupF_request_other`**
  (the setup's request is the request of `padSubstituted` at the branch's hierarchy).

Paper quantity of the main type (`unionRequest_padG`): the PCPP request of the padded outer verifier's substituted
circuit at a guessed width-`q` oracle. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.PCPPSubstitution
open NearCubicWires.RepairSource NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)

/-! ## Restricting an oracle to the low inputs -/

section Restrict

/-- One node restricted to the low inputs `i < R`: an input `i ≥ R` becomes the constant `false`. -/
def restrictNode (R : ℕ) {w : ℕ} : BooleanNode w → BooleanNode R
  | .const b => .const b
  | .input i => if hi : i.val < R then .input ⟨i.val, hi⟩ else .const false
  | .not c => .not c
  | .and a b => .and a b
  | .or a b => .or a b

theorem restrictNode_wf (R : ℕ) {w : ℕ} (node : BooleanNode w) (k : ℕ) (hn : node.WellFormedAt k) :
    (restrictNode R node).WellFormedAt k := by
  cases node with
  | input i =>
    simp only [restrictNode]
    split <;> trivial
  | _ => exact hn

/-- **The oracle restricted to the low inputs `i < R`**: the same nodes with every input `i ≥ R` constant `false`. -/
def restrictHigh (R : ℕ) {w : ℕ} (O : BooleanCircuit w) : BooleanCircuit R where
  nodes := O.nodes.map (restrictNode R)
  output := ⟨O.output.val, by simp⟩
  wellFormed := fun i => by
    rw [List.get_eq_getElem, List.getElem_map]
    exact restrictNode_wf R _ _ (O.wellFormed ⟨i.val, by simpa using i.isLt⟩)

theorem restrictHigh_size (R : ℕ) {w : ℕ} (O : BooleanCircuit w) : (restrictHigh R O).size = O.size := by
  simp [restrictHigh, BooleanCircuit.size]

theorem restrictHigh_length (R : ℕ) {w : ℕ} (O : BooleanCircuit w) :
    (restrictHigh R O).nodes.length = O.nodes.length := by
  simp [restrictHigh]

variable {R w : ℕ} (h : R ≤ w)

theorem firstNode_restrict (proj : Fin R → ProjectedRandomBit R) (node : BooleanNode w) :
    firstNode (padProj h proj) node = castNode h (firstNode proj (restrictNode R node)) := by
  cases node with
  | input i =>
    by_cases hi : i.val < R
    · have e : padProj h proj i = ProjectionPCPPadding.liftProjectedRandomBit h (proj ⟨i.val, hi⟩) := by
        unfold padProj; rw [dif_pos hi]
      simp only [firstNode, restrictNode, dif_pos hi, e]
      cases proj ⟨i.val, hi⟩ <;> rfl
    · have e : padProj h proj i = .constant false := by
        unfold padProj; rw [dif_neg hi]
      simp only [firstNode, restrictNode, dif_neg hi, e]
      rfl
  | _ => rfl

theorem secondNode_restrict (base index : ℕ) (proj : Fin R → ProjectedRandomBit R) (node : BooleanNode w) :
    secondNode base index (padProj h proj) node = castNode h (secondNode base index proj (restrictNode R node)) := by
  cases node with
  | input i =>
    by_cases hi : i.val < R
    · have e : padProj h proj i = ProjectionPCPPadding.liftProjectedRandomBit h (proj ⟨i.val, hi⟩) := by
        unfold padProj; rw [dif_pos hi]
      simp only [secondNode, restrictNode, dif_pos hi, e]
      cases proj ⟨i.val, hi⟩ <;> rfl
    · have e : padProj h proj i = .constant false := by
        unfold padProj; rw [dif_neg hi]
      simp only [secondNode, restrictNode, dif_neg hi, e]
      rfl
  | _ => rfl

end Restrict

/-! ## The builders, as, at a general oracle -/

section Builders
variable {R w : ℕ} (h : R ≤ w)

theorem copyPrefix_restrict (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (O : BooleanCircuit w) (proj : Fin R → ProjectedRandomBit R) :
    ∀ (count : ℕ) (hc : count ≤ (restrictHigh R O).nodes.length) (hc' : count ≤ O.nodes.length),
      (copyPrefix prior' O (padProj h proj) count hc').builder.nodes =
        (copyPrefix prior (restrictHigh R O) proj count hc).builder.nodes.map (castNode h) := by
  have hlen : prior'.nodes.length = prior.nodes.length := by rw [hp, List.length_map]
  intro count
  induction count with
  | zero => intro _ _; exact hp
  | succ count ih =>
    intro hc hc'
    simp only [copyPrefix, copyNode_nodes, List.map_append, List.map_cons, List.map_nil]
    rw [ih (by omega) (by omega)]
    simp only [restrictHigh, List.getElem_map, hlen, firstNode_restrict, secondNode_restrict]

theorem copyOracle_restrict (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (O : BooleanCircuit w) (proj : Fin R → ProjectedRandomBit R) :
    (copyOracle prior' O (padProj h proj)).final.nodes =
        (copyOracle prior (restrictHigh R O) proj).final.nodes.map (castNode h) ∧
      ((copyOracle prior' O (padProj h proj)).output 0).val =
        ((copyOracle prior (restrictHigh R O) proj).output 0).val := by
  have hlen : prior'.nodes.length = prior.nodes.length := by rw [hp, List.length_map]
  have hcount := restrictHigh_length R O
  have hcong : ∀ (n1 n2 : ℕ) (_e : n1 = n2) (p1 : n1 ≤ (restrictHigh R O).nodes.length)
      (p2 : n2 ≤ (restrictHigh R O).nodes.length),
      (copyPrefix prior (restrictHigh R O) proj n1 p1).builder.nodes =
        (copyPrefix prior (restrictHigh R O) proj n2 p2).builder.nodes := by
    intro n1 n2 e p1 p2; subst e; rfl
  refine ⟨?_, ?_⟩
  · exact (copyPrefix_restrict h prior prior' hp O proj O.nodes.length (by omega) le_rfl).trans
      (congrArg (List.map (castNode h)) (hcong _ _ hcount.symm _ _))
  · simp [copyOracle, hlen, restrictHigh]

theorem copyQuery_restrict (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (O : BooleanCircuit w) (proj : Fin R → ProjectedRandomBit R) :
    (copyQuery prior' O (padProj h proj)).final.nodes =
      (copyQuery prior (restrictHigh R O) proj).final.nodes.map (castNode h) := by
  obtain ⟨h1, h2⟩ := copyOracle_restrict h prior prior' hp O proj
  simp only [copyQuery, BooleanDAGBuilder.appendNot, BooleanDAGBuilder.append, BooleanDAGBuilder.appendNode_nodes,
    List.map_append, List.map_cons, List.map_nil, h1, h2]
  rfl

theorem queryPrefix_restrict {q : ℕ} (prior : BooleanDAGBuilder R) (prior' : BooleanDAGBuilder w)
    (hp : prior'.nodes = prior.nodes.map (castNode h)) (O : BooleanCircuit w)
    (projections : Fin q → Fin R → ProjectedRandomBit R) :
    ∀ (count : ℕ) (hc : count ≤ q),
      (queryPrefix prior' O (fun j => padProj h (projections j)) count hc).builder.nodes =
        (queryPrefix prior (restrictHigh R O) projections count hc).builder.nodes.map (castNode h) := by
  intro count
  induction count with
  | zero => intro _; exact hp
  | succ count ih =>
    intro hc
    exact copyQuery_restrict h _ _ (ih (by omega)) O _

/-- **The padded substituted circuit of a general oracle is the cast native one of its restriction.** -/
theorem substituted_restrict {q : ℕ} (O : BooleanCircuit w) (projections : Fin q → Fin R → ProjectedRandomBit R)
    (formula : ThreeCNF q) :
    substituted O (fun j => padProj h (projections j)) formula =
      castCircuit h (substituted (restrictHigh R O) projections formula) := by
  have h0 : (BooleanDAGBuilder.empty w).nodes = (BooleanDAGBuilder.empty R).nodes.map (castNode h) := rfl
  have hbank := queryPrefix_restrict h (BooleanDAGBuilder.empty R) (BooleanDAGBuilder.empty w) h0 O projections q le_rfl
  have hsize : O.size = (restrictHigh R O).size := (restrictHigh_size R O).symm
  have hout : O.output.val = (restrictHigh R O).output.val := rfl
  have hinit : ((queryBank (BooleanDAGBuilder.empty w) O fun j => padProj h (projections j)).appendConst
      true).builder.nodes = ((queryBank (BooleanDAGBuilder.empty R) (restrictHigh R O) projections).appendConst
        true).builder.nodes.map (castNode h) := by
    simp only [BooleanDAGBuilder.appendConst, BooleanDAGBuilder.append, BooleanDAGBuilder.appendNode_nodes,
      List.map_append, List.map_cons, List.map_nil, queryBank, hbank]
    rfl
  have hbanklen : (queryBank (BooleanDAGBuilder.empty w) O fun j => padProj h (projections j)).nodes.length
      = (queryBank (BooleanDAGBuilder.empty R) (restrictHigh R O) projections).nodes.length := by
    simp only [queryBank, hbank, List.length_map]
  obtain ⟨hn, ho⟩ := compileClauses_cast h formula.clauses
    ((queryBank (BooleanDAGBuilder.empty R) (restrictHigh R O) projections).appendConst true).builder
    ((queryBank (BooleanDAGBuilder.empty w) O fun j => padProj h (projections j)).appendConst true).builder
    hinit
    (fun literal => ((queryBank (BooleanDAGBuilder.empty R) (restrictHigh R O) projections).appendConst true).lift
      (literalRef (BooleanDAGBuilder.empty R) (restrictHigh R O) projections literal))
    (fun literal => ((queryBank (BooleanDAGBuilder.empty w) O
      fun j => padProj h (projections j)).appendConst true).lift
      (literalRef (BooleanDAGBuilder.empty w) O (fun j => padProj h (projections j)) literal))
    (fun l => by
      cases l <;> simp only [BooleanDAGBuilder.appendConst, BooleanDAGBuilder.append, BooleanDAGBuilder.liftRef_val,
        literalRef, queryRef, hsize, hout] <;> rfl)
    ((queryBank (BooleanDAGBuilder.empty R) (restrictHigh R O) projections).appendConst true).output
    ((queryBank (BooleanDAGBuilder.empty w) O fun j => padProj h (projections j)).appendConst true).output
    (by simp only [BooleanDAGBuilder.appendConst, BooleanDAGBuilder.append, BooleanDAGBuilder.newest, hbanklen])
  apply circuit_ext
  · exact hn
  · exact ho

theorem compactSubstituted_restrict {q : ℕ} (O : BooleanCircuit w)
    (projections : Fin q → Fin R → ProjectedRandomBit R) (formula : ThreeCNF q) :
    compactSubstituted O (fun j => padProj h (projections j)) formula =
      castCircuit h (compactSubstituted (restrictHigh R O) projections formula) :=
  substituted_restrict h O projections (compactThreeCNF formula)

end Builders

/-! ## The padded native circuit (G1) and the union request (G2) -/

/-- Compacting an already compacted formula changes nothing (base's `compact_request`, at the circuit). -/
theorem compact_subG {n r q : ℕ} (oracle : BooleanCircuit n) (projections : Fin q → Fin n → ProjectedRandomBit r)
    (formula : ThreeCNF q) :
    compactSubstituted oracle projections (compactThreeCNF formula) = compactSubstituted oracle projections formula := by
  simp only [compactSubstituted, compactThreeCNF, List.dedup_idem]

/-- The union request at the padding of any projection PCP is the request of the cast circuit of the restriction. -/
theorem unionRequest_restrict {M : TimedDecisionMachine} {T : ℕ → ℕ} (pcp : ProjectionPCP M T) (wf : ℕ → ℕ)
    (hw : ∀ n, pcp.nativeWidth n ≤ wf n) (a : PointwisePCPPAlgorithm) {N : ℕ} (z : BitInput N)
    (O : BooleanCircuit (wf N)) :
    unionRequest (ProjectionPCPPadding.padProjectionPCP pcp wf hw) a z O =
      PCPPRequestBoundary.request a (castCircuit (hw N)
        (compactSubstituted (restrictHigh (pcp.nativeWidth N) O) (pcp.queryAddressBits z)
          (pcp.decision z fun _ => false))) := by
  have hq : (ProjectionPCPPadding.padProjectionPCP pcp wf hw).queryAddressBits z =
      fun j => padProj (hw N) (pcp.queryAddressBits z j) := by
    funext j i
    rfl
  have hd : (ProjectionPCPPadding.padProjectionPCP pcp wf hw).decision z (fun _ => false) =
      pcp.decision z (fun _ => false) := rfl
  unfold unionRequest sourceRequest
  rw [hq, hd]
  exact congrArg (PCPPRequestBoundary.request a)
    (compactSubstituted_restrict (hw N) O (pcp.queryAddressBits z) (pcp.decision z fun _ => false))

section Native
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

/-- **The padded substituted circuit of a width-`q` oracle** (G1): the cast of base's native substituted circuit at
the oracle restricted to the native width `R`. -/
noncomputable def padSubstituted (k CH Cpad : ℕ) (code : List Bool) {n : ℕ} (x : BitInput n) (hpad : k + 3 ≤ Cpad) {q : ℕ}
    (hq : PCPPNativeHierarchyNodes.width source k CH Cpad code x ≤ q) (O : BooleanCircuit q) : BooleanCircuit q :=
  castCircuit hq (PCPPNativeHierarchyNodes.circuit source k CH Cpad code x hpad
    (restrictHigh (PCPPNativeHierarchyNodes.width source k CH Cpad code x) O))

/-- The native width at a source request is the hierarchy PCP's width. -/
theorem native_le {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hcoeff : H.coefficient ≤ Cpad)
    (hpad : k + 3 ≤ Cpad) (wf : ℕ → ℕ)
    (hw : ∀ n, (HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.nativeWidth n ≤ wf n)
    (r : InputRequest) :
    PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ wf r.1 :=
  (le_of_eq (HierarchyStreams.hierarchy_dimensions source H Cpad hpad r).2.1).trans (hw r.1)

/-- **The hierarchy PCP's padded request of a restricted oracle is the request of `padSubstituted`** (base's
compaction idempotence and `normalized_hierarchy`). -/
theorem separated_restrict {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (a : PointwisePCPPAlgorithm) (r : InputRequest) {q : ℕ}
    (hw : (HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.nativeWidth r.1 ≤ q)
    (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (O : BooleanCircuit q) :
    PCPPRequestBoundary.request a (castCircuit hw (compactSubstituted
      (restrictHigh ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.nativeWidth r.1) O)
      ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.queryAddressBits r.2)
      ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.decision r.2 fun _ => false))) =
    PCPPRequestBoundary.request a
      (padSubstituted source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad hq O) := by
  have actual : ∀ hp : (RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
      (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad).nativeWidth r.1 ≤ q,
      PCPPRequestBoundary.request a (castCircuit hp (compactSubstituted
        (restrictHigh ((RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
          (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad).nativeWidth r.1) O)
        ((RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
          (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad).queryAddressBits r.2)
        ((RecoveryPCPFormulaResumeHierarchy.normalized source k H.coefficient Cpad
          (VerifierEncoding.code H.verifier) (List.ofFn r.2) hpad).decision r.2 fun _ => false))) =
      PCPPRequestBoundary.request a
        (padSubstituted source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad hq O) :=
    fun _ => rfl
  rw [RecoveryPCPFormulaResumeHierarchy.normalized_hierarchy source H Cpad hpad r] at actual
  have e : (HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.nativeWidth r.1 =
      (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).nativeWidth r.1 := rfl
  have hp : (RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).nativeWidth r.1 ≤ q := by
    rw [← e]; exact hw
  have hcs : compactSubstituted
      (restrictHigh ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.nativeWidth r.1) O)
      ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.queryAddressBits r.2)
      ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.decision r.2 fun _ => false) =
      @compactSubstituted
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).nativeWidth r.1)
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).nativeWidth r.1)
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).queryCount r.1)
        (restrictHigh ((HierarchyNormalized.separated source H Cpad hcoeff hpad).data.pcp.nativeWidth r.1) O)
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).queryAddressBits r.2)
        ((RecoveryPCPFormulaResumeHierarchy.hierarchyNormalized source H Cpad hpad r).decision r.2 fun _ => false) :=
    compact_subG _ _ _
  rw [hcs, ← actual hp]
  rfl

end Native

section Gate
variable (l : Literals)

/-- The native width at `z` is at most the padded width `wf N`. -/
theorem nativeWidth_le {kclk : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))) (wf : ℕ → ℕ)
    (hw : ∀ n, (hierarchyPCP l H).data.pcp.nativeWidth n ≤ wf n) {N : ℕ} (z : BitInput N) :
    PCPPNativeHierarchyNodes.width (gateSource l) kclk H.coefficient (cpadOf H) (VerifierEncoding.code H.verifier) z ≤
      wf N :=
  native_le (gateSource l) H (cpadOf H) (le_max_left _ _) (le_max_right _ _) wf hw ⟨N, z⟩

/-- **G2: the union setup's padded request at a general-width oracle is the request of `padSubstituted`.** -/
theorem unionRequest_padG {kclk : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (kclk + 2))) (wf : ℕ → ℕ)
    (hw : ∀ n, (hierarchyPCP l H).data.pcp.nativeWidth n ≤ wf n) {N : ℕ} (z : BitInput N)
    (O : BooleanCircuit (wf N)) :
    unionRequest (ProjectionPCPPadding.padProjectionPCP (hierarchyPCP l H).data.pcp wf hw) (gatePCPP l) z O =
      PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk H.coefficient (cpadOf H)
        (VerifierEncoding.code H.verifier) z (le_max_right _ _) (nativeWidth_le l H wf hw z) O) :=
  (unionRequest_restrict _ wf hw (gatePCPP l) z O).trans
    (separated_restrict (gateSource l) H (cpadOf H) (le_max_left _ _) (le_max_right _ _) (gatePCPP l) ⟨N, z⟩ (hw N)
      (nativeWidth_le l H wf hw z) O)

/-! ## The pinned setup `Split.setupF` (both `S₂` branches) -/

variable (F : Split.GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- On the recovered language the pinned setup is the refuter branch. -/
theorem setupF_eq_rec (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) (h : L = recL l kclk) :
    Split.setupF l F kclk coef A a ha L hL = recSetup2 l (Split.gate0 l F) kclk coef A a ha := by
  subst h
  exact unionSetupS2_recL l (Split.gate0 l F) kclk coef A a ha hL

/-- Off the recovered language the pinned setup is `S₁`. -/
theorem setupF_eq_other (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) (h : L ≠ recL l kclk) :
    Split.setupF l F kclk coef A a ha L hL = unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL := by
  show unionSetupS2 l (Split.gate0 l F) kclk coef A a ha L hL = _
  unfold unionSetupS2
  rw [dif_neg h]

/-- **(A) The pinned setup's padded width is the ledger's `q(N)` past a cutoff** (`A_pad = gateApad l`). -/
theorem setupF_width (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) :
    ∃ N₀, ∀ N, N₀ ≤ N → (Split.setupF l F kclk coef A a ha L hL).pcp.nativeWidth N =
      Ledger.nativeWidth kclk (gateApad l) N := by
  by_cases h : L = recL l kclk
  · obtain ⟨N₀, hN₀⟩ := recSetup2_width l (Split.gate0 l F) kclk coef A a ha le_rfl
    refine ⟨N₀, fun N hN => ?_⟩
    rw [setupF_eq_rec l F kclk coef A a ha L hL h]
    exact hN₀ N hN
  · obtain ⟨N₀, hN₀⟩ := unionSetupS1_width l (Split.gate0 l F) kclk coef A a ha L hL le_rfl
    refine ⟨N₀, fun N hN => ?_⟩
    rw [setupF_eq_other l F kclk coef A a ha L hL h]
    exact hN₀ N hN

/-- **(B) at the refuter branch**: the setup's request is the request of `padSubstituted` at the refuter hierarchy. -/
theorem recSetup2_request_padG {N : ℕ} (z : BitInput N)
    (O : BooleanCircuit ((recSetup2 l (Split.gate0 l F) kclk coef A a ha).pcp.nativeWidth N))
    (hq : PCPPNativeHierarchyNodes.width (gateSource l) kclk (refH l kclk).coefficient (cpadOf (refH l kclk))
      (VerifierEncoding.code (refH l kclk).verifier) z ≤ (recSetup2 l (Split.gate0 l F) kclk coef A a ha).pcp.nativeWidth N) :
    (recSetup2 l (Split.gate0 l F) kclk coef A a ha).request z O =
      PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk (refH l kclk).coefficient
        (cpadOf (refH l kclk)) (VerifierEncoding.code (refH l kclk).verifier) z (le_max_right _ _) hq O) :=
  unionRequest_padG l (refH l kclk) (paddedWidth l (Split.gate0 l F) (refH l kclk)) (fun _ => le_max_left _ _) z O

/-- **(B) at the `S₁` branch**: the setup's request is the request of `padSubstituted` at the language's hierarchy. -/
theorem unionSetupS1_request_padG (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) {N : ℕ} (z : BitInput N)
    (O : BooleanCircuit ((unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).pcp.nativeWidth N))
    (hq : PCPPNativeHierarchyNodes.width (gateSource l) kclk (hierarchyOf hL).coefficient (cpadOf (hierarchyOf hL))
      (VerifierEncoding.code (hierarchyOf hL).verifier) z ≤
        (unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).pcp.nativeWidth N) :
    (unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).request z O =
      PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk (hierarchyOf hL).coefficient
        (cpadOf (hierarchyOf hL)) (VerifierEncoding.code (hierarchyOf hL).verifier) z (le_max_right _ _) hq O) :=
  unionRequest_padG l (hierarchyOf hL) (paddedWidth l (Split.gate0 l F) (hierarchyOf hL)) (fun _ => le_max_left _ _) z O

/-- The clause word of the refuter branch's PCPP output. -/
theorem recSetup2_pcppOutput {N : ℕ} (z : BitInput N)
    (O : BooleanCircuit ((recSetup2 l (Split.gate0 l F) kclk coef A a ha).pcp.nativeWidth N))
    (hq : PCPPNativeHierarchyNodes.width (gateSource l) kclk (refH l kclk).coefficient (cpadOf (refH l kclk))
      (VerifierEncoding.code (refH l kclk).verifier) z ≤ (recSetup2 l (Split.gate0 l F) kclk coef A a ha).pcp.nativeWidth N) :
    pcppOutput ((recSetup2 l (Split.gate0 l F) kclk coef A a ha).request z O)
        ((recSetup2 l (Split.gate0 l F) kclk coef A a ha).pcppOf z O) =
      pcppOutput (PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk (refH l kclk).coefficient
        (cpadOf (refH l kclk)) (VerifierEncoding.code (refH l kclk).verifier) z (le_max_right _ _) hq O))
        ((gatePCPP l).output (PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk
          (refH l kclk).coefficient (cpadOf (refH l kclk)) (VerifierEncoding.code (refH l kclk).verifier) z
          (le_max_right _ _) hq O))) := by
  show pcppOutput ((recSetup2 l (Split.gate0 l F) kclk coef A a ha).request z O)
    ((gatePCPP l).output ((recSetup2 l (Split.gate0 l F) kclk coef A a ha).request z O)) = _
  rw [recSetup2_request_padG l F kclk coef A a ha z O hq]
  rfl

/-- The clause word of the `S₁` branch's PCPP output. -/
theorem unionSetupS1_pcppOutput (L : Language) (hL : InNTIME (fun n => n ^ (kclk + 2)) L) {N : ℕ} (z : BitInput N)
    (O : BooleanCircuit ((unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).pcp.nativeWidth N))
    (hq : PCPPNativeHierarchyNodes.width (gateSource l) kclk (hierarchyOf hL).coefficient (cpadOf (hierarchyOf hL))
      (VerifierEncoding.code (hierarchyOf hL).verifier) z ≤
        (unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).pcp.nativeWidth N) :
    pcppOutput ((unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).request z O)
        ((unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).pcppOf z O) =
      pcppOutput (PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk
        (hierarchyOf hL).coefficient (cpadOf (hierarchyOf hL)) (VerifierEncoding.code (hierarchyOf hL).verifier) z
          (le_max_right _ _) hq O))
        ((gatePCPP l).output (PCPPRequestBoundary.request (gatePCPP l) (padSubstituted (gateSource l) kclk
          (hierarchyOf hL).coefficient (cpadOf (hierarchyOf hL)) (VerifierEncoding.code (hierarchyOf hL).verifier) z
          (le_max_right _ _) hq O))) := by
  show pcppOutput ((unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).request z O)
    ((gatePCPP l).output ((unionSetupS1 l (Split.gate0 l F) kclk coef A a ha L hL).request z O)) = _
  rw [unionSetupS1_request_padG l F kclk coef A a ha L hL z O hq]
  rfl

end Gate

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
