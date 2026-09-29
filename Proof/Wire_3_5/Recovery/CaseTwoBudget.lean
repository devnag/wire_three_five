import Proof.Wire_3_5.Recovery.CaseTwoExec

/-! # The hybrid Case-2 costs are polynomial (P3:3769-3771; D1.6 A3d)

Realizes, for the hybrid Case 2, "There are at most `2^{O(q)}` SAT queries and local work, in addition to
`poly(T(N_a)) = 2^{O(q)}` refuter work. Since `q = O(n)`, this is `2^{O(n)}` overall" (P3:3769-3771): the per-copy cost of
the padded whole block (`wbudget`) is at most a fixed monotone polynomial `blockEnv` of `Env(N) + q`, where
`Env(N)` is base's hierarchy envelope of the source length (`CloseoutCaseTwo.WholeBudgetHierarchy.envelope`, polynomial
in `N`); every term is charged by base's generic cost lemmas (`PCPPNativeResourceCost.descriptor_budget`,
`cache_parameter`, `PCPPNative.descriptor_length_bound`, `WholeBudget.request_source_bound`, `occurrence_bound`).

Paper quantity of the main type (`wbudget_le`): the padded Case-2 block's step bound, `2·wbudget + 4 ≤ blockEnv(Env + q)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoBudget
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPad NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadSource
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadBlock NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadWhole

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

/-! ## A monotone polynomial envelope of one padded block -/

/-- The PCPP measure of a request of size and arity at most `M + minimumArity`. -/
def capM (M : ℕ) : ℕ := PCPPQueryCachedBounds.capacity a (3 * M + 2 * a.minimumArity)
/-- The padded producer's fuel bound. -/
def fuelM (M : ℕ) : ℕ := M + 1 + (6 * M + 20)
/-- The padded request's source and descriptor costs. -/
def srcM (M : ℕ) : ℕ :=
  (2 * (6 * fuelM M + 8 + (9216 * (a.minimumArity + 2 * M + 1) ^ 2 + 2 * fuelM M + 3)) +
      4 * (39 * (3 * M + 2 * a.minimumArity + 5) ^ 2) + 7) + 1 +
    (2 * (PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) * (2 * M + 1)) ^ PCPPSourceCache.totalDegree a) +
      8 * (3 * capM a M + 3) + 16)
/-- **The block envelope**: a monotone polynomial of `Env + q` bounding one padded block. -/
def blockEnv (D M : ℕ) : ℕ :=
  2 * ((2 * ((4 * M + 3) + 1 + (4 * M + 3)) + 2) + 1 + srcM a M + 1 + WholeBudget.localEnvelope D 0 (capM a M)) + 4

theorem capacity_mono {m n : ℕ} (h : m ≤ n) : PCPPQueryCachedBounds.capacity a m ≤ PCPPQueryCachedBounds.capacity a n := by
  unfold PCPPQueryCachedBounds.capacity
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem capM_mono : Monotone (capM a) := fun _ _ h => capacity_mono a (by omega)
theorem fuelM_mono : Monotone fuelM := fun _ _ h => by unfold fuelM; omega

theorem srcM_mono : Monotone (srcM a) := by
  intro m n h
  have hf := fuelM_mono h
  have hc := capM_mono a h
  unfold srcM
  gcongr

theorem blockEnv_mono (D : ℕ) : Monotone (blockEnv a D) := by
  intro m n h
  have hs := srcM_mono a h
  have hl := WholeBudget.local_monotone D 0 (capM_mono a h)
  unfold blockEnv
  gcongr

open NearCubicWires.PaddedRunnerBudgetClosure in
/-- **The block envelope of a polynomial is a polynomial.** -/
theorem blockEnv_poly (D : ℕ) {f : ℕ → ℕ} (hf : SourcePoly f) : SourcePoly (fun x => blockEnv a D (f x)) := by
  have hc (v : ℕ) := polyDominated_const (measureOf := (fun n : ℕ => n)) v
  have hcap : SourcePoly (fun x => capM a (f x)) :=
    ((sourcePoly_pow (((hf.const_mul 3).add (hc (2 * a.minimumArity))).add (hc 1))
      (PCPPQueryCachedBounds.degree a)).const_mul (PCPPQueryCachedBounds.coefficient a)).mono (fun _ => le_of_eq rfl)
  have hfuel : SourcePoly (fun x => fuelM (f x)) :=
    (((hf.add (hc 1)).add ((hf.const_mul 6).add (hc 20)))).mono (fun _ => le_of_eq rfl)
  have hA : SourcePoly (fun x => 2 * (6 * fuelM (f x) + 8 + (9216 * (a.minimumArity + 2 * f x + 1) ^ 2 +
      2 * fuelM (f x) + 3))) :=
    ((((hfuel.const_mul 6).add (hc 8)).add ((((sourcePoly_pow (((hc a.minimumArity).add (hf.const_mul 2)).add (hc 1))
      2).const_mul 9216).add (hfuel.const_mul 2)).add (hc 3))).const_mul 2)
  have hB : SourcePoly (fun x => 4 * (39 * (3 * f x + 2 * a.minimumArity + 5) ^ 2)) :=
    ((sourcePoly_pow (((hf.const_mul 3).add (hc (2 * a.minimumArity))).add (hc 5)) 2).const_mul 39).const_mul 4
  have hR : SourcePoly (fun x => 2 * (PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) * (2 * f x + 1)) ^
      PCPPSourceCache.totalDegree a) + 8 * (3 * capM a (f x) + 3) + 16) :=
    ((((sourcePoly_pow (((hf.const_mul 2).add (hc 1)).const_mul (2 * a.minimumArity + 5))
      (PCPPSourceCache.totalDegree a)).const_mul (PCPPSourceCache.coefficient a)).const_mul 2).add
      (((hcap.const_mul 3).add (hc 3)).const_mul 8)).add (hc 16)
  have hsrc : SourcePoly (fun x => srcM a (f x)) :=
    ((((hA.add hB).add (hc 7)).add (hc 1)).add hR).mono (fun _ => le_of_eq rfl)
  have hloc := WholeBudget.local_polynomial D 0 hcap
  have hCI : SourcePoly (fun x => 2 * ((4 * f x + 3) + 1 + (4 * f x + 3)) + 2) :=
    ((((((hf.const_mul 4).add (hc 3)).add (hc 1)).add ((hf.const_mul 4).add (hc 3))).const_mul 2).add (hc 2))
  exact ((((((hCI.add (hc 1)).add hsrc).add (hc 1)).add hloc).const_mul 2).add (hc 4)).mono (fun _ => le_of_eq rfl)

/-! ## The native producer's quantities under the hierarchy envelope -/

section Block
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  (degree : ℕ)

/-- The native producer writes its node stream within its fuel. -/
theorem stream_le (hcoeff : H.coefficient ≤ Cpad) :
    ((PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle := by
  obtain ⟨native, hn, ns, _, head, _⟩ := PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hlen := SelectiveReset.prefix_head (prefix_of_run _ _ _ native hn).1 (PCPPNativeHierarchyNodes.slots source k 177)
  rw [head] at hlen
  change ((PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).nodes.flatMap PCPPRequestNodeSchema.native).length ≤ 0 + native.steps at hlen
  omega

include hpad in
/-- The native producer's fuel is within the envelope. -/
theorem nodes_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle ≤
      WholeBudgetHierarchy.envelope source a H Cpad degree r.1 := by
  have hb := (WholeBudgetHierarchy.bounds source a H Cpad degree hcoeff hpad r oracle horacle).1
  unfold PCPPNativeHierarchySource.originalBudget PCPPNativeClauseDescriptorConsumer.sourceBudget
    PCPPNativeSource.budget PCPPNativeClauseDescriptorConsumer.budget at hb
  omega

/-- The native substituted circuit's size is within the envelope. -/
theorem csize_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).size ≤ WholeBudgetHierarchy.envelope source a H Cpad degree r.1 := by
  have hb := (WholeBudgetHierarchy.bounds source a H Cpad degree hcoeff hpad r oracle horacle).2.1
  set c := PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
    oracle with hc
  have hm := WholeBudget.measure_parameter a (PCPPRequestBoundary.request a c)
  have hs := PCPPRequestBoundary.request_size a c
  change (PCPPRequestBoundary.request a c).circuit.size + (PCPPRequestBoundary.request a c).arity ≤
    PCPPQueryCachedBounds.capacity a ((PCPPRequestBoundary.request a c).circuit.size +
      (PCPPRequestBoundary.request a c).arity) at hm
  have := le_max_left c.size (PCPPRequestBoundary.domain a
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  omega

section Pieces
variable (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)

/-- The padded descriptor and its framed word. -/
theorem pbudget_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    pbudget source a H Cpad hpad r oracle q hq ≤
      2 * (6 * fuelM (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 8 +
        (9216 * (a.minimumArity + 2 * (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 1) ^ 2 +
          2 * fuelM (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 3)) +
      4 * (39 * (3 * (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 2 * a.minimumArity + 5) ^ 2) +
      7 := by
  unfold pbudget PCPPNativeClauseDescriptorConsumer.budget
  have hnodes := nodes_le source a H Cpad hpad r oracle degree hcoeff horacle
  have hcs := csize_le source a H Cpad hpad r oracle degree hcoeff horacle
  set Env := WholeBudgetHierarchy.envelope source a H Cpad degree r.1 with hEnv
  set M := Env + q with hM
  set c := PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
    oracle with hc
  have hsz : (castCircuit hq c).size = c.size := castCircuit_size hq c
  have hstream : ((castCircuit hq c).nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle := by
    rw [stream_cast]; exact stream_le source H Cpad hpad r oracle hcoeff
  set fuel := PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle + 1 + widthFixCost q with hfuel
  have hfM : fuel ≤ fuelM M := by simp only [hfuel, fuelM, widthFixCost, hM]; omega
  have hdb := PCPPNativeResourceCost.descriptor_budget a (castCircuit hq c) fuel (by omega)
  have hsq : (a.minimumArity + q + (castCircuit hq c).size + 1) ^ 2 ≤ (a.minimumArity + 2 * M + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h9 := Nat.mul_le_mul_left 9216 hsq
  set req := PCPPRequestBoundary.request a (castCircuit hq c) with hreq
  have hreqs : req.circuit.size = max (castCircuit hq c).size (PCPPRequestBoundary.domain a q) :=
    PCPPRequestBoundary.request_size a (castCircuit hq c)
  have hreqa : req.arity = max q a.minimumArity := rfl
  have hdom : PCPPRequestBoundary.domain a q = max q a.minimumArity := rfl
  have hsa : req.arity + req.circuit.size ≤ 3 * M + 2 * a.minimumArity := by
    rw [hreqs, hreqa, hdom, hsz]
    have := le_max_left q a.minimumArity
    omega
  have hdl' : (PCPPNative.descriptor req.circuit).length ≤ 39 * (3 * M + 2 * a.minimumArity + 5) ^ 2 :=
    (PCPPNative.descriptor_length_bound req.circuit).trans (Nat.mul_le_mul_left 39 (Nat.pow_le_pow_left (by omega) 2))
  omega

/-- The padded request's source call. -/
theorem rsource_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :
    RequestSource.budget a (PCPPRequestBoundary.request a (castCircuit hq
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))) ≤
      2 * (PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) *
        (2 * (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 1)) ^ PCPPSourceCache.totalDegree a) +
      8 * (3 * capM a (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 3) + 16 := by
  have hcs := csize_le source a H Cpad hpad r oracle degree hcoeff horacle
  set Env := WholeBudgetHierarchy.envelope source a H Cpad degree r.1 with hEnv
  set M := Env + q with hM
  set c := PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
    oracle with hc
  have hsz : (castCircuit hq c).size = c.size := castCircuit_size hq c
  set req := PCPPRequestBoundary.request a (castCircuit hq c) with hreq
  have hreqs : req.circuit.size = max (castCircuit hq c).size (PCPPRequestBoundary.domain a q) :=
    PCPPRequestBoundary.request_size a (castCircuit hq c)
  have hreqa : req.arity = max q a.minimumArity := rfl
  have hdom : PCPPRequestBoundary.domain a q = max q a.minimumArity := rfl
  have hsa : req.circuit.size + req.arity ≤ 3 * M + 2 * a.minimumArity := by
    rw [hreqs, hreqa, hdom, hsz]
    have := le_max_left q a.minimumArity
    omega
  have hrs := WholeBudget.request_source_bound a req
  have hcp := PCPPNativeResourceCost.cache_parameter a (castCircuit hq c)
  have htb : PCPPSourceCache.totalBudget a req ≤
      PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) * (2 * M + 1)) ^ PCPPSourceCache.totalDegree a := by
    unfold PCPPSourceCache.totalBudget
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hcp.trans (Nat.mul_le_mul_left _ ?_)) _)
    rw [hsz]; omega
  have hmeas : WholeBudget.measure a req ≤ capM a M := capacity_mono a (by omega)
  have hin : (pcppInput req).length ≤ 3 * WholeBudget.measure a req + 3 := (WholeBudget.components a req).2.2.1
  omega

end Pieces

/-- **One padded block is within the block envelope** of `Env(N) + q` (block `0`, any address fields). -/
theorem wbudget_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (D : ℕ) (u : BitInput (wrequest source a H Cpad hpad r oracle q hq).arity)
    (clause : BitInput (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
    (position : Bool) (padding : ℕ)
    (hcap : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits + padding =
      CloseoutLanguage.clauseWidth D (wrequest source a H Cpad hpad r oracle q hq).arity) :
    2 * wbudget source a H Cpad hpad r oracle q hq D 0 u clause position padding + 4 ≤
      blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) := by
  have hbd := WholeBudgetHierarchy.bounds source a H Cpad degree hcoeff hpad r oracle horacle
  have hPB := pbudget_le source a H Cpad hpad r oracle degree q hq hcoeff horacle
  have hRS := rsource_le source a H Cpad hpad r oracle degree q hq hcoeff horacle
  have hmeas : WholeBudget.measure a (wrequest source a H Cpad hpad r oracle q hq) ≤
      capM a (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) := by
    have hcs := csize_le source a H Cpad hpad r oracle degree hcoeff horacle
    refine capacity_mono a ?_
    have hreqs := PCPPRequestBoundary.request_size a (castCircuit hq
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))
    have hsz := castCircuit_size hq
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    change (wrequest source a H Cpad hpad r oracle q hq).circuit.size +
      max q a.minimumArity ≤ _
    change (wrequest source a H Cpad hpad r oracle q hq).circuit.size = max _ (max q a.minimumArity) at hreqs
    have := le_max_left q a.minimumArity
    omega
  have hOC := (WholeBudget.occurrence_bound D 0 0 a (wrequest source a H Cpad hpad r oracle q hq) u clause position
    padding le_rfl hcap).trans (WholeBudget.local_monotone D 0 hmeas)
  have hCI : CompoundInput.budget (HierarchySourceInput.hierarchyInput H r) (PCPPNative.descriptor oracle) ≤
      2 * ((4 * (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 3) + 1 +
        (4 * (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) + 3)) + 2 := by
    have := hbd.2.2.1
    have := hbd.2.2.2
    unfold CompoundInput.budget RecoveryPCPFormulaResumeSearchPair.budget; omega
  unfold wbudget sbudget obudget blockEnv srcM
  omega

end Block

/-! ## The fold's capacity need and cost -/

section Fold
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoFold NearCubicWires.WireExponent3_5.Transfer.CaseTwoFoldRun
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
  (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
  (degree D : ℕ)

/-- **Every round of the fold is within the block envelope** plus the crop's and the copy's linear costs. -/
theorem roundCost_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    {N : ℕ} (point : BitInput N) (i : ℕ) (hfit : (i + 1) * widthOf source a H Cpad hpad r oracle q hq D ≤ N) :
    CaseTwoFold.roundCost source a H Cpad hpad r oracle q hq D point i ≤
      2 * q + 5 + (12 * N + 11) + 1 + blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) := by
  have hiw : i * widthOf source a H Cpad hpad r oracle q hq D + widthOf source a H Cpad hpad r oracle q hq D ≤ N := by
    have : (i + 1) * widthOf source a H Cpad hpad r oracle q hq D =
      i * widthOf source a H Cpad hpad r oracle q hq D + widthOf source a H Cpad hpad r oracle q hq D := by ring
    omega
  have hwb := wbudget_le source a H Cpad hpad r oracle degree hcoeff horacle q hq D
    (AddressWindow.field point (i * widthOf source a H Cpad hpad r oracle q hq D)
      (wrequest source a H Cpad hpad r oracle q hq).arity)
    (AddressWindow.field point (i * widthOf source a H Cpad hpad r oracle q hq D +
      (wrequest source a H Cpad hpad r oracle q hq).arity)
      (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
    (AddressWindow.read point (i * widthOf source a H Cpad hpad r oracle q hq D +
      (wrequest source a H Cpad hpad r oracle q hq).arity + capOf source a H Cpad hpad r oracle q hq D))
    (capOf source a H Cpad hpad r oracle q hq D - (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits)
    (by show _ = capOf source a H Cpad hpad r oracle q hq D; omega)
  unfold CaseTwoFold.roundCost SliceFrame.budget
  omega

/-- The fold's cost bound over `c` rounds. -/
theorem foldCost_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    {N : ℕ} (point : BitInput N) (c : ℕ) (hfit : c * widthOf source a H Cpad hpad r oracle q hq D ≤ N) :
    foldCost source a H Cpad hpad r oracle q hq D point c ≤
      2 * q + 5 + (12 * N + 11) + 1 + blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) := by
  unfold foldCost
  refine Finset.sup_le fun i hi => ?_
  have hic := Finset.mem_range.1 hi
  exact roundCost_le source a H Cpad hpad r oracle q hq degree D hcoeff horacle hcb point i
    ((Nat.mul_le_mul_right _ (show i + 1 ≤ c by omega)).trans hfit)

/-- **The fold's capacity need is within the block envelope** plus linear terms in `Env(N)` and `N`. -/
theorem foldNeed_le (hcoeff : H.coefficient ≤ Cpad)
    (horacle : oracle.size ≤ oracleSizeBound degree
      (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))
    (hcb : (a.output (wrequest source a H Cpad hpad r oracle q hq)).clauseBits ≤
      capOf source a H Cpad hpad r oracle q hq D)
    {N : ℕ} (point : BitInput N) (c : ℕ) (hfit : c * widthOf source a H Cpad hpad r oracle q hq D ≤ N)
    (hqN : q ≤ N) :
    foldNeed source a H Cpad hpad r oracle q hq D point c ≤
      4 * WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + 20 * N + 40 +
        blockEnv a D (WholeBudgetHierarchy.envelope source a H Cpad degree r.1 + q) := by
  have hbd := WholeBudgetHierarchy.bounds source a H Cpad degree hcoeff hpad r oracle horacle
  have hfc := foldCost_le source a H Cpad hpad r oracle q hq degree D hcoeff horacle hcb point c hfit
  have h1 := hbd.2.2.1
  have h2 := hbd.2.2.2
  unfold foldNeed
  simp only [RepairOrdinary.frame_length, List.length_ofFn]
  omega

end Fold

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoBudget
