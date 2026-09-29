import Proof.Wire_3_5.Recovery.CaseTwoPadGSource

/-! # The padded source at a guessed oracle is polynomial (P3:3653-3655, 3669-3671, G4)

Realizes, for the union machine's check of a guessed oracle, the cost half of "the union machine [...] checks the PCPP
of the substituted circuit of the guessed oracle" (P3:3669-3671) within the union's polynomial source work
("`C_clk = k + 2 > d_ver + 2`", P3:3653-3655): the step budget `obudgetG` of G3's machine is at most
`C·(N+1)^E·(q+1)^c + C·(cap+1)^3` whenever the guessed oracle's size is within `oracleSizeBound degree q`. The
exponents `E = c` depend only on the source, the PCPP algorithm and the oracle degree (not on the hierarchy or its
clock exponent); the coefficient `C` depends on the hierarchy and `Cpad`. No bound on the clock's bit length is
assumed: `natBitLength (H.time N) + 1 ≤ (H.coefficient + k + 4)·(N+1)` (`clock_le`).

Every term is charged by base's generic cost lemmas (`PCPPNativeHierarchySource.original_budget_bound`,
`parameter_bound`, `WholeBudgetHierarchy.request_size_bound`, `HierarchyStreamCost.budget_bound`,
`PCPPNativeResourceCost.descriptor_budget`, `cache_parameter`, `WholeBudget.request_source_bound`,
`PCPPNative.descriptor_length_bound`). Donors checked: the M26 `CaseTwoBudget` (`pbudget_le`,
`rsource_le`, `blockEnv_poly`; its oracle hypothesis is at the native width `R`, the guessed oracle's is at `q ≥ R`,
so the two block lemmas are restated here over an arbitrary envelope `Env`); base `WholeBudgetHierarchy.bounds`
(same restriction to width `R`, not usable).

Paper quantity of the main type (`obudgetG_poly`): the polynomial step bound of the guessed-oracle PCPP check. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.PaddedRunnerBudgetClosure

noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm)

/-! ## The padded source's envelope as a polynomial (`srcM`, restated) -/

def gcapM (M : ℕ) : ℕ := PCPPQueryCachedBounds.capacity a (3 * M + 2 * a.minimumArity)
def gfuelM (M : ℕ) : ℕ := M + 1 + (6 * M + 20)
/-- The padded descriptor and request-source costs at a size bound `M`. -/
def gsrcM (M : ℕ) : ℕ :=
  (2 * (6 * gfuelM M + 8 + (9216 * (a.minimumArity + 2 * M + 1) ^ 2 + 2 * gfuelM M + 3)) +
      4 * (39 * (3 * M + 2 * a.minimumArity + 5) ^ 2) + 7) + 1 +
    (2 * (PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) * (2 * M + 1)) ^ PCPPSourceCache.totalDegree a) +
      8 * (3 * gcapM a M + 3) + 16)

theorem gcapacity_mono {m n : ℕ} (h : m ≤ n) :
    PCPPQueryCachedBounds.capacity a m ≤ PCPPQueryCachedBounds.capacity a n := by
  unfold PCPPQueryCachedBounds.capacity
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem gsrcM_mono : Monotone (gsrcM a) := by
  intro m n h
  have hf : gfuelM m ≤ gfuelM n := by unfold gfuelM; omega
  have hc : gcapM a m ≤ gcapM a n := gcapacity_mono a (by omega)
  unfold gsrcM
  gcongr

theorem gsrcM_poly {f : ℕ → ℕ} (hf : SourcePoly f) : SourcePoly (fun x => gsrcM a (f x)) := by
  have hc (v : ℕ) := polyDominated_const (measureOf := (fun n : ℕ => n)) v
  have hcap : SourcePoly (fun x => gcapM a (f x)) :=
    ((sourcePoly_pow (((hf.const_mul 3).add (hc (2 * a.minimumArity))).add (hc 1))
      (PCPPQueryCachedBounds.degree a)).const_mul (PCPPQueryCachedBounds.coefficient a)).mono (fun _ => le_of_eq rfl)
  have hfuel : SourcePoly (fun x => gfuelM (f x)) :=
    (((hf.add (hc 1)).add ((hf.const_mul 6).add (hc 20)))).mono (fun _ => le_of_eq rfl)
  have hA : SourcePoly (fun x => 2 * (6 * gfuelM (f x) + 8 + (9216 * (a.minimumArity + 2 * f x + 1) ^ 2 +
      2 * gfuelM (f x) + 3))) :=
    ((((hfuel.const_mul 6).add (hc 8)).add ((((sourcePoly_pow (((hc a.minimumArity).add (hf.const_mul 2)).add (hc 1))
      2).const_mul 9216).add (hfuel.const_mul 2)).add (hc 3))).const_mul 2)
  have hB : SourcePoly (fun x => 4 * (39 * (3 * f x + 2 * a.minimumArity + 5) ^ 2)) :=
    ((sourcePoly_pow (((hf.const_mul 3).add (hc (2 * a.minimumArity))).add (hc 5)) 2).const_mul 39).const_mul 4
  have hR : SourcePoly (fun x => 2 * (PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) * (2 * f x + 1)) ^
      PCPPSourceCache.totalDegree a) + 8 * (3 * gcapM a (f x) + 3) + 16) :=
    ((((sourcePoly_pow (((hf.const_mul 2).add (hc 1)).const_mul (2 * a.minimumArity + 5))
      (PCPPSourceCache.totalDegree a)).const_mul (PCPPSourceCache.coefficient a)).const_mul 2).add
      (((hcap.const_mul 3).add (hc 3)).const_mul 8)).add (hc 16)
  exact ((((hA.add hB).add (hc 7)).add (hc 1)).add hR).mono (fun _ => le_of_eq rfl)

/-! ## The padded source over an arbitrary envelope -/

section Block
variable {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hpad : k + 3 ≤ Cpad) (r : InputRequest)
  (oracle : BooleanCircuit
    (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2))

/-- The native producer writes its node stream within its fuel (`stream_le`). -/
theorem gstream_le (hcoeff : H.coefficient ≤ Cpad) :
    ((PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle := by
  obtain ⟨native, hn, ns, _, head, _⟩ := PCPPNativeHierarchyNodes.original_run source H Cpad hcoeff hpad r oracle
  have hlen := SelectiveReset.prefix_head (prefix_of_run _ _ _ native hn).1 (PCPPNativeHierarchyNodes.slots source k 177)
  rw [head] at hlen
  change ((PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).nodes.flatMap PCPPRequestNodeSchema.native).length ≤ 0 + native.steps at hlen
  omega

variable (q : ℕ) (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
  (Env : ℕ)

/-- The padded descriptor and its framed word, over an envelope `Env` of the native fuel and circuit size. -/
theorem gpbudget_le (hcoeff : H.coefficient ≤ Cpad)
    (hnodes : PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle ≤ Env)
    (hcs : (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).size ≤ Env) :
    CaseTwoPadSource.pbudget source a H Cpad hpad r oracle q hq ≤
      2 * (6 * gfuelM (Env + q) + 8 + (9216 * (a.minimumArity + 2 * (Env + q) + 1) ^ 2 + 2 * gfuelM (Env + q) + 3)) +
      4 * (39 * (3 * (Env + q) + 2 * a.minimumArity + 5) ^ 2) + 7 := by
  unfold CaseTwoPadSource.pbudget PCPPNativeClauseDescriptorConsumer.budget
  set M := Env + q with hM
  set c := PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
    oracle with hc
  have hsz : (castCircuit hq c).size = c.size := castCircuit_size hq c
  have hstream : ((castCircuit hq c).nodes.flatMap PCPPRequestNodeSchema.native).length ≤
      PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle := by
    rw [CaseTwoPad.stream_cast]; exact gstream_le source H Cpad hpad r oracle hcoeff
  set fuel := PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle + 1 + CaseTwoPad.widthFixCost q with hfuel
  have hfM : fuel ≤ gfuelM M := by simp only [hfuel, gfuelM, CaseTwoPad.widthFixCost, hM]; omega
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

/-- The padded request's source call, over an envelope `Env` of the circuit size. -/
theorem grsource_le
    (hcs : (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).size ≤ Env) :
    RequestSource.budget a (PCPPRequestBoundary.request a (castCircuit hq
      (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle))) ≤
      2 * (PCPPSourceCache.coefficient a * ((2 * a.minimumArity + 5) * (2 * (Env + q) + 1)) ^
        PCPPSourceCache.totalDegree a) + 8 * (3 * gcapM a (Env + q) + 3) + 16 := by
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
  have hmeas : WholeBudget.measure a req ≤ gcapM a M := gcapacity_mono a (by omega)
  have hin : (pcppInput req).length ≤ 3 * WholeBudget.measure a req + 3 := (WholeBudget.components a req).2.2.1
  omega

/-- **The padded source over an envelope**: its budget is at most `gsrcM (Env + q)`. -/
theorem gobudget_le (hcoeff : H.coefficient ≤ Cpad)
    (hnodes : PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle ≤ Env)
    (hcs : (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      oracle).size ≤ Env) :
    CaseTwoPadSource.obudget source a H Cpad hpad r oracle q hq ≤ gsrcM a (Env + q) := by
  have h1 := gpbudget_le source a H Cpad hpad r oracle q hq Env hcoeff hnodes hcs
  have h2 := grsource_le source a H Cpad hpad r oracle q hq Env hcs
  unfold CaseTwoPadSource.obudget gsrcM
  omega

end Block

/-! ## The clock's bit length -/

/-- The hierarchy clock's bit length is linear in the input length (coefficient `H.coefficient + k + 4`). -/
theorem clock_le {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (n : ℕ) :
    natBitLength (H.time n) + 1 ≤ (H.coefficient + k + 4) * (n + 1) := by
  have hc : H.coefficient ≤ 2 ^ H.coefficient := (Nat.lt_two_pow_self).le
  have hp : n ^ (k + 2) + 1 ≤ (n + 1) ^ (k + 2) := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by omega)
  have hq : (n + 1) ^ (k + 2) ≤ (2 ^ (n + 1)) ^ (k + 2) := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have h1 : H.time n ≤ 2 ^ (H.coefficient + (n + 1) * (k + 2)) := by
    rw [pow_add, pow_mul]
    exact Nat.mul_le_mul hc (hp.trans hq)
  have h2 : natBitLength (H.time n) ≤ H.coefficient + (n + 1) * (k + 2) + 1 := by
    unfold natBitLength
    have := Nat.log_mono_right (b := 2) h1
    rw [Nat.log_pow (by norm_num)] at this
    omega
  have e : (H.coefficient + k + 4) * (n + 1) = H.coefficient * (n + 1) + (n + 1) * (k + 2) + 2 * (n + 1) := by ring
  have h3 : H.coefficient ≤ H.coefficient * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [e]
  omega

/-! ## One polynomial in one scale -/

/-- The oracle degree's exponent `2^{oracleDepth G}`. -/
def gD (degree : ℕ) : ℕ := 2 ^ RecoveryScheduleEnvelope.oracleDepth degree
/-- The oracle parameter at scale `Y`. -/
def oPY (degree Y : ℕ) : ℕ := 2000 * Y ^ (2 * gD degree)
/-- The native/source constructor at scale `Y`. -/
def envA (degree Y : ℕ) : ℕ :=
  Y * Y ^ PCPPNativeHierarchySource.inputExponent source a * Y ^ PCPPNativeHierarchySource.logExponent source a *
    oPY degree Y ^ PCPPNativeHierarchySource.degree a
/-- The source parameter at scale `Y`. -/
def parP (degree Y : ℕ) : ℕ :=
  Y * Y ^ HierarchySourceCost.inputExponent source * Y ^ HierarchyStreamCost.logBase source * oPY degree Y
/-- The request size at scale `Y`. -/
def envB (degree Y : ℕ) : ℕ := (2 * a.minimumArity + 5) * (4098 * parP source degree Y ^ 3)
def envP (degree Y : ℕ) : ℕ := envA source a degree Y + envB source a degree Y
/-- The hierarchy word, the framings and the hierarchy stage at scale `Y`. -/
def stageP (degree Y : ℕ) : ℕ :=
  100 * Y + 16000 * Y ^ (2 * gD degree) +
    2 * Y ^ (1 + HierarchyStreamCost.inputExponent source + HierarchyStreamCost.logExponent source) + 100
/-- **The scale polynomial**: fixed by the source, the PCPP algorithm and the oracle degree. -/
def gP (degree Y : ℕ) : ℕ := stageP source degree Y + gsrcM a (envP source a degree Y + Y)

theorem gP_poly (degree : ℕ) : SourcePoly (fun Y => gP source a degree Y) := by
  have hc (v : ℕ) := polyDominated_const (measureOf := (fun n : ℕ => n)) v
  have hid : SourcePoly (fun Y : ℕ => Y) := sourcePoly_id
  have hpw (e : ℕ) : SourcePoly (fun Y : ℕ => Y ^ e) := sourcePoly_pow hid e
  have hoP : SourcePoly (fun Y => oPY degree Y) := ((hpw (2 * gD degree)).const_mul 2000).mono (fun _ => le_of_eq rfl)
  have hA : SourcePoly (fun Y => envA source a degree Y) :=
    (((hid.mul (hpw _)).mul (hpw _)).mul (sourcePoly_pow hoP _)).mono (fun _ => le_of_eq rfl)
  have hpar : SourcePoly (fun Y => parP source degree Y) :=
    (((hid.mul (hpw _)).mul (hpw _)).mul hoP).mono (fun _ => le_of_eq rfl)
  have hB : SourcePoly (fun Y => envB source a degree Y) :=
    (((sourcePoly_pow hpar 3).const_mul 4098).const_mul (2 * a.minimumArity + 5)).mono (fun _ => le_of_eq rfl)
  have hE : SourcePoly (fun Y => envP source a degree Y + Y) := ((hA.add hB).add hid).mono (fun _ => le_of_eq rfl)
  have hS : SourcePoly (fun Y => stageP source degree Y) :=
    ((((hid.const_mul 100).add ((hpw _).const_mul 16000)).add ((hpw _).const_mul 2)).add (hc 100)).mono
      (fun _ => le_of_eq rfl)
  exact (hS.add (gsrcM_poly a hE)).mono (fun _ => le_of_eq rfl)

/-- The oracle parameter and description length of `restrictHigh R O` at scale `Y`. -/
theorem oparam_le (R q : ℕ) (hRq : R ≤ q) (O : BooleanCircuit q) (Y D : ℕ) (hD : 1 ≤ D) (hY : 1 ≤ Y)
    (hQ : q + 1 ≤ Y) (hO : O.size ≤ Y ^ D) :
    PCPPNativeHierarchySource.oracleParameter (restrictHigh R O) ≤ 2000 * Y ^ (2 * D) ∧
      (PCPPNative.descriptor (restrictHigh R O)).length ≤ 1911 * Y ^ (2 * D) := by
  have hW : Y ≤ Y ^ D := Nat.le_self_pow (by omega) Y
  have hsq : (Y ^ D) ^ 2 = Y ^ (2 * D) := by rw [← pow_mul, mul_comm]
  have hW2 : Y ^ D ≤ (Y ^ D) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hd := PCPPNative.descriptor_length_bound (restrictHigh R O)
  rw [restrictHigh_size] at hd
  have h7 : R + O.size + 5 ≤ 7 * Y ^ D := by omega
  have h49 : (R + O.size + 5) ^ 2 ≤ 49 * (Y ^ D) ^ 2 := by
    calc (R + O.size + 5) ^ 2 ≤ (7 * Y ^ D) ^ 2 := Nat.pow_le_pow_left h7 2
      _ = 49 * (Y ^ D) ^ 2 := by ring
  rw [← hsq]
  refine ⟨?_, by omega⟩
  unfold PCPPNativeHierarchySource.oracleParameter
  rw [restrictHigh_size]
  omega

/-- The guessed-oracle budget at any scale `Y` dominating the input length, `q + 1`, the clock's bit length, the
hierarchy's coefficients and the oracle size. -/
theorem obudgetG_le_gP {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad degree : ℕ)
    (hcoeff : H.coefficient ≤ Cpad) (hpad : k + 3 ≤ Cpad) (r : InputRequest) (q : ℕ)
    (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
    (O : BooleanCircuit q) (cap Y : ℕ) (hY1 : 1 ≤ Y) (hN : r.1 + 1 ≤ Y) (hQ : q + 1 ≤ Y)
    (hclk : natBitLength (H.time r.1) + 1 ≤ Y) (hc1 : PCPPNativeHierarchySource.coefficient source a H Cpad ≤ Y)
    (hc2 : HierarchyStreamCost.sizeCoefficient source H Cpad + 1 ≤ Y)
    (hc3 : HierarchyStreamCost.coefficient source H Cpad ≤ Y) (hO : O.size ≤ Y ^ gD degree) :
    obudgetG source a H Cpad hpad r hq O cap ≤
      gP source a degree Y + (2 * cap + 4 + (6000 * (cap + 12) ^ 3 + 2)) := by
  have hD : 1 ≤ gD degree := Nat.one_le_two_pow
  obtain ⟨hoP, hdesc⟩ := oparam_le _ q hq O Y (gD degree) hD hY1 hQ hO
  -- the native/source constructor
  have hsrcB := PCPPNativeHierarchySource.original_budget_bound source a H Cpad hcoeff hpad r
    (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)
  have hEA : PCPPNativeHierarchySource.envelope source a H Cpad r
      (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
        O) ≤ envA source a degree Y := by
    unfold PCPPNativeHierarchySource.envelope envA
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc1 (Nat.pow_le_pow_left hN _)) (Nat.pow_le_pow_left hclk _))
      (Nat.pow_le_pow_left hoP _)
  unfold PCPPNativeHierarchySource.originalBudget PCPPNativeClauseDescriptorConsumer.sourceBudget
    PCPPNativeSource.budget PCPPNativeClauseDescriptorConsumer.budget at hsrcB
  -- the native circuit's size
  have hpar := PCPPNativeHierarchySource.parameter_bound source H Cpad hcoeff hpad r
    (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)
  have hpar' := hpar.trans (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hc2 (Nat.pow_le_pow_left hN _))
    (Nat.pow_le_pow_left hclk _)) hoP)
  have hreqsz := WholeBudgetHierarchy.request_size_bound source a H Cpad hpad r
    (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)
  dsimp only at hreqsz
  have hcsz := PCPPRequestBoundary.request_size a (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad
    (VerifierEncoding.code H.verifier) r.2 hpad
    (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O))
  have hEB : (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad
      (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)
        O)).size ≤ envB source a degree Y := by
    have h3 := Nat.mul_le_mul_left (2 * a.minimumArity + 5) (Nat.mul_le_mul_left 4098 (Nat.pow_le_pow_left hpar' 3))
    have hm := le_max_left (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier)
      r.2 hpad (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) r.2) O)).size
      (PCPPRequestBoundary.domain a (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad
        (VerifierEncoding.code H.verifier) r.2))
    unfold envB parP oPY
    omega
  -- the padded source at the restricted oracle
  have hob := gobudget_le source a H Cpad hpad r
    (restrictHigh (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2) O)
    q hq (envP source a degree Y) hcoeff (by unfold envP; omega) (by unfold envP; omega)
  have hob' := gsrcM_mono a (show envP source a degree Y + q ≤ envP source a degree Y + Y by omega)
  -- the stages
  have hhier : (HierarchySourceInput.hierarchyInput H r).length ≤ 4 * Y := by
    have hbits := PCPPQueryBounds.bits_le (H.time r.1)
    simp only [HierarchySourceInput.hierarchyInput, List.length_append, frame_length, List.length_ofFn]
    omega
  have hPHB : PCPPNativeHierarchy.budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)
      (H.time r.1).bits [] = HierarchyStreamCost.framedBudget source H Cpad r + 6 := by
    rw [PCPPNativeHierarchy.original_budget source H Cpad hpad r]
    simp
  have hFB := HierarchyStreamCost.budget_bound source H Cpad hcoeff hpad r
  have hFB' : HierarchyStreamCost.framedBudget source H Cpad r ≤
      Y ^ (1 + HierarchyStreamCost.inputExponent source + HierarchyStreamCost.logExponent source) := by
    refine hFB.trans ?_
    rw [pow_add, pow_add, pow_one]
    exact Nat.mul_le_mul (Nat.mul_le_mul hc3 (Nat.pow_le_pow_left hN _)) (Nat.pow_le_pow_left hclk _)
  simp only [obudgetG, pbudgetG, gP, stageP, CompoundInput.budget, RecoveryPCPFormulaResumeSearchPair.budget,
    List.length_nil]
  omega

/-! ## The bound -/

/-- The hierarchy-dependent scale coefficient. -/
def gK {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) : ℕ :=
  PCPPNativeHierarchySource.coefficient source a H Cpad + HierarchyStreamCost.sizeCoefficient source H Cpad +
    HierarchyStreamCost.coefficient source H Cpad + H.coefficient + k + 5

/-- **G4: the guessed-oracle PCPP check is polynomial.** The exponents `E = c` depend only on the source, the PCPP
algorithm and the oracle degree; the coefficient `C` on the hierarchy and `Cpad`. -/
theorem obudgetG_poly (degree : ℕ) :
    ∃ E c : ℕ, ∀ {k : ℕ} (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ), H.coefficient ≤ Cpad →
      ∀ hpad : k + 3 ≤ Cpad, ∃ C : ℕ, ∀ (r : InputRequest) (q : ℕ)
        (hq : PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 ≤ q)
        (O : BooleanCircuit q) (cap : ℕ), O.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree q →
        obudgetG source a H Cpad hpad r hq O cap ≤ C * (r.1 + 1) ^ E * (q + 1) ^ c + C * (cap + 1) ^ 3 := by
  obtain ⟨dp, Cp, hCp⟩ := gP_poly source a degree
  refine ⟨dp, dp, fun {k} H Cpad hcoeff hpad => ⟨Cp * (gK source a H Cpad + 1) ^ dp + 10368006,
    fun r q hq O cap hO => ?_⟩⟩
  have hK : H.coefficient + k + 4 + 1 ≤ gK source a H Cpad ∧
      PCPPNativeHierarchySource.coefficient source a H Cpad ≤ gK source a H Cpad ∧
      HierarchyStreamCost.sizeCoefficient source H Cpad + 1 ≤ gK source a H Cpad ∧
      HierarchyStreamCost.coefficient source H Cpad ≤ gK source a H Cpad := by
    unfold gK; omega
  have hX : 1 ≤ (r.1 + 1) * (q + 1) := Nat.mul_pos (by omega) (by omega)
  have hNX : r.1 + 1 ≤ (r.1 + 1) * (q + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hQX : q + 1 ≤ (r.1 + 1) * (q + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have hXY : (r.1 + 1) * (q + 1) ≤ gK source a H Cpad * ((r.1 + 1) * (q + 1)) := Nat.le_mul_of_pos_left _ (by omega)
  have hKY : gK source a H Cpad ≤ gK source a H Cpad * ((r.1 + 1) * (q + 1)) := Nat.le_mul_of_pos_right _ hX
  have hclkY : natBitLength (H.time r.1) + 1 ≤ gK source a H Cpad * ((r.1 + 1) * (q + 1)) :=
    (clock_le H r.1).trans (Nat.mul_le_mul (by omega) hNX)
  have hOs : O.size ≤ (gK source a H Cpad * ((r.1 + 1) * (q + 1))) ^ gD degree := by
    have hb := PolynomialClock.pairIter_add_one_le_pow (RecoveryScheduleEnvelope.oracleDepth degree) q
    change O.size ≤ PolynomialClock.pairIter (RecoveryScheduleEnvelope.oracleDepth degree) q at hO
    have hp : (q + 1) ^ gD degree ≤ (gK source a H Cpad * ((r.1 + 1) * (q + 1))) ^ gD degree :=
      Nat.pow_le_pow_left (hQX.trans hXY) _
    unfold gD at hp ⊢
    omega
  have hmain := obudgetG_le_gP source a H Cpad degree hcoeff hpad r q hq O cap
    (gK source a H Cpad * ((r.1 + 1) * (q + 1))) (by omega) (hNX.trans hXY) (hQX.trans hXY) hclkY (by omega)
    (by omega) (by omega) hOs
  have hPB : gP source a degree (gK source a H Cpad * ((r.1 + 1) * (q + 1))) ≤
      Cp * (gK source a H Cpad * ((r.1 + 1) * (q + 1)) + 1) ^ dp := hCp _
  have hpow : (gK source a H Cpad * ((r.1 + 1) * (q + 1)) + 1) ^ dp ≤
      (gK source a H Cpad + 1) ^ dp * ((r.1 + 1) ^ dp * (q + 1) ^ dp) := by
    calc (gK source a H Cpad * ((r.1 + 1) * (q + 1)) + 1) ^ dp
        ≤ ((gK source a H Cpad + 1) * ((r.1 + 1) * (q + 1))) ^ dp :=
          Nat.pow_le_pow_left (by rw [Nat.add_one_mul (gK source a H Cpad) ((r.1 + 1) * (q + 1))]; omega) _
      _ = (gK source a H Cpad + 1) ^ dp * ((r.1 + 1) ^ dp * (q + 1) ^ dp) := by rw [mul_pow, mul_pow]
  have hcap3 : 2 * cap + 4 + (6000 * (cap + 12) ^ 3 + 2) ≤ 10368006 * (cap + 1) ^ 3 := by
    have h12 : (cap + 12) ^ 3 ≤ 1728 * (cap + 1) ^ 3 := by
      calc (cap + 12) ^ 3 ≤ (12 * (cap + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = 1728 * (cap + 1) ^ 3 := by ring
    have h1 : cap + 1 ≤ (cap + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hfin : Cp * (gK source a H Cpad * ((r.1 + 1) * (q + 1)) + 1) ^ dp ≤
      (Cp * (gK source a H Cpad + 1) ^ dp + 10368006) * (r.1 + 1) ^ dp * (q + 1) ^ dp := by
    calc Cp * (gK source a H Cpad * ((r.1 + 1) * (q + 1)) + 1) ^ dp
        ≤ Cp * ((gK source a H Cpad + 1) ^ dp * ((r.1 + 1) ^ dp * (q + 1) ^ dp)) := Nat.mul_le_mul_left _ hpow
      _ = Cp * (gK source a H Cpad + 1) ^ dp * ((r.1 + 1) ^ dp * (q + 1) ^ dp) := (Nat.mul_assoc _ _ _).symm
      _ ≤ (Cp * (gK source a H Cpad + 1) ^ dp + 10368006) * ((r.1 + 1) ^ dp * (q + 1) ^ dp) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (Cp * (gK source a H Cpad + 1) ^ dp + 10368006) * (r.1 + 1) ^ dp * (q + 1) ^ dp :=
          (Nat.mul_assoc _ _ _).symm
  have hcapfin : 10368006 * (cap + 1) ^ 3 ≤ (Cp * (gK source a H Cpad + 1) ^ dp + 10368006) * (cap + 1) ^ 3 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

end

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
