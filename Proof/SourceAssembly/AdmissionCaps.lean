import Proof.SourceAssembly.AdmissionSmall
import Proof.CaseAnalysis.FiveRowCaps
import Proof.MachineModel.ClosureCompactCacheCost

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.CloseoutRawRows (sourceChildBound)
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.RepairSource.CloseoutRawRows (symmetric_occurrences_description threshold_occurrences_description)
open NearCubicWires.SupplierEstimator
open NearCubicWires.P1Closure NearCubicWires.RepairOrdinary

noncomputable section

/-! ## 1. Children and the source cache radix `beta` -/

/-- A pool gate of description `≤ D` has an exact child list of at most `sourceChildBound a D` bytes. -/
theorem children_bytes (a : DecompositionAlgorithm) {q : ℕ} (g : SupportedNormalizedGate q) (D : ℕ)
    (hd : g.descriptionBits ≤ D) :
    (exactListWord (ExtDecompositionBatch.children a g)).length ≤ sourceChildBound a D := by
  have hb := CloseoutRawRows.strict_gate_bits g.gate
  have hparam : q + (CompilerSemantics.nonStrictAsStrict g.gate).encodingBits + 1 ≤ D + 2 := by
    unfold SupportedNormalizedGate.descriptionBits at hd
    omega
  refine (RepairOrdinary.DecompositionSource.output_length a _).trans ?_
  unfold RepairOrdinary.DecompositionSource.sourceBudget sourceChildBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hparam a.degree)

theorem exactListWord_flatMap_le {n : ℕ} {α : Type} (xs : List α) (f : α → List (ExactThresholdGate n))
    (B : ℕ) (h : ∀ x ∈ xs, (exactListWord (f x)).length ≤ B) :
    (exactListWord (xs.flatMap f)).length ≤ 2*(xs.flatMap f).length + 3 + xs.length*B := by
  have hn := natWord_le (xs.flatMap f).length
  have hbody : ((xs.flatMap f).flatMap exactWord).length ≤ xs.length*B := by
    rw [List.flatMap_assoc]
    apply flatMap_le
    intro x hx
    have := h x hx
    unfold exactListWord at this
    simp only [List.length_append] at this
    omega
  unfold exactListWord
  simp only [List.length_append]
  omega

theorem pool_desc {q : ℕ} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (cap : ℕ)
    (hdesc : ∀ i : Fin occ.length, (occ.get i).descriptionBits ≤ cap) :
    ∀ g ∈ CloseoutRowsUniversal.pool live occ, g.descriptionBits ≤ (cap+3)^2 := by
  intro g hg
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  exact CloseoutRowsUniversal.pool_description live occ cap hdesc i

/-- `beta = CompactBounds.radix` is polynomial: `≤ 3*(2|occ|)*sourceChildBound a ((cap+3)^2) + 4`. -/
theorem beta_le (a : DecompositionAlgorithm) {q : ℕ} (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (cap : ℕ)
    (hdesc : ∀ i : Fin occ.length, (occ.get i).descriptionBits ≤ cap) :
    CompactBounds.radix a live occ ≤ 3*(2*occ.length)*sourceChildBound a ((cap+3)^2) + 4 := by
  have hpd := pool_desc live occ cap hdesc
  set S := sourceChildBound a ((cap+3)^2)
  have hbytes : ∀ g ∈ CloseoutRowsUniversal.pool live occ,
      (exactListWord (ExtDecompositionBatch.children a g)).length ≤ S :=
    fun g hg => children_bytes a g _ (hpd g hg)
  have hlen : (C10SupplierRowInput.childList a live occ).length ≤ 2*occ.length*S := by
    have h := GS_length_le a (CloseoutRowsUniversal.pool live occ) S (fun g hg =>
      (RepairOrdinary.DecompositionSource.children_le_output _).trans (hbytes g hg))
    rw [CloseoutRowsUniversal.pool_length] at h
    exact h
  have hw := exactListWord_flatMap_le (CloseoutRowsUniversal.pool live occ)
    (ExtDecompositionBatch.children a) S hbytes
  rw [CloseoutRowsUniversal.pool_length] at hw
  unfold CompactBounds.radix
  change (exactListWord (ExtDecompositionBatch.GS a (CloseoutRowsUniversal.pool live occ))).length + 1 ≤ _
  unfold ExtDecompositionBatch.GS
  change _ ≤ 2*(C10SupplierRowInput.childList a live occ).length + 3 + 2*occ.length*S at hw
  have e : 3*(2*occ.length)*S = 2*(2*occ.length*S) + 2*occ.length*S := by ring
  omega

/-! ## 2. The replicated pool and the layout-dependent sizes -/

section
variable (a : DecompositionAlgorithm) {q L : ℕ} (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g)

theorem packetsPool_le :
    (Packets.pool a F g).length + 1 ≤
      2*2^(Packets.live F).card*(CompactBounds.radix a (Packets.live F) F.occurrences + 1) := by
  unfold Packets.pool
  rw [BinaryPool.pool_length, C10SupplierRowInput.pool_length, C10SupplierRowInput.liveList_length]
  have hc := RepairOrdinary.DecompositionSource.children_le_output
    (C10SupplierRowInput.childList a (Packets.live F) F.occurrences)
  have hpow : 1 ≤ 2^(Packets.live F).card := Nat.one_le_two_pow
  unfold CompactBounds.radix
  have h := Nat.mul_le_mul_left (2^(Packets.live F).card) hc
  nlinarith

theorem residual_arity_le : (Packets.residual F + 1)/2 + Packets.residual F/2 ≤ q := by
  unfold Packets.residual
  omega

theorem packetsPool_bytes :
    (exactListWord (Packets.pool a F g)).length ≤
      4*(2*2^(Packets.live F).card*(CompactBounds.radix a (Packets.live F) F.occurrences + 1))*(q+1)*
        (CompactBounds.radix a (Packets.live F) F.occurrences + 1) := by
  have h := @CompactCacheCost.cache_bytes _ (Packets.pool a F g)
    (BinaryRequest.radix a (Packets.live F) F.occurrences (Packets.residual F) g.arity 0)
  have hp := packetsPool_le a F g
  have hr := residual_arity_le F
  exact h.trans (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 4 hp) (by omega)) le_rfl)

theorem nativeWidth_le :
    @ExtIncidence.P1CompactNativeWidth.width _ (Packets.pool a F g) (Packets.radix a F g layout)
        ((Packets.live F).card+1) ≤
      CompactBounds.radix a (Packets.live F) F.occurrences*(layout.degree*((Packets.live F).card+1)) +
        ((Packets.live F).card+1) := by
  letI := Packets.radix a F g layout
  change P1Radix.bits (Packets.pool a F g)*(P1Radix.effectiveDegree (Packets.pool a F g)*
    ((Packets.live F).card+1)) + ((Packets.live F).card+1) ≤ _
  have he : P1Radix.effectiveDegree (Packets.pool a F g) ≤ layout.degree := Nat.min_le_left _ _
  have hb : P1Radix.bits (Packets.pool a F g) = CompactBounds.radix a (Packets.live F) F.occurrences := rfl
  rw [hb]
  gcongr

end

/-! ## 3. Header envelope, stream and precision sizes -/

section
variable (a : DecompositionAlgorithm) {q L : ℕ} (F : Packets.Family q L) (g : Packets.Geometry F)
  (layout : Packets.Layout a F g)

theorem precision_le (hdw : layout.degree ≤ q)
    (hKq : (Packets.live F).card ≤ q) :
    RCFive.NativeResources.precision a F g layout ≤
      CompactBounds.radix a (Packets.live F) F.occurrences*(q*(q+1)) + (q+1) := by
  unfold RCFive.NativeResources.precision RCFive.NativeResources.beta RCFive.NativeResources.degree
  have hd : min layout.degree (Packets.pool a F g).length ≤ q := (Nat.min_le_left _ _).trans hdw
  have h1 : min layout.degree (Packets.pool a F g).length*((Packets.live F).card+1) ≤ q*(q+1) :=
    Nat.mul_le_mul hd (by omega)
  have h2 := Nat.mul_le_mul_left (CompactBounds.radix a (Packets.live F) F.occurrences) h1
  omega

/-- Pure arithmetic for the envelope. -/
theorem env_arith (res pool bytes β width K w raw q : ℕ) (hres : res ≤ q)
    (hpool : pool + 1 ≤ 2*2^K*(β+1)) (hbytes : bytes ≤ 4*(2*2^K*(β+1))*(q+1)*(β+1))
    (hwidth : width ≤ β*(q*(q+1)) + (q+1)) (hK : K ≤ q) (hw : w ≤ q)
    (hraw : raw ≤ 2^w*(q*(2*2^K*(β+1))+2)+1) :
    res + pool + bytes + β + width + (K+1) + w + raw + 2^K + 1 ≤
      64*(2^(w+K)*((β+1)^2*(q+1)^3)) := by
  generalize hX : 2^(w+K) = X
  have hXK : 2^w*2^K = X := by rw [← hX, pow_add]
  have hKX : 2^K ≤ X := by rw [← hX]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hwX : 2^w ≤ X := by rw [← hX]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hX1 : 1 ≤ X := by rw [← hX]; exact Nat.one_le_two_pow
  have hq3 : q+1 ≤ (q+1)^3 := Nat.le_self_pow (by norm_num) _
  have hb2 : β+1 ≤ (β+1)^2 := Nat.le_self_pow (by norm_num) _
  have hq31 : 1 ≤ (q+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hb21 : 1 ≤ (β+1)^2 := Nat.one_le_pow _ _ (by omega)
  generalize hB : (β+1)^2 = B at hb2 hb21 ⊢
  generalize hQ : (q+1)^3 = Q at hq3 hq31 ⊢
  -- `P = B*Q` and its small multiples
  have hP_q : q+1 ≤ B*Q := (hq3.trans (Nat.le_mul_of_pos_left _ hb21))
  have hP_b : β+1 ≤ B*Q := (hb2.trans (Nat.le_mul_of_pos_right _ hq31))
  have hP_bq : (β+1)*(β+1)*(q+1) ≤ B*Q := by
    have : (β+1)*(β+1) = B := by rw [← hB]; ring
    rw [this]; exact Nat.mul_le_mul_left _ hq3
  have hP_bqq : β*(q*(q+1)) ≤ B*Q := by
    have h1 : β ≤ B := by omega
    have h2 : q*(q+1) ≤ Q := by
      have : q*(q+1) ≤ (q+1)*(q+1) := Nat.mul_le_mul_right _ (by omega)
      have : (q+1)*(q+1) ≤ (q+1)^3 := by nlinarith
      omega
    exact Nat.mul_le_mul h1 h2
  have hP_qb : q*(β+1) ≤ B*Q := by
    have h1 : q ≤ Q := by omega
    have h2 : β+1 ≤ B := hb2
    rw [Nat.mul_comm]; exact Nat.mul_le_mul h2 h1
  have hP1 : 1 ≤ B*Q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hY : B*Q ≤ X*(B*Q) := Nat.le_mul_of_pos_left _ hX1
  have t2 : 2^K*(β+1) ≤ X*(B*Q) := Nat.mul_le_mul hKX hP_b
  have e2 : 2*2^K*(β+1) = 2*(2^K*(β+1)) := by ring
  have t3 : 2^K*((β+1)*(β+1)*(q+1)) ≤ X*(B*Q) := Nat.mul_le_mul hKX hP_bq
  have e3 : 4*(2*2^K*(β+1))*(q+1)*(β+1) = 8*(2^K*((β+1)*(β+1)*(q+1))) := by ring
  have t8 : X*(q*(β+1)) ≤ X*(B*Q) := Nat.mul_le_mul_left _ hP_qb
  have e8 : 2^w*(q*(2*2^K*(β+1))+2) = 2*(X*(q*(β+1))) + 2*2^w := by rw [← hXK]; ring
  have t9 : 2^w ≤ X*(B*Q) := hwX.trans (Nat.le_mul_of_pos_right _ hP1)
  have t10 : 2^K ≤ X*(B*Q) := hKX.trans (Nat.le_mul_of_pos_right _ hP1)
  omega

/-- The Header envelope is at most `2^(w+K)` times a fixed polynomial of `beta` and `q`. -/
theorem envelope_le (hdw : layout.degree ≤ q) (hwq : layout.w ≤ q)
    (hKq : (Packets.live F).card ≤ q) :
    RCFive.RowCaps.envelope a F g layout + 1 ≤
      64*(2^(layout.w + (Packets.live F).card) *
        ((CompactBounds.radix a (Packets.live F) F.occurrences + 1)^2*(q+1)^3)) := by
  have hpool := packetsPool_le a F g
  have hraw : RCFive.RowCaps.rawCap a F g layout ≤
      2^layout.w*(q*(2*2^(Packets.live F).card*
        (CompactBounds.radix a (Packets.live F) F.occurrences + 1))+2)+1 := by
    unfold RCFive.RowCaps.rawCap
    have h1 : layout.degree*((Packets.pool a F g).length+1) ≤
        q*(2*2^(Packets.live F).card*(CompactBounds.radix a (Packets.live F) F.occurrences + 1)) :=
      Nat.mul_le_mul hdw hpool
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right h1 2)) 1
  have hwidth : @ExtIncidence.P1CompactNativeWidth.width _ (Packets.pool a F g) (Packets.radix a F g layout)
        ((Packets.live F).card+1) ≤
      CompactBounds.radix a (Packets.live F) F.occurrences*(q*(q+1)) + (q+1) := by
    have h := nativeWidth_le a F g layout
    have h1 : layout.degree*((Packets.live F).card+1) ≤ q*(q+1) := Nat.mul_le_mul hdw (by omega)
    have h2 := Nat.mul_le_mul_left (CompactBounds.radix a (Packets.live F) F.occurrences) h1
    omega
  have h := env_arith ((Packets.residual F+1)/2 + Packets.residual F/2) (Packets.pool a F g).length
    (exactListWord (Packets.pool a F g)).length (CompactBounds.radix a (Packets.live F) F.occurrences)
    (@ExtIncidence.P1CompactNativeWidth.width _ (Packets.pool a F g) (Packets.radix a F g layout)
        ((Packets.live F).card+1))
    (Packets.live F).card layout.w (RCFive.RowCaps.rawCap a F g layout) q (residual_arity_le F)
    hpool (packetsPool_bytes a F g) hwidth hKq hwq hraw
  unfold RCFive.RowCaps.envelope
  exact h

theorem headerCap_le (hdw : layout.degree ≤ q) (hwq : layout.w ≤ q)
    (hKq : (Packets.live F).card ≤ q) :
    RCFive.RowCaps.headerCap a F g layout ≤
      2^119*(64*((CompactBounds.radix a (Packets.live F) F.occurrences + 1)^2*(q+1)^3))^22 *
        2^(22*(layout.w + (Packets.live F).card) + layout.w*((Packets.live F).card+2)) := by
  have he := envelope_le a F g layout hdw hwq hKq
  unfold RCFive.RowCaps.headerCap
  generalize (CompactBounds.radix a (Packets.live F) F.occurrences + 1)^2*(q+1)^3 = P at he ⊢
  generalize RCFive.RowCaps.envelope a F g layout = E at he ⊢
  have h1 : (E + 1)^22 ≤ (64*P)^22*2^(22*(layout.w + (Packets.live F).card)) := by
    calc (E + 1)^22 ≤ (64*(2^(layout.w + (Packets.live F).card)*P))^22 := Nat.pow_le_pow_left he 22
      _ = (64*P*2^(layout.w + (Packets.live F).card))^22 := by rw [Nat.mul_comm (2^_) P, Nat.mul_assoc]
      _ = (64*P)^22*2^(22*(layout.w + (Packets.live F).card)) := by
          rw [mul_pow (64*P), ← pow_mul, Nat.mul_comm (layout.w + _) 22]
  rw [pow_add]
  calc 2^119*(E + 1)^22*2^(layout.w*((Packets.live F).card+2))
      ≤ 2^119*((64*P)^22*2^(22*(layout.w + (Packets.live F).card)))*
          2^(layout.w*((Packets.live F).card+2)) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    _ = 2^119*(64*P)^22*(2^(22*(layout.w + (Packets.live F).card))*
          2^(layout.w*((Packets.live F).card+2))) := by
        rw [Nat.mul_assoc (2^119), Nat.mul_assoc ((64*P)^22), Nat.mul_assoc]

theorem streamCap_le (hdw : layout.degree ≤ q)
    (hKq : (Packets.live F).card ≤ q) :
    RCFive.NativeResources.streamCap a F g layout ≤
      2^(2*((Packets.live F).card + layout.w*((Packets.live F).card+2))) *
        ((q+2)*(2*(CompactBounds.radix a (Packets.live F) F.occurrences*(q*(q+1)) + (q+1))+3)) := by
  have hp := precision_le a F g layout hdw hKq
  have hr : Packets.residual F + 2 ≤ q + 2 := by unfold Packets.residual; omega
  unfold RCFive.NativeResources.streamCap RCFive.NativeResources.cutsCap
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hr (by omega))

end

/-! ## 4. The admitted request's facts, uniformly over the three constructors -/

/-- The cache radix polynomial. -/
def betaPoly (a : DecompositionAlgorithm) (degree q : ℕ) : ℕ :=
  3*(16*(q+1)^3)*sourceChildBound a ((uCap degree q + 3)^2) + 4

theorem betaPoly_polynomial (a : DecompositionAlgorithm) (degree : ℕ) :
    PolynomiallyBounded (betaPoly a degree) := by
  have hU := uCap_polynomial degree
  have hsq : PolynomiallyBounded (fun q => (uCap degree q + 3)^2) :=
    polynomiallyBounded_pow (polynomiallyBounded_add hU (polynomiallyBounded_constant 3)) 2
  exact polynomiallyBounded_add (polynomiallyBounded_mul (polynomiallyBounded_mul
    (polynomiallyBounded_constant 3) (polynomiallyBounded_mul (polynomiallyBounded_constant 16)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id
        (polynomiallyBounded_constant 1)) 3)))
    (CloseoutRawRows.sourceChildBound_polynomial a hsq)) (polynomiallyBounded_constant 4)

/-- Every admitted runtime request's family has population `≤ 8(q+1)^3` and occurrence descriptions
`≤ uCap degree q`, hence cache radix `≤ betaPoly`. -/
theorem RequestAdmitted.radix_le {den degree target : ℕ} (hden : 1 ≤ den) (a : DecompositionAlgorithm)
    (r : Request) (hr : RequestAdmitted den degree target r) :
    CompactBounds.radix a (Packets.live (r.family a)) (r.family a).occurrences ≤ betaPoly a degree r.q := by
  have key : (r.family a).occurrences.length ≤ 8*(r.q+1)^3 ∧
      ∀ i : Fin (r.family a).occurrences.length,
        ((r.family a).occurrences.get i).descriptionBits ≤ uCap degree r.q := by
    cases r with
    | terminal => exact ⟨by simp [Request.family], fun i => Fin.elim0 (by simpa [Request.family] using i)⟩
    | sym r0 four L t =>
      obtain ⟨_, hc⟩ := hr
      exact ⟨sym_population hden 5 r0 four (fun c h => (hc c h).1),
        symmetric_occurrences_description r0 (uCap degree r0.q)
          (fun c h => (hc c h).2.trans (Nat.le_add_right _ _))⟩
    | thr r0 four L t =>
      obtain ⟨_, hc⟩ := hr
      exact ⟨thr_population hden 9 r0 four (fun c h => (hc c h).1),
        threshold_occurrences_description r0 (uCap degree r0.q)
          (fun c h => (hc c h).2.trans (Nat.le_add_left _ _))⟩
  have h := NearCubicWires.Admission.beta_le a (Packets.live (r.family a)) (r.family a).occurrences
    (uCap degree r.q) key.2
  unfold betaPoly
  have hm := Nat.mul_le_mul_right (sourceChildBound a ((uCap degree r.q + 3)^2))
    (Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left 2 key.1))
  have e : 3*(2*(8*(r.q+1)^3))*sourceChildBound a ((uCap degree r.q + 3)^2) =
      3*(16*(r.q+1)^3)*sourceChildBound a ((uCap degree r.q + 3)^2) := by ring
  omega

/-- The load of any layout of an admitted request, in the form the caps use. -/
theorem layout_load_facts (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) :
    (Packets.live (r.family a)).card = normalizedLiveCount r.q r.liveScale ∧
      200*((Packets.live (r.family a)).card + layout.w*((Packets.live (r.family a)).card+2)) ≤ r.q ∧
      layout.w ≤ r.q ∧ (Packets.live (r.family a)).card ≤ r.q := by
  have hcard := (geometryOf selector a r).card
  have hload := layout.load
  unfold Packets.residual at hload
  rw [← hcard] at hload
  have hK : (Packets.live (r.family a)).card ≤ r.q := by rw [hcard]; exact normalizedLiveCount_le _ _
  refine ⟨hcard, by omega, ?_, hK⟩
  have : layout.w ≤ 200*(layout.w*((Packets.live (r.family a)).card+2)) := by nlinarith
  omega

theorem two_pow_le_quarter (x q c : ℕ) (hc : 4*c ≤ 200) (h : 200*x ≤ q) : 2^(c*x) ≤ 2^(q/4) :=
  Nat.pow_le_pow_right (by decide) ((Nat.le_div_iff_mul_le (by decide)).mpr (by nlinarith))

/-! ## 5. The three class facts -/

/-- The stream-cap polynomial factor. -/
def streamPoly (a : DecompositionAlgorithm) (degree q : ℕ) : ℕ :=
  (q+2)*(2*(betaPoly a degree q*(q*(q+1)) + (q+1))+3)

theorem streamPoly_polynomial (a : DecompositionAlgorithm) (degree : ℕ) :
    PolynomiallyBounded (streamPoly a degree) := by
  have hq := polynomiallyBounded_id
  have k := fun (n : ℕ) => polynomiallyBounded_constant n
  exact polynomiallyBounded_mul (polynomiallyBounded_add hq (k 2))
    (polynomiallyBounded_add (polynomiallyBounded_mul (k 2) (polynomiallyBounded_add
      (polynomiallyBounded_mul (betaPoly_polynomial a degree) (polynomiallyBounded_mul hq
        (polynomiallyBounded_add hq (k 1)))) (polynomiallyBounded_add hq (k 1)))) (k 3))

/-- The stream cap of any layout (degree `≤` width) of an admitted request. -/
theorem streamCap_small (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) {den degree target : ℕ}
    (hden : 1 ≤ den) (r : Request) (hr : RequestAdmitted den degree target r)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r)) (hdw : layout.degree ≤ r.q) :
    RCFive.NativeResources.streamCap a (r.family a) (geometryOf selector a r) layout ≤
      2^(r.q/4)*streamPoly a degree r.q := by
  obtain ⟨_, hx, hwq, hKq⟩ := layout_load_facts selector a r layout
  have hs := streamCap_le a (r.family a) (geometryOf selector a r) layout hdw hKq
  have hb := RequestAdmitted.radix_le hden a r hr
  have h2 := two_pow_le_quarter ((Packets.live (r.family a)).card + layout.w*((Packets.live (r.family a)).card+2))
    r.q 2 (by norm_num) hx
  unfold streamPoly
  refine hs.trans (Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ ?_))
  have := Nat.mul_le_mul_right (r.q*(r.q+1)) hb
  omega

/-- The header polynomial factor at live scale `L`. -/
def headerPoly (a : DecompositionAlgorithm) (degree L q : ℕ) : ℕ :=
  2^119*(64*((betaPoly a degree q + 1)^2*(q+1)^3))^22*2^(22*L*logScale q)

theorem headerPoly_polynomial (a : DecompositionAlgorithm) (degree L : ℕ) :
    PolynomiallyBounded (headerPoly a degree L) := by
  have k := fun (n : ℕ) => polynomiallyBounded_constant n
  exact polynomiallyBounded_mul (polynomiallyBounded_mul (k (2^119)) (polynomiallyBounded_pow
    (polynomiallyBounded_mul (k 64) (polynomiallyBounded_mul (polynomiallyBounded_pow
      (polynomiallyBounded_add (betaPoly_polynomial a degree) (k 1)) 2)
      (polynomiallyBounded_pow (polynomiallyBounded_add polynomiallyBounded_id (k 1)) 3))) 22))
    (two_pow_mul_logScale_poly (22*L))

/-- The Header exponent: `22(w+K) + w(K+2) ≤ 22 L l + q/4` from the load and `K ≤ L l`. -/
theorem header_exponent_le (w K L l q : ℕ) (hx : 200*(K + w*(K+2)) ≤ q) (hKL : K ≤ L*l) :
    22*(w+K) + w*(K+2) ≤ 22*L*l + q/4 := by
  have h4 : 22*w + w*(K+2) ≤ q/4 := by
    rw [Nat.le_div_iff_mul_le (by decide)]
    have h1 : 22*w ≤ 11*(w*(K+2)) := by nlinarith
    omega
  have : 22*K ≤ 22*L*l := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 22 hKL
  omega

/-- **`h_header`** at the caps `RCFive.RowCaps.chosen`. The small exponent depends on `L` (through
`2^{22K}`), which the small class allows (`Split.order` constrains only the table exponent). -/
theorem header_class (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (printer : WilliamsAlgorithm) (degree target L : ℕ) :
    ∃ headerC headerE : ℕ, ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      r.liveScale = L → ∀ layout : Packets.Layout a (r.family a) (geometryOf selector a r),
      layout.degree ≤ r.q →
      (RCFive.RowCaps.chosen selector a printer r layout).headerFuel ≤
        headerC*RuntimeShape.smallClass 4 headerE r.q := by
  obtain ⟨C, E, _, hC⟩ := headerPoly_polynomial a degree L
  refine ⟨C, E, ?_⟩
  intro den hden r hr hL layout hdw
  obtain ⟨hcard, hx, hwq, hKq⟩ := layout_load_facts selector a r layout
  have hh := headerCap_le a (r.family a) (geometryOf selector a r) layout hdw hwq hKq
  have hb := RequestAdmitted.radix_le hden a r hr
  change RCFive.RowCaps.headerCap a (r.family a) (geometryOf selector a r) layout ≤ _
  have hKL : (Packets.live (r.family a)).card ≤ L*logScale r.q := by
    rw [hcard, hL]; exact Raw.normalizedLiveCount_le_liveScale r.q L
  have hsplit : 2^(22*(layout.w + (Packets.live (r.family a)).card) +
      layout.w*((Packets.live (r.family a)).card+2)) ≤ 2^(22*L*logScale r.q)*2^(r.q/4) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (header_exponent_le _ _ _ _ _ hx hKL)
  have hbase : (CompactBounds.radix a (Packets.live (r.family a)) (r.family a).occurrences + 1)^2*
      (r.q+1)^3 ≤ (betaPoly a degree r.q + 1)^2*(r.q+1)^3 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 2)
  have h22 := Nat.pow_le_pow_left (Nat.mul_le_mul_left 64 hbase) 22
  have hmain := Nat.mul_le_mul (Nat.mul_le_mul_left (2^119) h22) hsplit
  have hpoly := Nat.mul_le_mul_right (2^(r.q/4)) (hC r.q)
  unfold headerPoly at hpoly
  unfold RuntimeShape.smallClass
  calc RCFive.RowCaps.headerCap a (r.family a) (geometryOf selector a r) layout
      ≤ _ := hh
    _ ≤ _ := hmain
    _ = 2^119*(64*((betaPoly a degree r.q + 1)^2*(r.q+1)^3))^22*2^(22*L*logScale r.q)*2^(r.q/4) :=
        (Nat.mul_assoc _ _ _).symm
    _ ≤ C*(r.q+1)^E*2^(r.q/4) := hpoly
    _ = C*((r.q+1)^E*2^(r.q/4)) := Nat.mul_assoc _ _ _

/-- Pure arithmetic of the copy cap `2*Driver.value … + 1`: one table factor `2^res`, the rest small. -/
theorem copy_arith (d p G C x q res e tc Pp Ps : ℕ) (hx : 200*x ≤ q) (hG : G = 2^(2*x))
    (hC : C ≤ 2^(q/4)*Ps) (hp : p ≤ Pp) (hdq : d ≤ q) (hdr : 2*d ≤ res+1) :
    2*(64*(C+1) + 2000000*(d+p+G+1)^3 + tc*(2^d)^2*(d+p+1)^e) + 1 ≤
      (4*tc*(q+Pp+1)^e)*2^res + (128*(Ps+1) + 4000000*(q+Pp+2)^3 + 1)*2^(q/4) := by
  have hQ1 : 1 ≤ 2^(q/4) := Nat.one_le_two_pow
  have hG1 : 1 ≤ G := by rw [hG]; exact Nat.one_le_two_pow
  have hG3 : G^3 ≤ 2^(q/4) := by
    rw [hG, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) ((Nat.le_div_iff_mul_le (by decide)).mpr (by nlinarith))
  have h1 : d+p+G+1 ≤ G*(d+p+2) := by nlinarith
  have h1' : (d+p+G+1)^3 ≤ 2^(q/4)*(q+Pp+2)^3 := by
    calc (d+p+G+1)^3 ≤ (G*(d+p+2))^3 := Nat.pow_le_pow_left h1 3
      _ = G^3*(d+p+2)^3 := by rw [mul_pow]
      _ ≤ 2^(q/4)*(q+Pp+2)^3 := Nat.mul_le_mul hG3 (Nat.pow_le_pow_left (by omega) 3)
  have h2 : (2^d)^2 ≤ 2*2^res := by
    rw [← pow_mul, ← pow_succ']
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : (d+p+1)^e ≤ (q+Pp+1)^e := Nat.pow_le_pow_left (by omega) e
  have hT : tc*(2^d)^2*(d+p+1)^e ≤ 2*(tc*(q+Pp+1)^e*2^res) := by
    calc tc*(2^d)^2*(d+p+1)^e ≤ tc*(2*2^res)*(q+Pp+1)^e :=
          Nat.mul_le_mul (Nat.mul_le_mul_left tc h2) h3
      _ = 2*(tc*(q+Pp+1)^e*2^res) := by ring
  have hCs : C + 1 ≤ (Ps+1)*2^(q/4) := by
    have : 2^(q/4)*Ps + 1 ≤ (Ps+1)*2^(q/4) := by nlinarith
    omega
  have e1 : (4*tc*(q+Pp+1)^e)*2^res = 4*(tc*(q+Pp+1)^e*2^res) := by ring
  have e2 : (128*(Ps+1) + 4000000*(q+Pp+2)^3 + 1)*2^(q/4) =
      128*((Ps+1)*2^(q/4)) + 4000000*(2^(q/4)*(q+Pp+2)^3) + 2^(q/4) := by ring
  omega

/-- The precision polynomial. -/
def precisionPoly (a : DecompositionAlgorithm) (degree q : ℕ) : ℕ :=
  betaPoly a degree q*(q*(q+1)) + (q+1)

theorem precisionPoly_polynomial (a : DecompositionAlgorithm) (degree : ℕ) :
    PolynomiallyBounded (precisionPoly a degree) := by
  have hq := polynomiallyBounded_id
  have k := fun (n : ℕ) => polynomiallyBounded_constant n
  exact polynomiallyBounded_add (polynomiallyBounded_mul (betaPoly_polynomial a degree)
    (polynomiallyBounded_mul hq (polynomiallyBounded_add hq (k 1)))) (polynomiallyBounded_add hq (k 1))

/-- The small class is below the table class once the live count leaves a quarter of `q`. -/
theorem small_le_table (L h q : ℕ) (hK : normalizedLiveCount q L + q/4 ≤ q) :
    RuntimeShape.smallClass 4 h q ≤ RuntimeShape.tableClass L h q := by
  unfold RuntimeShape.smallClass RuntimeShape.tableClass
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))


end
end NearCubicWires.Admission
