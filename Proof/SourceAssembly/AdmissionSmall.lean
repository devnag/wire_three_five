import Proof.SourceAssembly.AdmissionSmallArith
import Proof.MachineModel.RuntimeShapeClasses

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.Admission
open NearCubicWires NearCubicWires.SupplierPipeline NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierWalkBridge NearCubicWires.SupplierListSchedule
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.PolynomialSchedule NearCubicWires.RepairRepresentation NearCubicWires.SupplierCapacity
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairOrdinary.CloseoutRowsRawLogShape
open NearCubicWires.RepairSource.CloseoutRawRows (descriptionEnvelope descriptionEnvelope_polynomial
  rowDepthAt windowSumAt symmetric_occurrences_description threshold_occurrences_description)
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production

noncomputable section

/-- The occurrence bound `occ+2 ≤ 2^(3 L_q + 4)` for a population `≤ 8(q+1)^3`. -/
theorem occ_two_pow {q occ : ℕ} (h : occ ≤ 8*(q+1)^3) : occ + 2 ≤ 2^(3*logScale q + 4) := by
  have h3 : (q+1)^3 ≤ 2^(3*logScale q) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left (succ_le_two_pow_logScale' q) 3
  have hp : 1 ≤ 2^(3*logScale q) := Nat.one_le_two_pow
  have : 2^(3*logScale q + 4) = 16*2^(3*logScale q) := by rw [pow_add]; ring
  omega

/-- The graded depth of a population `occ+2 ≤ 2^ell` is at most `ell+8`. -/
theorem depth_le {q : ℕ} (occ : List (SupportedNormalizedGate q)) (I : Finset (Fin q)) (ell : ℕ)
    (h : occ.length + 2 ≤ 2^ell) : canonicalGradedDepth (LiveRows.bound occ I) ≤ ell + 8 := by
  unfold canonicalGradedDepth
  apply Nat.clog_le_of_le_pow
  have hb := RepairOrdinary.CloseoutFinalC10WireEnvelope.touchingCost_le_length occ I
  unfold LiveRows.bound
  rw [pow_add]
  have : (2:ℕ)^8 = 256 := by norm_num
  omega

/-- `q + |input|` under one power of two whose exponent is `O(L_q)`. -/
theorem input_two_pow (q inp C E : ℕ) (h : inp ≤ C*(q+1)^E) :
    q + inp ≤ 2^(natBitLength (C+1) + (E+1)*logScale q) := by
  have hq : (q+1)^(E+1) ≤ 2^((E+1)*logScale q) := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (succ_le_two_pow_logScale' q) _
  have hc : C+1 ≤ 2^natBitLength (C+1) := (lt_two_pow_natBitLength _).le
  have h1 : q + inp ≤ (C+1)*(q+1)^(E+1) := by
    have hp : (q+1)^E ≤ (q+1)^(E+1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hq1 : q+1 ≤ (q+1)^(E+1) := Nat.le_self_pow (by omega) _
    nlinarith [Nat.mul_le_mul_left C hp]
  rw [pow_add]
  exact h1.trans (Nat.mul_le_mul hc hq)

/-! ## The printer inequality's constants, named (so the case lemmas stay small) -/

noncomputable def symDen0 (ct ce L : ℕ) : ℕ := (Raw.admitted_layout_sym ct ce L 1 (by norm_num)).choose
noncomputable def symOnset (ct ce L : ℕ) : ℕ :=
  (Raw.admitted_layout_sym ct ce L 1 (by norm_num)).choose_spec.choose

noncomputable def thrDen0 (cz ct ce L : ℕ) : ℕ := (Raw.admitted_layout_thr cz ct ce L 1 (by norm_num)).choose
noncomputable def thrOnset (cz ct ce L : ℕ) : ℕ :=
  (Raw.admitted_layout_thr cz ct ce L 1 (by norm_num)).choose_spec.choose

/-- The final step shared by both modes. -/
theorem small_finish (q m d W K X A S : ℕ) (hm : 1 ≤ m) (hlog : 1 ≤ logScale q)
    (hload : 200*(K+W*(K+2)) ≤ q-K) (hK : m*d ≤ K) (hX : X ≤ A*logScale q^2)
    (hrest0 : 2*(m*(d*(A+4)))*logScale q^2 ≤ q) (hsz : S ≤ 2^(W + X + 4)) :
    S^d ≤ 1*RuntimeShape.smallClass m 0 q := by
  have hload' : 200*W*(K+2) ≤ q := by
    have : 200*(K+W*(K+2)) = 200*K + 200*W*(K+2) := by ring
    omega
  have hl2 : 1 ≤ logScale q^2 := Nat.one_le_pow _ _ hlog
  have h4 : A*logScale q^2+4 ≤ (A+4)*logScale q^2 := by
    have e : (A+4)*logScale q^2 = A*logScale q^2 + 4*logScale q^2 := by ring
    omega
  have hrest : 2*(m*(d*(A*logScale q^2+4))) ≤ q := by
    have : 2*(m*(d*(A*logScale q^2+4))) ≤ 2*(m*(d*(A+4)))*logScale q^2 := by
      calc 2*(m*(d*(A*logScale q^2+4))) ≤ 2*(m*(d*((A+4)*logScale q^2))) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left m (Nat.mul_le_mul_left d h4))
        _ = 2*(m*(d*(A+4)))*logScale q^2 := by ring
    omega
  have he := small_exponent_le q m d W K A (logScale q) hm hload' hK hrest
  unfold RuntimeShape.smallClass
  rw [pow_zero, Nat.one_mul, Nat.one_mul]
  calc S^d ≤ (2^(W + X + 4))^d := Nat.pow_le_pow_left hsz d
    _ = 2^(d*(W + X + 4)) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2^(q/m) := Nat.pow_le_pow_right (by decide)
        ((Nat.mul_le_mul_left d (by omega)).trans he)

/-- The `O(L_q^2)` remainder, arithmetic only. -/
theorem remainder_le (ell l ce nb E Lv t0 T5 T6 Z A : ℕ) (hl : 1 ≤ l) (hell : ell + 1 = (ce+1)*l)
    (hT5 : T5 ≤ (ce+1)*(Z+1)*l^2) (hT6 : T6 ≤ (t0+1)*l)
    (hA : (ce+1)^2 + 10*(ce+1) + nb + E + 1 + Lv + (ce+1)*(Z+1) + t0 + 1 ≤ A) :
    ell*(ell+9) + (nb + (E+1)*l) + Lv*l + T5 + T6 ≤ A*l^2 := by
  have he : ell ≤ (ce+1)*l := by omega
  have hl2 : l ≤ l^2 := Nat.le_self_pow (by norm_num) _
  have h1 : ell*(ell+9) ≤ ((ce+1)^2 + 9*(ce+1))*l^2 := by
    have h9 : ell + 9 ≤ (ce+1)*l + 9*l := by omega
    calc ell*(ell+9) ≤ ((ce+1)*l)*((ce+1)*l + 9*l) := Nat.mul_le_mul he h9
      _ = ((ce+1)^2 + 9*(ce+1))*l^2 := by ring
  have h2 : nb ≤ nb*l^2 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hl)
  have h3 : (E+1)*l ≤ (E+1)*l^2 := Nat.mul_le_mul_left _ hl2
  have h4 : Lv*l ≤ Lv*l^2 := Nat.mul_le_mul_left _ hl2
  have h5 : T5 ≤ (ce+1)*(Z+1)*l^2 := hT5
  have h6 : T6 ≤ (t0+1)*l^2 := hT6.trans (Nat.mul_le_mul_left _ hl2)
  have hsum : ((ce+1)^2 + 9*(ce+1))*l^2 + nb*l^2 + (E+1)*l^2 + Lv*l^2 + (ce+1)*(Z+1)*l^2 +
      (t0+1)*l^2 = ((ce+1)^2 + 9*(ce+1) + nb + E + 1 + Lv + (ce+1)*(Z+1) + t0 + 1)*l^2 := by ring
  have hAl : ((ce+1)^2 + 9*(ce+1) + nb + E + 1 + Lv + (ce+1)*(Z+1) + t0 + 1)*l^2 ≤ A*l^2 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- SYM: the load and the `smallSize` bound at one admitted request. -/
theorem sym_small_facts (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (degree target L den Cin Ein ce ceS : ℕ) (hden1 : 1 ≤ den) (hce : ceS + 7 ≤ ce)
    (hceS : ∀ {q L : ℕ} (F : Packets.Family q L), F.occurrences.length ≤ 8*(q+1)^3 →
      (∀ i : Fin F.occurrences.length, (F.occurrences.get i).descriptionBits ≤ symDescCap degree q) →
      natBitLength (Packets.alphabet a F) + 1 ≤ (ceS+1)*logScale q)
    (hin : ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      (r.input a).length ≤ (Cin + 4*r.liveScale)*(r.q+1)^Ein)
    (hd : symDen0 (canonicalWalkLength (4*(target+1))) ce L ≤ den)
    (r0 : FourfoldRequest NormalizedSymmetricThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (hcirc : ∀ c ∈ r0.circuits, c.wireCount ≤ max (r0.q*(r0.q+1)) (carriedWireCap den 5 r0.q) ∧
      c.descriptionBits ≤ symDescCap degree r0.q)
    (ho : symOnset (canonicalWalkLength (4*(target+1))) ce L ≤ r0.q) :
    ∃ W ell : ℕ, ell + 1 = (ce+1)*logScale r0.q ∧
      200*(normalizedLiveCount r0.q L + W*(normalizedLiveCount r0.q L+2)) ≤
        r0.q - normalizedLiveCount r0.q L ∧
      (Request.sym r0 four L target).smallSize a ≤
        2^(W + (ell*(ell+9) + (natBitLength (Cin+4*L+1) + (Ein+1)*logScale r0.q) +
          normalizedLiveCount r0.q L + ell + canonicalWalkLength (4*(target+1))) + 4) := by
  have hlog : 1 ≤ logScale r0.q := logScale_pos r0.q
  obtain ⟨ell, hell⟩ : ∃ ell, ell + 1 = (ce+1)*logScale r0.q := ⟨(ce+1)*logScale r0.q - 1, by
    have : 1 ≤ (ce+1)*logScale r0.q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega⟩
  have hwire : ∀ c ∈ r0.circuits,
      c.wireCount ≤ max (r0.q*(r0.q+1)) (carriedWireCap den 5 r0.q) := fun c hc => (hcirc c hc).1
  have hpop := sym_population hden1 5 r0 four hwire
  have h34 : 3*logScale r0.q + 4 ≤ ell := by
    have h8 : 8*logScale r0.q ≤ (ce+1)*logScale r0.q := Nat.mul_le_mul_right _ (by omega)
    omega
  have hocc : (symmetricFourfoldOccurrences r0).length + 2 ≤ 2^ell :=
    (occ_two_pow hpop).trans (Nat.pow_le_pow_right (by decide) h34)
  have hdesc := symmetric_occurrences_description r0 (symDescCap degree r0.q)
    (fun c hc => (hcirc c hc).2)
  have halph : Packets.alphabet a (Packets.symFamily r0 L target) ≤ 2^ell := by
    have h := hceS (Packets.symFamily r0 L target) hpop hdesc
    have hm' := Nat.mul_le_mul_right (logScale r0.q) (show ceS+1 ≤ ce+1 by omega)
    exact (lt_two_pow_natBitLength _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have g := Packets.geometry selector (Packets.symFamily r0 L target)
  have hwalk1 := Raw.symmetric_walk_constant target r0 four
  have hKle := Raw.normalizedLiveCount_le_liveScale r0.q L
  obtain ⟨_, hlt, _, hload⟩ := (Raw.admitted_layout_sym (canonicalWalkLength (4*(target+1))) ce L 1
    (by norm_num)).choose_spec.choose_spec den hd r0
    (Packets.live (Packets.symFamily r0 L target)) (symmetricListDenominator r0 target) ell
    (normalizedLiveCount r0.q L) ho four hwalk1 (by omega) hKle g.touch
    (fun c hc => by rw [one_mul]; exact hwire c hc)
  refine ⟨_, ell, hell, hload, ?_⟩
  have hdeg : (Request.sym r0 four L target).degree a ≤ r0.circuits.length *
      Packets.coordinateDegree (symmetricFourfoldOccurrences r0)
        (Packets.live (Packets.symFamily r0 L target)) (symmetricListDenominator r0 target) := by
    unfold Request.degree
    apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    exact le_of_eq (Raw.symFamily_row_degree r0 L target row hrow)
  have hwalk : canonicalWalkLength (symmetricListDenominator r0 target) ≤
      canonicalWalkLength (4*(target+1)) := by omega
  have hinp := input_two_pow r0.q ((Request.sym r0 four L target).input a).length (Cin+4*L) Ein
    (hin den hden1 _ ⟨rfl, hcirc⟩)
  have hsz := small_sum_le r0.q ((Request.sym r0 four L target).input a).length
    (Packets.live (Packets.symFamily r0 L target)).card (symmetricFourfoldOccurrences r0).length
    (Packets.alphabet a (Packets.symFamily r0 L target)) ((symmetricFourfoldOccurrences r0).length+1)
    (canonicalWalkLength (symmetricListDenominator r0 target))
    (canonicalGradedDepth (LiveRows.bound (symmetricFourfoldOccurrences r0)
      (Packets.live (Packets.symFamily r0 L target))))
    ((Request.sym r0 four L target).degree a) ell _ _
    (natBitLength (Cin+4*L+1) + (Ein+1)*logScale r0.q) ell (canonicalWalkLength (4*(target+1)))
    (normalizedLiveCount r0.q L)
    hinp (le_of_eq g.card) hocc halph hdeg hlt (by omega) hwalk
    (depth_le (symmetricFourfoldOccurrences r0) _ ell hocc)
  unfold Request.smallSize
  exact hsz

/-- THR: the load and the `smallSize` bound at one admitted request. -/
theorem thr_small_facts (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (degree target L den Cin Ein ce ceT cz ct : ℕ) (hden1 : 1 ≤ den) (hce : ceT + 7 ≤ ce)
    (hceT : ∀ {q L : ℕ} (F : Packets.Family q L), F.occurrences.length ≤ 8*(q+1)^3 →
      (∀ i : Fin F.occurrences.length,
        (F.occurrences.get i).descriptionBits ≤ descriptionEnvelope degree q) →
      natBitLength (Packets.alphabet a F) + 1 ≤ (ceT+1)*logScale q)
    (hzt : ∀ (r : FourfoldRequest NormalizedThresholdThresholdCircuit), r.circuits.length ≤ 4 →
      (∀ c ∈ r.circuits, c.descriptionBits ≤ descriptionEnvelope degree r.q) →
      modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r target)+1 ≤
          (cz+1)*logScale r.q ∧
        canonicalWalkLength (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r target)+1 ≤
          (ct+1)*logScale r.q)
    (hin : ∀ den : ℕ, 1 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      (r.input a).length ≤ (Cin + 4*r.liveScale)*(r.q+1)^Ein)
    (hd : thrDen0 cz ct ce L ≤ den)
    (r0 : FourfoldRequest NormalizedThresholdThresholdCircuit) (four : r0.circuits.length ≤ 4)
    (hcirc : ∀ c ∈ r0.circuits, c.wireCount ≤ max (r0.q*(r0.q+1)) (carriedWireCap den 9 r0.q) ∧
      c.descriptionBits ≤ descriptionEnvelope degree r0.q)
    (ho : thrOnset cz ct ce L ≤ r0.q) :
    ∃ W ell : ℕ, ell + 1 = (ce+1)*logScale r0.q ∧
      200*(normalizedLiveCount r0.q L + W*(normalizedLiveCount r0.q L+2)) ≤
        r0.q - normalizedLiveCount r0.q L ∧
      (Request.thr r0 four L target).smallSize a ≤
        2^(W + (ell*(ell+9) + (natBitLength (Cin+4*L+1) + (Ein+1)*logScale r0.q) +
          normalizedLiveCount r0.q L + ell*((cz+1)*logScale r0.q) + (ct+1)*logScale r0.q) + 4) := by
  have hlog : 1 ≤ logScale r0.q := logScale_pos r0.q
  obtain ⟨ell, hell⟩ : ∃ ell, ell + 1 = (ce+1)*logScale r0.q := ⟨(ce+1)*logScale r0.q - 1, by
    have : 1 ≤ (ce+1)*logScale r0.q := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega⟩
  have hwire : ∀ c ∈ r0.circuits,
      c.wireCount ≤ max (r0.q*(r0.q+1)) (carriedWireCap den 9 r0.q) := fun c hc => (hcirc c hc).1
  have hpop := thr_population hden1 9 r0 four hwire
  have h34 : 3*logScale r0.q + 4 ≤ ell := by
    have h8 : 8*logScale r0.q ≤ (ce+1)*logScale r0.q := Nat.mul_le_mul_right _ (by omega)
    omega
  have hocc : (thresholdFourfoldOccurrences r0).length + 2 ≤ 2^ell :=
    (occ_two_pow hpop).trans (Nat.pow_le_pow_right (by decide) h34)
  have hdesc := threshold_occurrences_description r0 (descriptionEnvelope degree r0.q)
    (fun c hc => (hcirc c hc).2)
  have halph : Packets.alphabet a (Packets.thrFamily a r0 L target) ≤ 2^ell := by
    have h := hceT (Packets.thrFamily a r0 L target) hpop hdesc
    have hm' := Nat.mul_le_mul_right (logScale r0.q) (show ceT+1 ≤ ce+1 by omega)
    exact (lt_two_pow_natBitLength _).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨hz, ht⟩ := hzt r0 four (fun c hc => (hcirc c hc).2)
  have g := Packets.geometry selector (Packets.thrFamily a r0 L target)
  have hKle := Raw.normalizedLiveCount_le_liveScale r0.q L
  obtain ⟨_, hlt, _, hload⟩ := (Raw.admitted_layout_thr cz ct ce L 1
    (by norm_num)).choose_spec.choose_spec den hd r0
    (Packets.live (Packets.thrFamily a r0 L target))
    (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r0 target)
    (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target)) ell
    (normalizedLiveCount r0.q L) ho four hz ht (by omega) hKle g.touch
    (fun c hc => by rw [one_mul]; exact hwire c hc)
  refine ⟨_, ell, hell, hload, ?_⟩
  have hdeg : (Request.thr r0 four L target).degree a ≤
      modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target) *
      Packets.coordinateDegree (thresholdFourfoldOccurrences r0)
        (Packets.live (Packets.thrFamily a r0 L target))
        (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r0 target) := by
    unfold Request.degree
    apply foldl_max_le _ _ _ (Nat.zero_le _)
    intro x hx
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hx
    exact Raw.thrFamily_row_degree a r0 L target row hrow
  have htw : ((thresholdFourfoldOccurrences r0).length+1)^
      (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target)) ≤
      2^(ell*((cz+1)*logScale r0.q)) := by
    calc ((thresholdFourfoldOccurrences r0).length+1)^
          (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target))
        ≤ (2^ell)^(modulusDigitCount
            (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target)) :=
          Nat.pow_le_pow_left (by omega) _
      _ = 2^(ell*modulusDigitCount
            (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target)) := by
          rw [← pow_mul]
      _ ≤ 2^(ell*((cz+1)*logScale r0.q)) :=
          Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left ell (by omega))
  have hinp := input_two_pow r0.q ((Request.thr r0 four L target).input a).length (Cin+4*L) Ein
    (hin den hden1 _ ⟨rfl, hcirc⟩)
  have hsz := small_sum_le r0.q ((Request.thr r0 four L target).input a).length
    (Packets.live (Packets.thrFamily a r0 L target)).card (thresholdFourfoldOccurrences r0).length
    (Packets.alphabet a (Packets.thrFamily a r0 L target))
    (((thresholdFourfoldOccurrences r0).length+1)^
      (modulusDigitCount (RepairOrdinary.CloseoutFinalC10ThresholdRows.primeCutoff a r0 target)))
    (canonicalWalkLength (RepairOrdinary.CloseoutFinalC10ThresholdRows.listDenominator a r0 target))
    (canonicalGradedDepth (LiveRows.bound (thresholdFourfoldOccurrences r0)
      (Packets.live (Packets.thrFamily a r0 L target))))
    ((Request.thr r0 four L target).degree a) ell _ _
    (natBitLength (Cin+4*L+1) + (Ein+1)*logScale r0.q) (ell*((cz+1)*logScale r0.q))
    ((ct+1)*logScale r0.q) (normalizedLiveCount r0.q L)
    hinp (le_of_eq g.card) hocc halph hdeg hlt htw (by omega)
    (depth_le (thresholdFourfoldOccurrences r0) _ ell hocc)
  unfold Request.smallSize
  exact hsz

/-- **`h_small`.** For the producer degree `d`, the divisor `m` and the live scale `L` (all fixed
before), one carried-coefficient threshold and one arity onset put every fixed power of every admitted
request's `smallSize` in the small class `2^(q/m)`. -/
theorem small_poly (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm)
    (degree target L d m : ℕ) (hL : 1 ≤ L) (hm : 1 ≤ m) :
    ∃ den0 onset : ℕ, ∀ den : ℕ, den0 ≤ den → ∀ r : Request, RequestAdmitted den degree target r →
      r.liveScale = L → onset ≤ r.q →
      (r.smallSize a)^d ≤ 1*RuntimeShape.smallClass m 0 r.q := by
  obtain ⟨ceS, hceS⟩ := alphabet_log a (symDescCap_polynomial degree)
  obtain ⟨ceT, hceT⟩ := alphabet_log a (descriptionEnvelope_polynomial degree)
  obtain ⟨cz, ct, hzt⟩ := thr_factor_logs a degree target
  obtain ⟨Cin, Ein, hin⟩ := input_poly a degree target
  obtain ⟨ce, hce⟩ : ∃ ce, ce = ceS + ceT + 7 := ⟨_, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0, t0 = canonicalWalkLength (4*(target+1)) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = (ce+1)^2 + 10*(ce+1) + natBitLength (Cin+4*L+1) + Ein + 1 + L +
    (ce+1)*(cz+1) + (t0 + ct) + 1 := ⟨_, rfl⟩
  obtain ⟨o3, h3⟩ := coefficient_mul_logScale_pow_eventually_le (2*(m*(d*(A+4)))) 2
  refine ⟨max 1 (max (symDen0 t0 ce L) (thrDen0 cz ct ce L)),
    max (max (symOnset t0 ce L) (thrOnset cz ct ce L)) (max o3 (2^(m*d))), ?_⟩
  intro den hden r hr hLr hq
  have hden1 : 1 ≤ den := (le_max_left _ _).trans hden
  have hd1 : symDen0 t0 ce L ≤ den := ((le_max_left _ _).trans (le_max_right _ _)).trans hden
  have hd2 : thrDen0 cz ct ce L ≤ den := ((le_max_right _ _).trans (le_max_right _ _)).trans hden
  have ho1 : symOnset t0 ce L ≤ r.q := ((le_max_left _ _).trans (le_max_left _ _)).trans hq
  have ho2 : thrOnset cz ct ce L ≤ r.q := ((le_max_right _ _).trans (le_max_left _ _)).trans hq
  have ho3 : o3 ≤ r.q := ((le_max_left _ _).trans (le_max_right _ _)).trans hq
  have ho4 : 2^(m*d) ≤ r.q := ((le_max_right _ _).trans (le_max_right _ _)).trans hq
  have hlog : 1 ≤ logScale r.q := logScale_pos r.q
  have hK : m*d ≤ normalizedLiveCount r.q L := by
    unfold normalizedLiveCount
    exact le_min ((Nat.lt_two_pow_self).le.trans ho4)
      ((logScale_eventually_ge (m*d) r.q ho4).trans (Nat.le_mul_of_pos_left _ hL))
  have hKL : normalizedLiveCount r.q L ≤ L*logScale r.q := Raw.normalizedLiveCount_le_liveScale r.q L
  have hrest0 := h3 r.q ho3
  cases r with
  | terminal => simp [Request.liveScale] at hLr; omega
  | sym r0 four L' t =>
    obtain ⟨htt, hcirc⟩ := hr
    subst htt
    change L' = L at hLr
    subst hLr
    change 1 ≤ logScale r0.q at hlog
    change m*d ≤ normalizedLiveCount r0.q L' at hK
    change normalizedLiveCount r0.q L' ≤ L'*logScale r0.q at hKL
    change 2*(m*(d*(A+4)))*logScale r0.q^2 ≤ r0.q at hrest0
    rw [ht0] at hd1 ho1
    obtain ⟨W, ell, hell, hload, hsz⟩ := sym_small_facts selector a degree t L' den Cin Ein ce ceS
      hden1 (by omega) hceS hin hd1 r0 four hcirc ho1
    refine small_finish r0.q m d W (normalizedLiveCount r0.q L') _ A _ hm hlog hload hK ?_ hrest0 hsz
    have hr := remainder_le ell (logScale r0.q) ce (natBitLength (Cin+4*L'+1)) Ein L' t0 ell t0 cz A
      hlog hell (by
        have h1 : ell ≤ (ce+1)*logScale r0.q := by omega
        have h2 : (ce+1)*logScale r0.q ≤ (ce+1)*logScale r0.q*((cz+1)*logScale r0.q) :=
          Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hlog)
        have e : (ce+1)*logScale r0.q*((cz+1)*logScale r0.q) = (ce+1)*(cz+1)*logScale r0.q^2 := by ring
        omega) (by
        have : t0 ≤ (t0+1)*logScale r0.q := by
          have := Nat.mul_le_mul_left (t0+1) hlog
          omega
        omega) (by omega)
    omega
  | thr r0 four L' t =>
    obtain ⟨htt, hcirc⟩ := hr
    subst htt
    change L' = L at hLr
    subst hLr
    change 1 ≤ logScale r0.q at hlog
    change m*d ≤ normalizedLiveCount r0.q L' at hK
    change normalizedLiveCount r0.q L' ≤ L'*logScale r0.q at hKL
    change 2*(m*(d*(A+4)))*logScale r0.q^2 ≤ r0.q at hrest0
    obtain ⟨W, ell, hell, hload, hsz⟩ := thr_small_facts selector a degree t L' den Cin Ein ce ceT cz ct
      hden1 (by omega) hceT hzt hin hd2 r0 four hcirc ho2
    refine small_finish r0.q m d W (normalizedLiveCount r0.q L') _ A _ hm hlog hload hK ?_ hrest0 hsz
    have hr := remainder_le ell (logScale r0.q) ce (natBitLength (Cin+4*L'+1)) Ein L' ct
      (ell*((cz+1)*logScale r0.q)) ((ct+1)*logScale r0.q) cz A hlog hell (by
        have h1 : ell ≤ (ce+1)*logScale r0.q := by omega
        have h2 := Nat.mul_le_mul_right ((cz+1)*logScale r0.q) h1
        have e : (ce+1)*logScale r0.q*((cz+1)*logScale r0.q) = (ce+1)*(cz+1)*logScale r0.q^2 := by ring
        omega) (le_refl _) (by omega)
    omega


end
end NearCubicWires.Admission
