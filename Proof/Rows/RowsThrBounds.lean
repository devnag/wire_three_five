import Proof.Rows.RowsThrWidth

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.ThrBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.BlockPlatform NearCubicWires.BlockPlatform.PolyBound
open NearCubicWires.ValidatorPolynomialDomination NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator NearCubicWires.ExtDecompositionBatch NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.RepairSource.CloseoutFinal
open RowsConstruction.SymBounds
noncomputable section

/-! ## Budget polynomials (any measure `m` dominating the sizes) -/

theorem cap_pb : ∃ c d, ∀ m w : Nat, w ≤ m → PolyBounded (1024*(w+1)^2) m c d :=
  ⟨_, _, fun m _ hw => (const 1024 m 0).mul (pb_sq (PolyBound.add (pb_var hw) (const 1 m 1)))⟩

theorem mut_pb : ∃ c d, ∀ m v i : Nat, v ≤ m → i ≤ m →
    PolyBounded (MatrixUnaryTemplate.budget v i) m c d :=
  ⟨_, _, fun m _ _ hv hi =>
    PolyBound.add (PolyBound.add (PolyBound.add
      ((pb_var hi).mul (PolyBound.add ((const 8 m 0).mul (pb_var hv)) (const 10 m 0)))
      ((const 8 m 0).mul (pb_var hv))) (pb_var hi)) (const 17 m 0)⟩

theorem tcc_pb : ∃ c d, ∀ (m n : Nat) (gs : List (ExactThresholdGate n)) (i : Nat), n ≤ m → gs.length ≤ m →
    ((gs.take i).flatMap exactWord).length ≤ m → i ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_TopChildCursor.budget gs i) m c d :=
  ⟨_, _, fun m _ _ _ hn hg hx hi =>
    PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      ((const 2 m 0).mul (nbl_pb hn)) ((const 2 m 0).mul (nbl_pb hg))) (pb_var hx))
      ((PolyBound.add ((const 6 m 0).mul (pb_var hn)) (const 10 m 0)).mul (pb_var hi))) (const 11 m 0)⟩

theorem tfr_pb : ∃ c d, ∀ (m : Nat) (words : List (List Bool)) (j : Fin words.length) (B : Nat),
    (words.flatMap frame).length ≤ m → j.val ≤ m → B ≤ m → (words.get j).length ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_TopFrameReentry.budget words j B) m c d :=
  ⟨_, _, fun m _ _ _ hf hj hB hw =>
    PolyBound.add (PolyBound.add (PolyBound.add ((const 4 m 0).mul (pb_var hf))
      (PolyBound.add ((pb_var hj).mul (PolyBound.add ((const 2 m 0).mul (pb_var hB)) (const 4 m 0)))
        (const 3 m 0)))
      ((const 8 m 0).mul (pb_var hw))) (const 11 m 0)⟩

theorem sch_pb : ∃ c d, ∀ (m n : Nat) (g : ExactThresholdGate n) (C : Nat), C ≤ m → (exactWord g).length ≤ m →
    n ≤ m → PolyBounded (C10ThresholdSelectedChild.budget g C) m c d :=
  ⟨_, _, fun m _ _ _ hC hg hn =>
    PolyBound.add (PolyBound.add (PolyBound.add ((const 6 m 0).mul (pb_var hC)) (pb_var hg))
      ((const 6 m 0).mul (pb_var hn))) (const 18 m 0)⟩

theorem half {x m : Nat} (h : 2*x ≤ m) : x ≤ m := by omega

theorem ite_pb (b : Bool) (m : Nat) : PolyBounded (if b = true then 2 else 0) m 2 0 :=
  PolyBounded.of_le_coefficient (by cases b <;> simp)

/-- `Q*(2*(2*w+2)+2+3)+3+1+(2*w+2)`: the shape of both `FinalPrimeResidue.fuel` and `rowFuel`. -/
theorem rowShape_pb : ∃ c d, ∀ m w Q : Nat, w ≤ m → Q ≤ m →
    PolyBounded (Q*(2*(2*w+2)+2+3)+3+1+(2*w+2)) m c d :=
  ⟨_, _, fun m _ _ hw hQ =>
    PolyBound.add (PolyBound.add (PolyBound.add
      ((pb_var hQ).mul (PolyBound.add (PolyBound.add ((const 2 m 0).mul
        (PolyBound.add ((const 2 m 0).mul (pb_var hw)) (const 2 m 0))) (const 2 m 0)) (const 3 m 0)))
      (const 3 m 0)) (const 1 m 0)) (PolyBound.add ((const 2 m 0).mul (pb_var hw)) (const 2 m 0))⟩

theorem core_pb : ∃ c d, ∀ (m : Nat) (negate : Bool) (z : ℤ) (w : Nat), w ≤ m → 2*natBitLength z.natAbs ≤ m →
    PolyBounded (C10NativeResidueCallback.coreBudget negate z w) m c d := by
  obtain ⟨c0, d0, h0⟩ := rowShape_pb
  exact ⟨_, _, fun m negate z w hw hz =>
    PolyBound.add
      (PolyBound.add
        (PolyBound.add
          (PolyBound.add
            (PolyBound.add
              (PolyBound.add (PolyBound.add ((const 22 m 0).mul (pb_var (half hz))) (const 19 m 0)) (const 1 m 0))
              (PolyBound.add (ite_pb negate m)
                (PolyBound.add (PolyBound.add ((const 2 m 0).mul (h0 m w _ hw hz)) ((const 12 m 0).mul (pb_var hw)))
                  (const 21 m 0))))
            (const 1 m 0))
          (PolyBound.add ((const 2 m 0).mul (pb_var hw)) (const 1 m 0)))
        ((const 4 m 0).mul (pb_var (half hz))))
      (const 11 m 0)⟩

theorem nsw_pb : ∃ c d, ∀ m N F w U : Nat, N ≤ m → F ≤ m → w ≤ m → U ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_NativeScaleWeights.budget N F w U) m c d := by
  obtain ⟨c0, d0, h0⟩ := cap_pb
  exact ⟨_, _, fun m _ _ w _ hN hF hw hU =>
    PolyBound.add ((pb_var hN).mul (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      ((const 4 m 0).mul (pb_var hF)) (h0 m w hw)) ((const 10 m 0).mul (pb_var hU)))
      ((const 18 m 0).mul (pb_var hw))) (const 53 m 0)) (const 3 m 0))) (const 3 m 0)⟩

theorem nsr_pb : ∃ c d, ∀ (m : Nat) (negate : Bool) (z : ℤ) (w F U : Nat), w ≤ m → 2*natBitLength z.natAbs ≤ m →
    F ≤ m → U ≤ m → PolyBounded (PCJ45bee56da9f34d5a_NativeScaleRun.budget negate z w F U) m c d := by
  obtain ⟨c0, d0, h0⟩ := cap_pb
  obtain ⟨c1, d1, h1⟩ := core_pb
  exact ⟨_, _, fun m negate z w _ _ hw hz hF hU =>
    PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add (PolyBound.add
      ((const 2 m 0).mul (h1 m negate z w hw hz)) ((const 2 m 0).mul (pb_var hF))) (h0 m w hw))
      ((const 10 m 0).mul (pb_var hU))) ((const 18 m 0).mul (pb_var hw))) (const 55 m 0)⟩

theorem nse_pb : ∃ c d, ∀ (m n F w U : Nat) (target : ℤ), n ≤ m → F ≤ m → w ≤ m → U ≤ m →
    2*natBitLength target.natAbs ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_NativeScaleEquation.budget n F w U target) m c d := by
  obtain ⟨c0, d0, h0⟩ := nsw_pb
  obtain ⟨c1, d1, h1⟩ := nsr_pb
  exact ⟨_, _, fun m n F w U target hn hF hw hU hz =>
    J (h0 m n F w U hn hF hw hU) (h1 m true target w F U hw hz hF hU)⟩

theorem spr_pb : ∃ c d, ∀ (m n : Nat) (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w F U : Nat),
    n ≤ m → gs.length ≤ m → ((gs.take i.val).flatMap exactWord).length ≤ m → i.val ≤ m →
    (exactWord (gs.get i)).length ≤ m → 2*natBitLength (gs.get i).target.natAbs ≤ m → w ≤ m → F ≤ m →
    U ≤ m → PolyBounded (PCJ45bee56da9f34d5a_SelectedPowerRun.budget gs i w F U) m c d := by
  obtain ⟨c0, d0, h0⟩ := tcc_pb
  obtain ⟨c1, d1, h1⟩ := sch_pb
  obtain ⟨c2, d2, h2⟩ := nse_pb
  obtain ⟨c3, d3, h3⟩ := cap_pb
  exact ⟨_, _, fun m n gs i w F U hn hg hx hi he ht hw hF hU =>
    J (J (PolyBound.add (PolyBound.add (PolyBound.add (h0 m n gs i.val hn hg hx hi) (h1 m n (gs.get i) U hU he hn))
          ((const 4 m 0).mul (pb_var hU))) (const 13 m 0))
        (J (h2 m n F w U (gs.get i).target hn hF hw hU ht)
          (PolyBound.add (PolyBound.add (PolyBound.add (h3 m w hw) ((const 10 m 0).mul (pb_var hU)))
            ((const 18 m 0).mul (pb_var hw))) (const 45 m 0))))
      (PolyBound.add ((const 4 m 0).mul (pb_var hU)) (const 9 m 0))⟩

theorem spready_pb : ∃ c d, ∀ (m n : Nat) (gs : List (ExactThresholdGate n)) (i : Fin gs.length)
    (w F U v : Nat), n ≤ m → gs.length ≤ m → ((gs.take i.val).flatMap exactWord).length ≤ m → i.val ≤ m →
    (exactWord (gs.get i)).length ≤ m → 2*natBitLength (gs.get i).target.natAbs ≤ m → w ≤ m → F ≤ m →
    U ≤ m → v ≤ m → PolyBounded (PCJ45bee56da9f34d5a_SelectedPowerReady.budget gs i w F U v) m c d := by
  obtain ⟨c0, d0, h0⟩ := pqn_pb
  obtain ⟨c1, d1, h1⟩ := mut_pb
  obtain ⟨c2, d2, h2⟩ := spr_pb
  exact ⟨_, _, fun m n gs i w F U v hn hg hx hi he ht hw hF hU hv =>
    J (J (J (PolyBound.add (PolyBound.add ((const 2 m 0).mul (h0 m n hn)) ((const 4 m 0).mul (pb_var hU)))
            (const 10 m 0))
          (PolyBound.add (PolyBound.add (h1 m v i.val hv hi) ((const 2 m 0).mul (pb_var hU))) (const 5 m 0)))
        (h2 m n gs i w F U hn hg hx hi he ht hw hF hU))
      (PolyBound.add ((const 4 m 0).mul (pb_var hU)) (const 9 m 0))⟩

theorem cpr_pb : ∃ c d, ∀ (m : Nat) (words : List (List Bool)) (j : Fin words.length) (C n : Nat)
    (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w F U v : Nat),
    (words.flatMap frame).length ≤ m → j.val ≤ m → C ≤ m → (words.get j).length ≤ m →
    n ≤ m → gs.length ≤ m → ((gs.take i.val).flatMap exactWord).length ≤ m → i.val ≤ m →
    (exactWord (gs.get i)).length ≤ m → 2*natBitLength (gs.get i).target.natAbs ≤ m → w ≤ m → F ≤ m →
    U ≤ m → v ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_CircuitPowerRun.budget words j C gs i w F U v) m c d := by
  obtain ⟨c0, d0, h0⟩ := tfr_pb
  obtain ⟨c1, d1, h1⟩ := spready_pb
  exact ⟨_, _, fun m words j C n gs i w F U v hf hj hC hwj hn hg hx hi he ht hw hF hU hv =>
    J (J (PolyBound.add (PolyBound.add (h0 m words j C hf hj hC hwj) ((const 4 m 0).mul (pb_var hU)))
          (const 12 m 0))
        (h1 m n gs i w F U v hn hg hx hi he ht hw hF hU hv))
      (PolyBound.add ((const 2 m 0).mul (pb_var hU)) (const 4 m 0))⟩

theorem tt_pb : ∃ c d, ∀ (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
    (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q)) (x : BitInput r.q) (m T L target w U P : Nat),
    r.q ≤ m → natBitLength L ≤ m → natBitLength target ≤ m →
    (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r).length ≤ m → T ≤ m → P ≤ m → U ≤ m → w ≤ m →
    PCJ45bee56da9f34d5a_StreamCompare.count a r sel I x ≤ m → 1 ≤ m →
    PolyBounded (PCJ45bee56da9f34d5a_ThresholdTraversal.budget a r sel I x T L target w U P) m c d := by
  obtain ⟨c0, d0, h0⟩ := nff_pb
  obtain ⟨c1, d1, h1⟩ := rowShape_pb
  exact ⟨_, _, fun a r sel I x m T L target w U P hq hL ht hN hT hP hU hw hc h1m =>
    J (J (J (h0 m 1 r.q L target _ T h1m hq hL ht hN hT)
          (J (PolyBound.add ((const 4 m 0).mul (pb_var hP)) (const 27 m 0))
            (PolyBound.add (PolyBound.add ((const 6 m 0).mul (pb_var hU)) ((const 10 m 0).mul (pb_var hw)))
              (const 28 m 0))))
        (PolyBound.add ((const 2 m 0).mul (pb_var hU)) (const 6 m 0)))
      (h1 m w _ hw hc)⟩

theorem cw_pb : ∃ c d, ∀ m T w : Nat, T ≤ m → w ≤ m → PolyBounded (4*(T*(2*w+1))+(2*w+1)) m c d :=
  ⟨_, _, fun m _ _ hT hw =>
    PolyBound.add ((const 4 m 0).mul ((pb_var hT).mul (PolyBound.add ((const 2 m 0).mul (pb_var hw)) (const 1 m 0))))
      (PolyBound.add ((const 2 m 0).mul (pb_var hw)) (const 1 m 0))⟩

theorem lin_pb (m : Nat) : PolyBounded (m+2) m 2 1 := by
  unfold PolyBounded; rw [pow_one]; omega

theorem fit {v m c d C D : Nat} (h : PolyBounded v m c d) (hc : c ≤ C) (hd : d ≤ D) : v ≤ C*(m+1)^D :=
  (h.coefficient_mono hc).degree_mono hd

/-! ## List-length facts -/

theorem flatMap_length_le {α β : Type} (l : List α) (f : α → List β) (K : Nat) (h : ∀ y ∈ l, (f y).length ≤ K) :
    (l.flatMap f).length ≤ l.length*K := by
  induction l with
  | nil => simp
  | cons y l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h y (by simp)
    have h2 := ih (fun z hz => h z (by simp [hz]))
    rw [Nat.succ_mul]
    omega

theorem take_flatMap_le {α β : Type} (l : List α) (f : α → List β) (i : Nat) :
    ((l.take i).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.flatMap_append, List.length_append]
  omega

theorem mem_flatMap_le {α β : Type} (l : List α) (f : α → List β) (y : α) (hy : y ∈ l) :
    (f y).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨y, hy, rfl⟩)

theorem flatMap_intWord_ge (l : List ℤ) : 2*l.length ≤ (l.flatMap intWord).length := by
  induction l with
  | nil => simp
  | cons z l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, DecompositionSource.intWord_length]
    omega

/-- An exact gate's word carries `2` bits per input at least. -/
theorem arity_le_exactWord {n : Nat} (g : ExactThresholdGate n) : 2*n+2 ≤ (exactWord g).length := by
  have h := flatMap_intWord_ge (List.ofFn g.weight)
  rw [List.length_ofFn] at h
  simp only [exactWord, List.length_append, DecompositionSource.intWord_length]
  omega

theorem weight_le_exactWord {n : Nat} (g : ExactThresholdGate n) (k : Fin n) :
    2*natBitLength (g.weight k).natAbs+2 ≤ (exactWord g).length := by
  have h := mem_flatMap_le (List.ofFn g.weight) intWord (g.weight k) (List.mem_ofFn.mpr ⟨k, rfl⟩)
  rw [DecompositionSource.intWord_length] at h
  have e : intBitLength (g.weight k) = natBitLength (g.weight k).natAbs := rfl
  simp only [exactWord, List.length_append]
  omega

theorem target_le_exactWord {n : Nat} (g : ExactThresholdGate n) :
    2*natBitLength g.target.natAbs+2 ≤ (exactWord g).length := by
  have e : intBitLength g.target = natBitLength g.target.natAbs := rfl
  simp only [exactWord, List.length_append, DecompositionSource.intWord_length]
  omega

theorem gates_le {q : Nat} (c : NormalizedThresholdThresholdCircuit q) :
    (PCJ45bee56da9f34d5a_NativeCircuitCodec.thrGates c).length+1 ≤
      (frame (PCJd4d1d9d7d1fa4313_Production.thrWord c)).length := by
  have hb := flatMap_length_le (List.ofFn (fun i => c.bottom (retainedTopIndex c i)))
    (fun g => frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g)) 1
  have hb' : (List.ofFn (fun i => c.bottom (retainedTopIndex c i))).length ≤
      ((List.ofFn (fun i => c.bottom (retainedTopIndex c i))).flatMap
        (fun g => frame (PCJd4d1d9d7d1fa4313_Production.bottomWord g))).length := by
    induction (List.ofFn (fun i => c.bottom (retainedTopIndex c i))) with
    | nil => simp
    | cons g l ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, frame_length]
      omega
  clear hb
  simp only [PCJ45bee56da9f34d5a_NativeCircuitCodec.thrGates, List.length_ofFn] at hb' ⊢
  simp only [PCJd4d1d9d7d1fa4313_Production.thrWord, frame_length, List.length_append] at hb' ⊢
  omega

/-! ## Encoding facts: every THR size is bounded by `T = |input|` -/

section Facts
variable (a : DecompositionAlgorithm) (r : FourfoldRequest NormalizedThresholdThresholdCircuit)
  (four : r.circuits.length ≤ 4) (L target : Nat)

theorem header_le : 2*natBitLength r.q+1 + (2*natBitLength L+1) + (2*natBitLength target+1) ≤
    ThrWidth.T a r four L target := by
  have h := SymBounds.native_le_input a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target)
  simp only [PCJd4d1d9d7d1fa4313_Production.Request.nativeWord, List.length_append,
    DecompositionSource.natWord_length] at h
  simp only [ThrWidth.T]
  omega

theorem native_le : (PCJ45bee56da9f34d5a_StreamPair.native r L target).length ≤ ThrWidth.T a r four L target := by
  rw [PCJ45bee56da9f34d5a_StreamPair.native_eq r four L target]
  exact SymBounds.native_le_input a _

theorem flags_le (I : Finset (Fin r.q)) (x : BitInput r.q) :
    (PCJ45bee56da9f34d5a_StreamPair.flags r I x).length ≤ ThrWidth.T a r four L target+1 := by
  have h0 : (PCJ45bee56da9f34d5a_StreamPair.flags r I x).length =
      (PCJ45bee56da9f34d5a_NativeFlags.word (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r) I x).length := rfl
  have h1 : (PCJ45bee56da9f34d5a_NativeFlags.word (PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits r) I x).length ≤
      (r.circuits.map (fun c => (frame (PCJd4d1d9d7d1fa4313_Production.thrWord c)).length)).sum+1 := by
    rw [PCJ45bee56da9f34d5a_NativeFlags.word_length]
    simp only [PCJ45bee56da9f34d5a_NativeFlagsMeaning.circuits, List.map_map]
    apply Nat.add_le_add_right
    apply List.sum_le_sum
    intro c _
    exact gates_le c
  have h2 : (r.circuits.map (fun c => (frame (PCJd4d1d9d7d1fa4313_Production.thrWord c)).length)).sum =
      (r.circuits.flatMap (fun c => frame (PCJd4d1d9d7d1fa4313_Production.thrWord c))).length := by
    rw [List.length_flatMap]
  have h3 : (r.circuits.flatMap (fun c => frame (PCJd4d1d9d7d1fa4313_Production.thrWord c))).length ≤
      (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target).nativeWord.length := by
    simp only [PCJd4d1d9d7d1fa4313_Production.Request.nativeWord, List.length_append]
    omega
  have h4 := SymBounds.native_le_input a (PCJd4d1d9d7d1fa4313_Production.Request.thr r four L target)
  simp only [ThrWidth.T]
  omega

theorem exactWord_le (c : NormalizedThresholdThresholdCircuit r.q) (hc : c ∈ r.circuits)
    (g : ExactThresholdGate c.top.support.card) (hg : g ∈ ThresholdRows.children a c) :
    (exactWord g).length ≤ ThrWidth.T a r four L target := by
  refine le_trans ?_ (ThrWidth.children_le a r four L target c hc)
  have h := mem_flatMap_le (ThresholdRows.children a c) exactWord g hg
  simp only [exactListWord, List.length_append]
  omega

theorem take_le (c : NormalizedThresholdThresholdCircuit r.q) (hc : c ∈ r.circuits) (i : Nat) :
    (((ThresholdRows.children a c).take i).flatMap exactWord).length ≤ ThrWidth.T a r four L target := by
  refine le_trans (take_flatMap_le _ _ i) (le_trans ?_ (ThrWidth.children_le a r four L target c hc))
  simp only [exactListWord, List.length_append]
  omega

theorem arity_le (c : NormalizedThresholdThresholdCircuit r.q) (hc : c ∈ r.circuits)
    (g : ExactThresholdGate c.top.support.card) (hg : g ∈ ThresholdRows.children a c) :
    2*c.top.support.card+2 ≤ ThrWidth.T a r four L target :=
  le_trans (arity_le_exactWord g) (exactWord_le a r four L target c hc g hg)

theorem count_le (sel : ThresholdRows.Selection a r) (I : Finset (Fin r.q)) (x : BitInput r.q) :
    PCJ45bee56da9f34d5a_StreamCompare.count a r sel I x ≤ 4*ThrWidth.T a r four L target+1 := by
  unfold PCJ45bee56da9f34d5a_StreamCompare.count PCJ45bee56da9f34d5a_ExpandedThresholdStream.terms
  refine Nat.add_le_add_right (le_trans (flatMap_length_le _ _ (ThrWidth.T a r four L target) ?_) ?_) 1
  · intro i _
    simp only [PCJ45bee56da9f34d5a_ExpandedThresholdStream.block, List.length_append, List.length_ofFn,
      List.length_singleton]
    have := arity_le a r four L target (r.circuits.get i) (List.get_mem _ _)
      ((ThresholdRows.children a (r.circuits.get i)).get (sel i)) (List.get_mem _ (sel i))
    omega
  · rw [List.length_ofFn]
    exact Nat.mul_le_mul_right _ four

theorem words_eq (sel : ThresholdRows.Selection a r) :
    (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words =
      r.circuits.map (fun c => PCJ45bee56da9f34d5a_TopChildCursor.payload (ThresholdRows.children a c)) := by
  apply List.ext_get
  · simp [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.words, PCJ45bee56da9f34d5a_StreamPair.data,
      PCJ45bee56da9f34d5a_ThresholdData.data]
  · intro n _ _
    simp [PCJ45bee56da9f34d5a_FourfoldBaseData.Data.words, PCJ45bee56da9f34d5a_StreamPair.data,
      PCJ45bee56da9f34d5a_ThresholdData.data]

theorem words_frame_le (sel : ThresholdRows.Selection a r) :
    ((PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words.flatMap frame).length ≤
      ThrWidth.T a r four L target := by
  rw [words_eq, List.flatMap_map]
  exact ThrWidth.topWord_le a r four L target

theorem word_le (sel : ThresholdRows.Selection a r) (y : List Bool)
    (hy : y ∈ (PCJ45bee56da9f34d5a_StreamPair.data a r four sel).words) : y.length ≤ ThrWidth.T a r four L target := by
  have h1 := mem_flatMap_le _ frame y hy
  have h2 := words_frame_le a r four L target sel
  rw [frame_length] at h1
  omega

end Facts

/-! ## The coefficient stream -/

theorem stream_le (d : PCJ45bee56da9f34d5a_FourfoldBaseData.Data) (B p w N : Nat)
    (hN : ∀ j : Fin d.count, d.arity j+1 ≤ N) (k : Nat) :
    (PCJ45bee56da9f34d5a_FourfoldPowerData.stream d B p w k).length ≤ k*(N*(2*w+1)) := by
  induction k with
  | zero => simp [PCJ45bee56da9f34d5a_FourfoldPowerData.stream]
  | succ k ih =>
    simp only [PCJ45bee56da9f34d5a_FourfoldPowerData.stream]
    split
    · rename_i h
      rw [List.length_append]
      have hr := FinalPrimeModular.blocks_length
        (PCJ45bee56da9f34d5a_NativeScaleWeights.words (PCJ45bee56da9f34d5a_FourfoldPowerData.factor d B p k) p w
          (PCJ45bee56da9f34d5a_NativeScaleEquation.weights
            (PCJ45bee56da9f34d5a_SelectedPowerBody.equation ((d.gates ⟨k, h⟩).get (d.selected ⟨k, h⟩)))))
        w (fun _ => SignedSortKey.binary_length _ _) 0 (d.arity ⟨k, h⟩)
      have hN' := Nat.mul_le_mul_right (2*w+1) (hN ⟨k, h⟩)
      simp only [PCJ45bee56da9f34d5a_NativeScaleEquation.result, List.length_append, frame_length,
        SignedSortKey.binary_length, hr]
      have e : (k+1)*(N*(2*w+1)) = k*(N*(2*w+1))+N*(2*w+1) := by ring
      have e' : (d.arity ⟨k, h⟩+1)*(2*w+1) = d.arity ⟨k, h⟩*(2*w+1)+(2*w+1) := by ring
      omega
    · have e : (k+1)*(N*(2*w+1)) = k*(N*(2*w+1))+N*(2*w+1) := by ring
      omega

/-! ## The THR cell parameters, as closed polynomials of `(q, T)` -/

/-- `m₁ := q+w` with `w := 12T+19`: dominates every size the U- and F-level budgets read. -/
def m1Of (q T : Nat) := q+(12*T+19)
def UOf (cU dU q T : Nat) := cU*(m1Of q T+1)^dU
def FOf (cF dF q T : Nat) := cF*(m1Of q T+1)^dF
def m2Of (cU dU cF dF q T : Nat) := m1Of q T+UOf cU dU q T+FOf cF dF q T
def POf (cU dU cF dF cP dP q T : Nat) := cP*(m2Of cU dU cF dF q T+1)^dP
def BOf (cU dU cF dF cP dP cB dB q T : Nat) := cB*(m2Of cU dU cF dF q T+POf cU dU cF dF cP dP q T+1)^dB

theorem m1_pb (q T : Nat) : PolyBounded (m1Of q T) (q+T) 19 1 := by
  unfold PolyBounded m1Of; rw [pow_one]; omega

theorem self_pb (c d m : Nat) : PolyBounded (c*(m+1)^d) m c d := le_refl _

/-- **The four THR parameters are one fixed polynomial of `q+|input|`** (degrees compose, never a table
size). -/
theorem params_pb (cU dU cF dF cP dP cB dB : Nat) : ∃ c d, ∀ q T : Nat,
    PolyBounded (UOf cU dU q T+FOf cF dF q T+POf cU dU cF dF cP dP q T+BOf cU dU cF dF cP dP cB dB q T)
      (q+T) c d :=
  ⟨_, _, fun q T =>
    PolyBound.add (PolyBound.add (PolyBound.add
      (comp (self_pb cU dU (m1Of q T)) (m1_pb q T))
      (comp (self_pb cF dF (m1Of q T)) (m1_pb q T)))
      (comp (self_pb cP dP (m2Of cU dU cF dF q T))
        (PolyBound.add (PolyBound.add (m1_pb q T) (comp (self_pb cU dU (m1Of q T)) (m1_pb q T)))
          (comp (self_pb cF dF (m1Of q T)) (m1_pb q T)))))
      (comp (self_pb cB dB (m2Of cU dU cF dF q T+POf cU dU cF dF cP dP q T))
        (PolyBound.add
          (PolyBound.add (PolyBound.add (m1_pb q T) (comp (self_pb cU dU (m1Of q T)) (m1_pb q T)))
            (comp (self_pb cF dF (m1Of q T)) (m1_pb q T)))
          (comp (self_pb cP dP (m2Of cU dU cF dF q T))
            (PolyBound.add (PolyBound.add (m1_pb q T) (comp (self_pb cU dU (m1Of q T)) (m1_pb q T)))
              (comp (self_pb cF dF (m1Of q T)) (m1_pb q T))))))⟩

/-! ## C3(e) for THR -/

end
end RowsConstruction.ThrBounds
