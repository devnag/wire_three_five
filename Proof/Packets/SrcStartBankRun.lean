import Proof.Packets.SrcStartBankWords

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Bank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation RepairSource.VerifierDecoding P1Closure SupplierPipeline SupplierEstimator
open RepairSource RepairSource.CloseoutFinal PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. Facts about the request's words -/

theorem bf_append {q : ℕ} (g h : List (SupportedNormalizedGate q)) :
    Rounds.bf (g ++ h) = Rounds.bf g ++ Rounds.bf h := by simp [Rounds.bf]

theorem bf_le_segment {q : ℕ} (gs : List (SupportedNormalizedGate q)) (t : List Bool) :
    (Rounds.bf gs).length ≤ (RepairOrdinary.frame (segment gs t)).length := by
  unfold Rounds.bf
  rw [Circuit.segment_split, Circuit.frames_bottoms, frame_length]
  simp only [List.length_append]
  omega

theorem bf_le_flat {q : ℕ} {C : Type} (cs : List C) (occF : C → List (SupportedNormalizedGate q))
    (topF : C → List Bool) :
    (Rounds.bf (cs.flatMap occF)).length ≤ (cs.flatMap (fun c => RepairOrdinary.frame (segment (occF c) (topF c)))).length := by
  induction cs with
  | nil => simp [Rounds.bf]
  | cons c cs ih =>
    simp only [List.flatMap_cons, bf_append, List.length_append]
    have := bf_le_segment (occF c) (topF c)
    omega

theorem stream_eq_bf {q : ℕ} (occ : List (SupportedNormalizedGate q)) : PoolEntryLoop.stream occ = Rounds.bf occ := rfl

/-- The occurrence stream is no longer than the native word. -/
theorem stream_le_nw (a : DecompositionAlgorithm) (r : Request) :
    (PoolEntryLoop.stream (r.family a).occurrences).length ≤ r.nativeWord.length := by
  cases r with
  | terminal => simp [PoolEntryLoop.stream, Request.family]
  | sym r four L target =>
    have h := bf_le_flat r.circuits symmetricCircuitOccurrences (fun c => List.ofFn c.top)
    have hw : Request.nativeWord (.sym r four L target) = natWord 0 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => RepairOrdinary.frame (segment (symmetricCircuitOccurrences c) (List.ofFn c.top))) := by
      simp only [Request.nativeWord, Circuit.symWord_segment]
    rw [hw, stream_eq_bf]
    simp only [List.length_append]
    change (Rounds.bf (symmetricFourfoldOccurrences r)).length ≤ _
    unfold symmetricFourfoldOccurrences
    omega
  | thr r four L target =>
    have h := bf_le_flat r.circuits thresholdCircuitOccurrences
      (fun c => thresholdWord (CompilerSemantics.nonStrictAsStrict (retainedTopGate c)))
    have hw : Request.nativeWord (.thr r four L target) = natWord 1 ++ natWord r.q ++ natWord L ++ natWord target ++
        natWord r.circuits.length ++ r.circuits.flatMap
          (fun c => RepairOrdinary.frame (segment (thresholdCircuitOccurrences c)
            (thresholdWord (CompilerSemantics.nonStrictAsStrict (retainedTopGate c))))) := by
      simp only [Request.nativeWord, Circuit.thrWord_segment]
    rw [hw, stream_eq_bf]
    simp only [List.length_append]
    change (Rounds.bf (thresholdFourfoldOccurrences r)).length ≤ _
    unfold thresholdFourfoldOccurrences
    omega

theorem occ_le_stream {q : ℕ} (occ : List (SupportedNormalizedGate q)) :
    occ.length ≤ (PoolEntryLoop.stream occ).length ∧
      ∀ g ∈ occ, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ (PoolEntryLoop.stream occ).length := by
  induction occ with
  | nil => simp
  | cons g occ ih =>
    have e : PoolEntryLoop.stream (g :: occ) = RepairOrdinary.frame (CloseoutRowsCircuitBottom.nativeWord g) ++ PoolEntryLoop.stream occ :=
      rfl
    rw [e]
    simp only [List.length_append, frame_length, List.length_cons, List.mem_cons]
    refine ⟨by omega, ?_⟩
    rintro h (rfl | hh)
    · omega
    · have := ih.2 h hh
      omega

theorem occ_le_nw (a : DecompositionAlgorithm) (r : Request) : (r.family a).occurrences.length ≤ r.nativeWord.length :=
  (occ_le_stream _).1.trans (stream_le_nw a r)

theorem bottom_le_nw (a : DecompositionAlgorithm) (r : Request) :
    ∀ g ∈ (r.family a).occurrences, (CloseoutRowsCircuitBottom.nativeWord g).length ≤ r.nativeWord.length :=
  fun g hg => ((occ_le_stream _).2 g hg).trans (stream_le_nw a r)

theorem nw_le_value (B q : ℕ) : B ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q := by
  have h1 : (B + q + 1)^1 ≤ (B + q + 1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at h1
  unfold PCJ6e421fabe2aa4155_SourcePoolCapacity.value
  omega

/-! ## 2. The producer's bank -/

theorem pp_input {q : ℕ} (live : Finset (Fin q)) (B N : ℕ) (S : List Bool) (k : Fin 229) :
    PCJ6e421fabe2aa4155_SourcePoolProduced.input live B N S k = if k.val = 0 then CompareMachine.word q
      else if k.val = 1 then List.replicate B true else if k.val = 62 then CompareMachine.word N
      else if k.val = 63 then CloseoutRowsGateSupport.gateMembers live else if k.val = 64 then S else [] := by
  fin_cases k <;> rfl

theorem slots_worker (i : Fin 132) :
    (PCJ6e421fabe2aa4155_SourcePoolProduced.slots (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i)).val = 93 + i.val := by
  have hw : (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker i).val = 9 + i.val := by
    simp only [PCJ6e421fabe2aa4155_SourcePoolInitialize.worker, PCJ6e421fabe2aa4155_SourcePoolAllocate.worker, Fin.val_castAdd,
      Fin.val_natAdd]
  simp only [PCJ6e421fabe2aa4155_SourcePoolProduced.slots]
  split_ifs with h1 h2
  · omega
  · have := congrArg Fin.val h2
    simp only [hw] at this
    have := i.isLt
    omega
  · simp [hw]
    omega

theorem start_tapes {q : ℕ} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (B : ℕ) :
    (PCJ6fbdd6f776f6447d_Source.PoolCold.start live occ B (B+q+1) []).tapes =
      PCJ6e421fabe2aa4155_SourcePoolBank.startBank live B occ.length (PoolEntryLoop.stream occ) := rfl

theorem start_heads {q : ℕ} (live : Finset (Fin q)) (occ : List (SupportedNormalizedGate q)) (B : ℕ) :
    (PCJ6fbdd6f776f6447d_Source.PoolCold.start live occ B (B+q+1) []).heads =
      PCJ6e421fabe2aa4155_SourcePoolInitialize.head occ.length := by
  funext i; fin_cases i <;> rfl

/-! ## 3. The three machine stages and the head move -/

section stages
variable (a : DecompositionAlgorithm)

/-- `1^B, 1^q ↦ 1^(B+q)` (74), the sources kept. -/
theorem z_run (B q R : ℕ) (E : T3 a → List Bool)
    (h97 : E (tl a 97 (by omega)) = ZeroPadding.pad R (List.replicate B true))
    (h61 : E (tl a 61 (by omega)) = ZeroPadding.pad R (List.replicate q true))
    (h74 : E (tl a 74 (by omega)) = List.replicate R false) (h75 : E (tl a 75 (by omega)) = List.replicate R false) :
    ∃ E' : T3 a → List Bool, Step (mZ a) (2*(B+q)+6) (fun _ => 0) E (fun _ => 0) E' ∧
      E' (tl a 74 (by omega)) = ZeroPadding.pad R (List.replicate (B+q) true) ∧
      ∀ x : T3 a, x.val ≠ 132 + Cold.tapes a + 74 → x.val ≠ 132 + Cold.tapes a + 75 → E' x = E x := by
  have st := Stages.stage0 (BlockPlatform.UnaryCalc.sum_step B q) (sZ a) (sZ_inj a) R E (by
    intro j
    fin_cases j
    · exact h97
    · exact h61
    · show E (tl a 74 (by omega)) = ZeroPadding.pad R ([] : List Bool)
      rw [h74, Stages.pad_nil]
    · show E (tl a 75 (by omega)) = ZeroPadding.pad R ([] : List Bool)
      rw [h75, Stages.pad_nil])
  refine ⟨_, st, install_slot (sZ a) (sZ_inj a) E _ 2, ?_⟩
  intro x h1 h2
  by_cases x97 : x.val = 132 + Cold.tapes a + 97
  · have e : x = sZ a 0 := Fin.ext x97
    rw [e, install_slot (sZ a) (sZ_inj a)]
    exact h97.symm
  by_cases x61 : x.val = 132 + Cold.tapes a + 61
  · have e : x = sZ a 1 := Fin.ext x61
    rw [e, install_slot (sZ a) (sZ_inj a)]
    exact h61.symm
  apply install_other
  intro j hj
  have hv := congrArg Fin.val hj
  have hs := sZ_spec a j
  omega

theorem pc_run (B q R : ℕ) (E : T3 a → List Bool)
    (h74 : E (tl a 74 (by omega)) = ZeroPadding.pad R (List.replicate (B+q) true))
    (hbl : ∀ j, j.val ≠ 0 → E (sPC a j) = List.replicate R false) :
    ∃ E' : T3 a → List Bool, Step (mPC a) (PCPSerializerCapacity.Power.budget 3 16777216 (B+q)) (fun _ => 0) E (fun _ => 0) E' ∧
      E' (tP a) = ZeroPadding.pad R (List.replicate (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) true) ∧
      ∀ x : T3 a, x.val ≠ 132 + Cold.tapes a + 74 → x.val ≠ 132 + SB a + 14 →
        (x.val < 132 + Cold.tapes a + 77 ∨ 132 + Cold.tapes a + 96 ≤ x.val) → E' x = E x := by
  obtain ⟨out, hs, _, ho⟩ := BlockPlatform.UnaryCalc.poly_step 3 16777216 (B+q)
  have st := Stages.stage0 hs (sPC a) (sPC_inj a) R E (by
    intro j
    by_cases j0 : j.val = 0
    · have e : sPC a j = tl a 74 (by omega) := Fin.ext (by rw [sPC_val, if_pos j0]; rfl)
      rw [e, h74]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, j0]
    · rw [hbl j j0]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, j0, Stages.pad_nil])
  have hout : (BlockPlatform.UnaryCalc.outputTape 3).val ≠ 0 := by
    intro h
    exact BlockPlatform.UnaryCalc.output_ne_input 3 (Fin.ext (by rw [h]; rfl))
  refine ⟨_, st, ?_, ?_⟩
  · have e : tP a = sPC a (BlockPlatform.UnaryCalc.outputTape 3) := Fin.ext (by rw [sPC_val, if_neg hout, if_pos rfl]; rfl)
    rw [e, install_slot (sPC a) (sPC_inj a), ho]
    rfl
  · intro x h1 h2 h3
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    have hs := sPC_spec a j
    have := j.isLt
    simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at this
    omega

/-- **The accepted start-bank producer at `N ≤ B`**, its 132 worker slots on the bank's writer tapes. -/
theorem pr_run {q : ℕ} (live : Finset (Fin q)) (B N : ℕ) (S : List Bool) (hn : N ≤ B)
    (hs : S.length ≤ PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q) (R : ℕ)
    (hR : PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q ≤ R) (E : T3 a → List Bool)
    (h96 : E (tl a 96 (by omega)) = ZeroPadding.pad R (CompareMachine.word q))
    (h97 : E (tl a 97 (by omega)) = ZeroPadding.pad R (List.replicate B true))
    (h158 : E (tl a 158 (by omega)) = ZeroPadding.pad R (CompareMachine.word N))
    (h159 : E (tl a 159 (by omega)) = ZeroPadding.pad R (CloseoutRowsGateSupport.gateMembers live))
    (h160 : E (tl a 160 (by omega)) = ZeroPadding.pad R S)
    (hbl : ∀ p : Fin 230, p.val ≠ 0 → p.val ≠ 1 → p.val ≠ 62 → p.val ≠ 63 → p.val ≠ 64 → E (sPR a p) = List.replicate R false) :
    ∃ (H' : T3 a → ℕ) (E' : T3 a → List Bool),
      Step (mPR a) (2*PCJ6e421fabe2aa4155_SourcePoolProduced.budget B q N+2) (fun _ => 0) E H' E' ∧
      (∀ (i : ℕ) (hi : i < 132), H' (bk a i (by omega)) = PCJ6e421fabe2aa4155_SourcePoolInitialize.head N ⟨i, hi⟩) ∧
      (∀ x : T3 a, 132 ≤ x.val → H' x = 0) ∧
      (∀ (i : ℕ) (hi : i < 132), E' (bk a i (by omega)) =
        ZeroPadding.pad R (PCJ6e421fabe2aa4155_SourcePoolBank.startBank live B N S ⟨i, hi⟩)) ∧
      (∀ x : T3 a, 132 ≤ x.val → x.val < 132 + Cold.tapes a + 96 → E' x = E x) := by
  obtain ⟨H, A, sp, hh, ha⟩ := PoolGen.produced_run live B N S hn hs
  obtain ⟨k, m⟩ := PacketsGlue.RequestMeta.step_mask0 sp selPR (fun _ _ => rfl)
  have hz : Fin.addCases (motive := fun _ => ℕ) (fun _ : Fin 229 => 0) (fun _ : Fin 1 => 0) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp
  have m' := m.congr_in hz rfl
  have hE : ∀ p : Fin (229 + 1), E (sPR a p) =
      ZeroPadding.pad R (Fin.addCases (PCJ6e421fabe2aa4155_SourcePoolProduced.input live B N S) (fun _ : Fin 1 => []) p) := by
    intro p
    by_cases p229 : p.val < 229
    · rw [addCases_lt _ _ p p229, pp_input]
      by_cases p0 : p.val = 0
      · have e : sPR a p = tl a 96 (by omega) := Fin.ext (by rw [sPR_val, if_pos (by omega)]; simp [p0])
        rw [e, h96, if_pos p0]
      by_cases p1 : p.val = 1
      · have e : sPR a p = tl a 97 (by omega) := Fin.ext (by rw [sPR_val, if_pos (by omega)]; simp [p1])
        rw [e, h97, if_neg p0, if_pos p1]
      by_cases p62 : p.val = 62
      · have e : sPR a p = tl a 158 (by omega) := Fin.ext (by rw [sPR_val, if_pos (by omega)]; simp [p62])
        rw [e, h158, if_neg p0, if_neg p1, if_pos p62]
      by_cases p63 : p.val = 63
      · have e : sPR a p = tl a 159 (by omega) := Fin.ext (by rw [sPR_val, if_pos (by omega)]; simp [p63])
        rw [e, h159, if_neg p0, if_neg p1, if_neg p62, if_pos p63]
      by_cases p64 : p.val = 64
      · have e : sPR a p = tl a 160 (by omega) := Fin.ext (by rw [sPR_val, if_pos (by omega)]; simp [p64])
        rw [e, h160, if_neg p0, if_neg p1, if_neg p62, if_neg p63, if_pos p64]
      rw [hbl p p0 p1 p62 p63 p64, if_neg p0, if_neg p1, if_neg p62, if_neg p63, if_neg p64, Stages.pad_nil]
    · have p229' : p.val = 229 := by have := p.isLt; omega
      rw [addCases_ge _ _ p (by omega), hbl p (by omega) (by omega) (by omega) (by omega) (by omega), Stages.pad_nil]
  have d := (m'.pad (fun _ => R)).dock (sPR a) (sPR_inj a) (fun _ => 0) E (fun _ => rfl) hE
  have hwk : ∀ (i : ℕ) (hi : i < 132), bk a i (by omega) = sPR a ⟨93 + i, by omega⟩ := by
    intro i hi
    apply Fin.ext
    rw [sPR_val, if_neg (by simp only; omega), if_pos (by simp only; omega)]
    simp only [bk_val]
    omega
  have hsl : ∀ (i : ℕ) (hi : i < 132), (⟨93 + i, by omega⟩ : Fin 229) =
      PCJ6e421fabe2aa4155_SourcePoolProduced.slots (PCJ6e421fabe2aa4155_SourcePoolInitialize.worker ⟨i, hi⟩) :=
    fun i hi => Fin.ext (by rw [slots_worker])
  refine ⟨_, _, d, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hwk i hi, dockH_slot _ (sPR_inj a), addCases_lt _ _ _ (by simp only; omega)]
    have hsel : selPR ⟨93 + i, by omega⟩ = false := by
      simp only [selPR, Bool.not_eq_eq_eq_not, Bool.not_false, Bool.and_eq_true, decide_eq_true_eq]
      omega
    simp only [hsel, Bool.false_eq_true, if_false]
    rw [hsl i hi, hh]
  · intro x hx
    by_cases hr : ∃ p, sPR a p = x
    · obtain ⟨p, rfl⟩ := hr
      rw [dockH_slot _ (sPR_inj a)]
      have hs := sPR_spec a p
      by_cases p229 : p.val < 229
      · rw [addCases_lt (n := 229) (m := 1) _ _ p p229]
        have hsel : selPR ⟨p.val, p229⟩ = true := by
          simp only [selPR, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        simp [hsel]
      · rw [addCases_ge (n := 229) (m := 1) _ _ p (by omega)]
    · simp only [not_exists] at hr
      exact dockH_other _ _ _ _ hr
  · intro i hi
    rw [hwk i hi, install_slot _ (sPR_inj a), addCases_lt _ _ _ (by simp only; omega), hsl i hi, ha,
      PCJ6e421fabe2aa4155_SourcePoolSeedFanout.pad_pad _ _ _ hR]
  · intro x h1 h2
    apply install_other
    intro p hp
    have hv := congrArg Fin.val hp
    have hs := sPR_spec a p
    have := p.isLt
    omega

/-- The template tape's head to `1`. -/
theorem mv_run (H : T3 a → ℕ) (A : T3 a → List Bool) :
    Step (mMV a) 1 H A (fun i => (dirMV a i).apply (H i)) A := by
  obtain ⟨r, hr, hf, _⟩ := DecompositionCountPosition.move_run (dirMV a) H A
  exact Step.of_run hr (by rw [hf]) (by rw [hf])

end stages

end
end NearCubicWires.SourceStart.Bank

