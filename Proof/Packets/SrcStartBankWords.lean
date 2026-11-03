import Proof.Packets.SrcStartBank

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Bank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation RepairSource.VerifierDecoding P1Closure SupplierPipeline SupplierEstimator
open RepairSource RepairSource.CloseoutFinal PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. Helpers -/

theorem addCases_lt {α : Type} {n m : ℕ} (w : Fin n → α) (f : Fin m → α) (j : Fin (n+m)) (h : j.val < n) :
    Fin.addCases w f j = w ⟨j.val, h⟩ := by
  induction j using Fin.addCases with
  | left i => rw [Fin.addCases_left]; rfl
  | right i => exfalso; simp only [Fin.val_natAdd] at h; omega

theorem addCases_ge {α : Type} {n m : ℕ} (w : Fin n → α) (f : Fin m → α) (j : Fin (n+m)) (h : n ≤ j.val) :
    Fin.addCases w f j = f ⟨j.val - n, by have := j.isLt; omega⟩ := by
  induction j using Fin.addCases with
  | left i => exfalso; have := i.isLt; simp only [Fin.val_castAdd] at h; omega
  | right i =>
    rw [Fin.addCases_right]
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd]
    omega

/-- **A two-tape stage on the bank universe**, with a value-level frame. -/
theorem pair_tl (a : DecompositionAlgorithm) {s : ℕ} {M : Machine 2 s} {c : ℕ} {src out : List Bool} {H : Fin 2 → ℕ}
    (h : Step M c (fun _ => 0) ![src, []] H ![src, out]) (R : ℕ) (xs xo xl : T3 a)
    (hd1 : xs.val ≠ xo.val) (hd2 : xs.val ≠ xl.val) (hd3 : xo.val ≠ xl.val) (E : T3 a → List Bool)
    (hs : E xs = ZeroPadding.pad R src) (ho : E xo = List.replicate R false) (hl : E xl = List.replicate R false) :
    ∃ E' : T3 a → List Bool,
      Step (RecoveryFocus.machine ![xs, xo, xl] (MaskedReset.machine M (fun _ => true))) (2*c+2) (fun _ => 0) E (fun _ => 0) E' ∧
      E' xo = ZeroPadding.pad R out ∧ ∀ x : T3 a, x.val ≠ xo.val → x.val ≠ xl.val → E' x = E x := by
  obtain ⟨E', st, _, o, f⟩ := Stages.pair_stage h R xs xo xl (fun e => hd1 (congrArg Fin.val e)) (fun e => hd2 (congrArg Fin.val e))
    (fun e => hd3 (congrArg Fin.val e)) E hs ho hl
  exact ⟨E', st, o, fun x h1 h2 => f x (fun e => h1 (congrArg Fin.val e)) (fun e => h2 (congrArg Fin.val e))⟩

/-! ## 2. The request's words -/

section words
variable (a : DecompositionAlgorithm)

/-- The per-occurrence support bitmaps (the support word is their frames). -/
def supF (r : Request) : List (List Bool) :=
  (r.family a).occurrences.map (fun g : SupportedNormalizedGate r.q => List.ofFn (fun i : Fin r.q => decide (i ∈ g.support)))

theorem sup_eq (r : Request) : r.supportWord a = PacketsGlue.CountFrames.frames (supF a r) := by
  unfold Request.supportWord PacketsGlue.CountFrames.frames supF
  rw [List.map_map]
  rfl

theorem supF_length (r : Request) : (supF a r).length = (r.family a).occurrences.length := by
  unfold supF; rw [List.length_map]

/-- The word stages' cost (exactly the composed `Step`'s). -/
def wordsCost (r : Request) : ℕ :=
  ((((((((2*(2*r.nativeWord.length+1)+2) + 1 + (2*Stream.xBound r.nativeWord.length+2)) + 1 +
    (2*(2*(List.replicate r.q true).length+1)+2)) + 1 + (2*(r.q+2)+2)) + 1 + (2*(r.q+2)+2)) + 1 +
    (2*(r.nativeWord.length+1+0)+2)) + 1 + (2*(RepairOrdinary.frame (PacketsGlue.CountFrames.frames (supF a r))).length+2)) + 1 +
    (2*((supF a r).length+2)+2)) + 1 +
    (2*(2*(CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a))).length+1)+2)

/-- The tapes the word stages return exactly. -/
def Keep9 (v : ℕ) : Prop :=
  (v < 132 + Cold.tapes a ∧ v ≠ 132 + SB a + 10) ∨ (132 + Cold.tapes a ≤ v ∧ v < 132 + Cold.tapes a + 5) ∨
  (132 + Cold.tapes a + 74 ≤ v ∧ v ≠ 132 + Cold.tapes a + 96 ∧ v ≠ 132 + Cold.tapes a + 97 ∧ v ≠ 132 + Cold.tapes a + 158 ∧
    v ≠ 132 + Cold.tapes a + 159 ∧ v ≠ 132 + Cold.tapes a + 160)

/-- **The word stages at a request.** -/
theorem words_run (r : Request) (R : ℕ) (E : T3 a → List Bool)
    (hin : ∀ (j : ℕ) (h : j < 5), E (tl a j (by omega)) = ZeroPadding.pad R (SourceFactorSel.Item4.inWord a r ⟨j, h⟩))
    (hbl : ∀ x : T3 a, (x.val < 132 + Cold.tapes a ∨ 132 + Cold.tapes a + 5 ≤ x.val) → E x = List.replicate R false) :
    ∃ E9 : T3 a → List Bool, Step (wordsM a) (wordsCost a r) (fun _ => 0) E (fun _ => 0) E9 ∧
      E9 (tl a 96 (by omega)) = ZeroPadding.pad R (CompareMachine.word r.q) ∧
      E9 (tl a 97 (by omega)) = ZeroPadding.pad R (List.replicate r.nativeWord.length true) ∧
      E9 (tl a 158 (by omega)) = ZeroPadding.pad R (CompareMachine.word (r.family a).occurrences.length) ∧
      E9 (tl a 159 (by omega)) = ZeroPadding.pad R (CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a))) ∧
      E9 (tl a 160 (by omega)) = ZeroPadding.pad R (PoolEntryLoop.stream (r.family a).occurrences) ∧
      E9 (tl a 61 (by omega)) = ZeroPadding.pad R (List.replicate r.q true) ∧
      E9 (tT a) = ZeroPadding.pad R (CompareMachine.word r.q) ∧
      ∀ x : T3 a, Keep9 a x.val → E9 x = E x := by
  have hct := tapes_ge a
  -- 1. the frame copy of the native word (5)
  obtain ⟨H1, l1⟩ := Stages.field_local r.nativeWord
  obtain ⟨E1, s1, o1, f1⟩ := pair_tl a l1 R (tl a 0 (by omega)) (tl a 5 (by omega)) (tl a 6 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E (by rw [hin 0 (by omega)]; rfl)
    (hbl _ (by simp [tl_val])) (hbl _ (by simp [tl_val]))
  -- 2. the occurrence stream (160)
  obtain ⟨n, Hx, Ax, sx, ax, hn⟩ := Stream.x_request a r
  obtain ⟨kx, mx⟩ := Stages.mask0 (sx.enlarge hn)
  have s2 := Stages.stage0 mx (sST a) (sST_inj a) R E1 (by
    intro j
    by_cases j0 : j.val = 0
    · have e : sST a j = tl a 5 (by omega) := Fin.ext (by rw [sST_val, if_pos j0]; rfl)
      rw [e, o1, addCases_lt _ _ j (by omega)]
      simp [Stream.xIn, j0]
    · have hs := sST_spec a j
      have hjl := j.isLt
      rw [f1 _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), hbl _ (by omega)]
      by_cases j54 : j.val < 54
      · rw [addCases_lt _ _ j j54]
        simp [Stream.xIn, j0, Stages.pad_nil]
      · rw [addCases_ge _ _ j (by omega)]
        simp [Stages.pad_nil])
  set E2 := install (sST a) E1 (fun j => ZeroPadding.pad R (Fin.addCases Ax (fun _ : Fin 1 => List.replicate kx false) j)) with hE2
  have o2 : E2 (tl a 160 (by omega)) = ZeroPadding.pad R (PoolEntryLoop.stream (r.family a).occurrences) := by
    have e : tl a 160 (by omega) = sST a 1 := Fin.ext (by rw [sST_val]; rfl)
    rw [hE2, e, install_slot _ (sST_inj a), addCases_lt _ _ _ (by decide)]
    exact congrArg (ZeroPadding.pad R) ax
  have f2 : ∀ x : T3 a, x.val ≠ 132 + Cold.tapes a + 5 → x.val ≠ 132 + Cold.tapes a + 160 →
      (x.val < 132 + Cold.tapes a + 8 ∨ 132 + Cold.tapes a + 60 < x.val) → E2 x = E1 x := by
    intro x h1 h2 h3
    rw [hE2]
    apply install_other
    intro j hj
    have hv := congrArg Fin.val hj
    have hs := sST_spec a j
    have := j.isLt
    omega
  -- 3. `1^q` (61)
  obtain ⟨H3, l3⟩ := Stages.unframe_local (List.replicate r.q true)
  obtain ⟨E3, s3, o3, f3⟩ := pair_tl a l3 R (tl a 2 (by omega)) (tl a 61 (by omega)) (tl a 62 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E2
    (by rw [f2 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]),
          f1 _ (by simp [tl_val]) (by simp [tl_val])]; rw [hin 2 (by omega)]; rfl)
    (by rw [f2 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]),
          f1 _ (by simp [tl_val]) (by simp [tl_val])]; exact hbl _ (by simp [tl_val]))
    (by rw [f2 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]),
          f1 _ (by simp [tl_val]) (by simp [tl_val])]; exact hbl _ (by simp [tl_val]))
  -- a tape the first three stages do not touch is still `E`'s
  have g3 : ∀ x : T3 a, (x.val < 132 + Cold.tapes a + 5 ∨ 132 + Cold.tapes a + 63 ≤ x.val) → x.val ≠ 132 + Cold.tapes a + 160 →
      E3 x = E x := by
    intro x h1 h2
    rw [f3 _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), f2 _ (by omega) h2 (by omega),
      f1 _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
  -- 4. `word q` (96)
  obtain ⟨H4, l4⟩ := Stages.cmp_local r.q
  obtain ⟨E4, s4, o4, f4⟩ := pair_tl a l4 R (tl a 61 (by omega)) (tl a 96 (by omega)) (tl a 64 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E3 o3
    (by rw [g3 _ (by simp [tl_val]) (by simp [tl_val])]; exact hbl _ (by simp [tl_val]))
    (by rw [g3 _ (by simp [tl_val]) (by simp [tl_val])]; exact hbl _ (by simp [tl_val]))
  -- 5. `word q` on the template tape
  obtain ⟨H5, l5⟩ := Stages.cmp_local r.q
  obtain ⟨E5, s5, o5, f5⟩ := pair_tl a l5 R (tl a 61 (by omega)) (tT a) (tl a 65 (by omega))
    (by simp only [tl_val, tT_val]; omega) (by simp [tl_val]) (by simp only [tl_val, tT_val]; omega) E4
    (by rw [f4 _ (by simp [tl_val]) (by simp [tl_val])]; exact o3)
    (by rw [f4 _ (by simp only [tl_val, tT_val]; omega) (by simp only [tl_val, tT_val]; omega),
          g3 _ (by simp only [tT_val]; omega) (by simp only [tT_val]; omega)]; exact hbl _ (by simp only [tT_val]; omega))
    (by rw [f4 _ (by simp [tl_val]) (by simp [tl_val]),
          g3 _ (by simp [tl_val]) (by simp [tl_val])]; exact hbl _ (by simp [tl_val]))
  have g5 : ∀ x : T3 a, (x.val < 132 + Cold.tapes a + 5 ∨ 132 + Cold.tapes a + 66 ≤ x.val) → x.val ≠ 132 + Cold.tapes a + 160 →
      x.val ≠ 132 + Cold.tapes a + 96 → x.val ≠ 132 + SB a + 10 → E5 x = E x := by
    intro x h1 h2 h3 h4
    rw [f5 _ (by simp only [tT_val]; omega) (by simp only [tl_val]; omega), f4 _ (by simp only [tl_val]; omega)
      (by simp only [tl_val]; omega), g3 _ (by omega) h2]
  -- 6. `1^B` (97)
  obtain ⟨H6, l6⟩ := Stages.copy_local r.nativeWord.length
  obtain ⟨E6, s6, o6, f6⟩ := pair_tl a l6 R (tl a 3 (by omega)) (tl a 97 (by omega)) (tl a 67 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E5
    (by rw [g5 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega)]; rw [hin 3 (by omega)]; rfl)
    (by rw [g5 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega)]; exact hbl _ (by simp only [tl_val]; omega))
    (by rw [g5 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega)]; exact hbl _ (by simp only [tl_val]; omega))
  -- 7. `1^N` (68)
  obtain ⟨H7, l7⟩ := Stages.count_local (supF a r)
  obtain ⟨E7, s7, o7, f7⟩ := pair_tl a l7 R (tl a 1 (by omega)) (tl a 68 (by omega)) (tl a 69 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E6
    (by rw [f6 _ (by simp [tl_val]) (by simp [tl_val]), g5 _ (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), hin 1 (by omega)]
        change ZeroPadding.pad R (RepairOrdinary.frame (r.supportWord a)) = _
        rw [sup_eq])
    (by rw [f6 _ (by simp [tl_val]) (by simp [tl_val]), g5 _ (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
        exact hbl _ (by simp [tl_val]))
    (by rw [f6 _ (by simp [tl_val]) (by simp [tl_val]), g5 _ (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
        exact hbl _ (by simp [tl_val]))
  -- 8. `word N` (158)
  obtain ⟨H8, l8⟩ := Stages.cmp_local (supF a r).length
  obtain ⟨E8, s8, o8, f8⟩ := pair_tl a l8 R (tl a 68 (by omega)) (tl a 158 (by omega)) (tl a 71 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E7 o7
    (by rw [f7 _ (by simp [tl_val]) (by simp [tl_val]), f6 _ (by simp [tl_val])
          (by simp [tl_val]), g5 _ (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
        exact hbl _ (by simp [tl_val]))
    (by rw [f7 _ (by simp [tl_val]) (by simp [tl_val]), f6 _ (by simp [tl_val])
          (by simp [tl_val]), g5 _ (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
        exact hbl _ (by simp [tl_val]))
  have g8 : ∀ x : T3 a, (x.val < 132 + Cold.tapes a + 5 ∨ 132 + Cold.tapes a + 72 ≤ x.val) → x.val ≠ 132 + Cold.tapes a + 160 →
      x.val ≠ 132 + Cold.tapes a + 96 → x.val ≠ 132 + SB a + 10 → x.val ≠ 132 + Cold.tapes a + 97 →
      x.val ≠ 132 + Cold.tapes a + 158 → E8 x = E x := by
    intro x h1 h2 h3 h4 h5 h6
    rw [f8 _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), f7 _ (by simp only [tl_val]; omega)
      (by simp only [tl_val]; omega), f6 _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), g5 _ (by omega) h2 h3 h4]
  -- 9. the mask (159)
  obtain ⟨H9, l9⟩ := Stages.unframe_local (CloseoutRowsGateSupport.gateMembers (Packets.live (r.family a)))
  obtain ⟨E9, s9, o9, f9⟩ := pair_tl a l9 R (tl a 4 (by omega)) (tl a 159 (by omega)) (tl a 73 (by omega))
    (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val]) E8
    (by rw [g8 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]; rw [hin 4 (by omega)]; rfl)
    (by rw [g8 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
        exact hbl _ (by simp [tl_val]))
    (by rw [g8 _ (by simp [tl_val]) (by simp [tl_val]) (by simp [tl_val])
          (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]
        exact hbl _ (by simp [tl_val]))
  refine ⟨E9, ((((((((s1.seq s2).seq s3).seq s4).seq s5).seq s6).seq s7).seq s8).seq s9).enlarge (le_of_eq rfl), ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [f9 _ (by simp [tl_val]) (by simp [tl_val]), f8 _ (by simp [tl_val])
      (by simp [tl_val]), f7 _ (by simp [tl_val]) (by simp [tl_val]),
      f6 _ (by simp [tl_val]) (by simp [tl_val]), f5 _ (by simp only [tl_val, tT_val]; omega)
      (by simp [tl_val])]
    exact o4
  · rw [f9 _ (by simp [tl_val]) (by simp [tl_val]), f8 _ (by simp [tl_val])
      (by simp [tl_val]), f7 _ (by simp [tl_val]) (by simp [tl_val])]
    exact o6
  · rw [f9 _ (by simp [tl_val]) (by simp [tl_val]), o8, supF_length]
  · exact o9
  · rw [f9 _ (by simp [tl_val]) (by simp [tl_val]), f8 _ (by simp [tl_val])
      (by simp [tl_val]), f7 _ (by simp [tl_val]) (by simp [tl_val]),
      f6 _ (by simp [tl_val]) (by simp [tl_val]), f5 _ (by simp only [tl_val, tT_val]; omega)
      (by simp [tl_val]), f4 _ (by simp [tl_val]) (by simp [tl_val]),
      f3 _ (by simp [tl_val]) (by simp [tl_val])]
    exact o2
  · rw [f9 _ (by simp [tl_val]) (by simp [tl_val]), f8 _ (by simp [tl_val])
      (by simp [tl_val]), f7 _ (by simp [tl_val]) (by simp [tl_val]),
      f6 _ (by simp [tl_val]) (by simp [tl_val]), f5 _ (by simp only [tl_val, tT_val]; omega)
      (by simp [tl_val]), f4 _ (by simp [tl_val]) (by simp [tl_val])]
    exact o3
  · rw [f9 _ (by simp only [tl_val, tT_val]; omega) (by simp only [tl_val, tT_val]; omega), f8 _ (by simp only [tl_val, tT_val]; omega)
      (by simp only [tl_val, tT_val]; omega), f7 _ (by simp only [tl_val, tT_val]; omega) (by simp only [tl_val, tT_val]; omega),
      f6 _ (by simp only [tl_val, tT_val]; omega) (by simp only [tl_val, tT_val]; omega)]
    exact o5
  · intro x hk
    unfold Keep9 at hk
    rw [f9 _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), g8 _ (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]

end words

end
end NearCubicWires.SourceStart.Bank

