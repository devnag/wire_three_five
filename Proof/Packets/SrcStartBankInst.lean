import Proof.Packets.SrcStartBankRun

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceStart.Bank
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation RepairSource.VerifierDecoding P1Closure SupplierPipeline SupplierEstimator
open RepairSource RepairSource.CloseoutFinal PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
noncomputable section

section inst
variable (a : DecompositionAlgorithm)

/-- The capacity `Pc = SourcePoolCapacity.value |nativeWord| q` (also the pad width the bank needs). -/
def PcOf (r : Request) : ℕ := PCJ6e421fabe2aa4155_SourcePoolCapacity.value r.nativeWord.length r.q

/-- The start bank's cost (exactly the composed `Step`'s). -/
def bankCost (r : Request) : ℕ :=
  (((wordsCost a r + 1 + (2*(r.nativeWord.length + r.q)+6)) + 1 +
    PCPSerializerCapacity.Power.budget 3 16777216 (r.nativeWord.length + r.q)) + 1 +
    (2*PCJ6e421fabe2aa4155_SourcePoolProduced.budget r.nativeWord.length r.q (r.family a).occurrences.length+2)) + 1 + 1

theorem heads_eq (r : Request) (H : T3 a → ℕ)
    (ph : ∀ (i : ℕ) (hi : i < 132), H (bk a i (by omega)) =
      PCJ6e421fabe2aa4155_SourcePoolInitialize.head (r.family a).occurrences.length ⟨i, hi⟩)
    (pz : ∀ x : T3 a, 132 ≤ x.val → H x = 0) :
    (fun i => (dirMV a i).apply (H i)) =
      Fin.addCases (Fin.addCases (PCJ6fbdd6f776f6447d_Source.PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences
        r.nativeWord.length (r.nativeWord.length + r.q + 1) []).heads (PCJ6fbdd6f776f6447d_Source.PoolCold.coldHeads a))
        (fun _ : Fin (kOf a) => 0) := by
  have hct := tapes_ge a
  funext x
  by_cases hx1 : x.val < 132 + Cold.tapes a
  · rw [addCases_lt _ _ x hx1]
    by_cases hx0 : x.val < 132
    · rw [addCases_lt _ _ _ hx0, start_heads]
      have e : x = bk a x.val (by omega) := Fin.ext rfl
      have hd : dirMV a x = HeadMove.stay := by unfold dirMV; rw [if_neg (by omega)]
      rw [hd]
      simp only [HeadMove.apply]
      have h := ph x.val hx0
      rw [← e] at h
      exact h
    · rw [addCases_ge _ _ _ (by show 132 ≤ x.val; omega), pz x (by omega)]
      simp only [PCJ6fbdd6f776f6447d_Source.PoolCold.coldHeads, Cold.heads, dirMV]
      by_cases h10 : x.val = 132 + SB a + 10
      · rw [if_pos h10, if_neg (by omega), if_pos (by omega)]
        rfl
      · rw [if_neg h10]
        have n10 : ¬ (x.val - 132 = SB a + 10) := by omega
        by_cases hS : x.val - 132 = SB a
        · rw [if_pos hS]
          rfl
        · rw [if_neg hS, if_neg n10]
          rfl
  · rw [addCases_ge _ _ x (by omega), pz x (by omega)]
    have hd : dirMV a x = HeadMove.stay := by unfold dirMV; rw [if_neg (by omega)]
    rw [hd]
    rfl

theorem bank_run (r : Request) (R : ℕ) (E : T3 a → List Bool) (hR : PcOf r ≤ R)
    (hin : ∀ j, E (Fin.natAdd (132 + Cold.tapes a) (inPortB a j)) = ZeroPadding.pad R (SourceFactorSel.Item4.inWord a r j))
    (hbl : ∀ x, (∀ j, Fin.natAdd (132 + Cold.tapes a) (inPortB a j) ≠ x) → E x = List.replicate R false) :
    ∃ E' : T3 a → List Bool,
      Step (bankM a) (bankCost a r) (fun _ => 0) E
        (Fin.addCases (Fin.addCases (PCJ6fbdd6f776f6447d_Source.PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences
          r.nativeWord.length (r.nativeWord.length + r.q + 1) []).heads (PCJ6fbdd6f776f6447d_Source.PoolCold.coldHeads a))
          (fun _ : Fin (kOf a) => 0)) E' ∧
      (∀ i : Fin (132 + Cold.tapes a), E' (Fin.castAdd (kOf a) i) = ZeroPadding.pad R
        (Fin.addCases (PCJ6fbdd6f776f6447d_Source.PoolCold.start (Packets.live (r.family a)) (r.family a).occurrences
          r.nativeWord.length (r.nativeWord.length + r.q + 1) []).tapes
          (PCJ6fbdd6f776f6447d_Source.PoolCold.coldData a (PcOf r) r.q) i)) ∧
      (∀ j, E' (Fin.natAdd (132 + Cold.tapes a) (inPortB a j)) = E (Fin.natAdd (132 + Cold.tapes a) (inPortB a j))) := by
  have hct := tapes_ge a
  have hsmall := PCJ6e421fabe2aa4155_SourcePoolCapacity.small_bounds r.nativeWord.length r.q
  have hq2 : r.q + 2 ≤ R := le_trans hsmall.1 hR
  have hin' : ∀ (j : ℕ) (h : j < 5), E (tl a j (by omega)) = ZeroPadding.pad R (SourceFactorSel.Item4.inWord a r ⟨j, h⟩) := by
    intro j h
    rw [← natAdd_in a ⟨j, h⟩]
    exact hin ⟨j, h⟩
  have hbl' : ∀ x : T3 a, (x.val < 132 + Cold.tapes a ∨ 132 + Cold.tapes a + 5 ≤ x.val) → E x = List.replicate R false := by
    intro x hx
    apply hbl x
    intro j e
    have hv := congrArg Fin.val e
    simp only [Fin.val_natAdd, inPortB_val] at hv
    have := j.isLt
    omega
  -- the words
  obtain ⟨E9, s9, w96, w97, w158, w159, w160, w61, wT, k9⟩ := words_run a r R E hin' hbl'
  -- `1^(B+q)`
  obtain ⟨E10, s10, z74, zf⟩ := z_run a r.nativeWord.length r.q R E9 w97 w61
    (by rw [k9 _ (by unfold Keep9; simp only [tl_val]; omega)]; exact hbl' _ (by simp only [tl_val]; omega))
    (by rw [k9 _ (by unfold Keep9; simp only [tl_val]; omega)]; exact hbl' _ (by simp only [tl_val]; omega))
  -- `1^Pc`
  obtain ⟨E11, s11, pT, pf⟩ := pc_run a r.nativeWord.length r.q R E10 z74 (by
    intro j j0
    have hj := j.isLt
    simp only [RepairSource.ProjectionNormalization.DimensionPolynomial.tapes] at hj
    have hs := sPC_spec a j
    rw [zf _ (by omega) (by omega), k9 _ (by unfold Keep9; omega), hbl' _ (by omega)])
  -- the producer
  have hn := occ_le_nw a r
  have hs : (PoolEntryLoop.stream (r.family a).occurrences).length ≤
      PCJ6e421fabe2aa4155_SourcePoolCapacity.value r.nativeWord.length r.q := (stream_le_nw a r).trans (nw_le_value _ _)
  obtain ⟨H12, E12, s12, ph, pz, pt, pfr⟩ := pr_run a (Packets.live (r.family a)) r.nativeWord.length
    (r.family a).occurrences.length (PoolEntryLoop.stream (r.family a).occurrences) hn hs R hR E11
    (by rw [pf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      zf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]; exact w96)
    (by rw [pf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      zf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]; exact w97)
    (by rw [pf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      zf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]; exact w158)
    (by rw [pf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      zf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]; exact w159)
    (by rw [pf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      zf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega)]; exact w160)
    (by
      intro p p0 p1 p62 p63 p64
      have hp := p.isLt
      have hs := sPR_spec a p
      rw [pf _ (by omega) (by omega) (by omega), zf _ (by omega) (by omega), k9 _ (by unfold Keep9; omega), hbl' _ (by omega)])
  -- the template head
  have s13 := mv_run a H12 E12
  refine ⟨E12, ((((s9.seq s10).seq s11).seq s12).seq s13).congr (heads_eq a r H12 ph pz) rfl, ?_, ?_⟩
  · intro i
    by_cases hi0 : i.val < 132
    · rw [addCases_lt _ _ i hi0, start_tapes]
      have e : Fin.castAdd (kOf a) i = bk a i.val (by omega) := Fin.ext rfl
      rw [e, pt i.val hi0]
    · rw [addCases_ge _ _ i (by omega)]
      have hiv : (Fin.castAdd (kOf a) i).val = i.val := rfl
      have hil := i.isLt
      rw [pfr _ (by omega) (by omega)]
      simp only [PCJ6fbdd6f776f6447d_Source.PoolCold.coldData, Cold.data, base_eq]
      by_cases hB : i.val = 132 + SB a + 14
      · have e : Fin.castAdd (kOf a) i = tP a := Fin.ext (by rw [hiv, hB]; rfl)
        rw [e, pT, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        rfl
      · by_cases hT : i.val = 132 + SB a + 10
        · have e : Fin.castAdd (kOf a) i = tT a := Fin.ext (by rw [hiv, hT]; rfl)
          rw [e, pf _ (by simp only [tT_val]; omega) (by simp only [tT_val]; omega) (by simp only [tT_val]; omega),
            zf _ (by simp only [tT_val]; omega) (by simp only [tT_val]; omega), wT,
            if_neg (by omega), if_pos (by omega)]
          exact pad_template R r.q hq2
        · rw [pf _ (by omega) (by omega) (by omega), zf _ (by omega) (by omega), k9 _ (by unfold Keep9; omega),
            hbl' _ (by omega)]
          have n10 : ¬ (i.val - 132 = SB a + 10) := by omega
          have n14 : ¬ (i.val - 132 = SB a + 14) := by omega
          by_cases hS : i.val - 132 = SB a
          · rw [if_pos hS]
            exact (Stages.pad_nil R).symm
          · rw [if_neg hS, if_neg n10, if_neg n14]
            exact (Stages.pad_nil R).symm
  · intro j
    have hj := j.isLt
    rw [natAdd_in, pfr _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      pf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega) (by simp only [tl_val]; omega),
      zf _ (by simp only [tl_val]; omega) (by simp only [tl_val]; omega), k9 _ (by unfold Keep9; simp only [tl_val]; omega)]

def sb : SourceFactorSel.Item4.StartBank a (kOf a) where
  states := _
  machine := bankM a
  cost := bankCost a
  need := PcOf
  B := fun r => r.nativeWord.length
  w := fun r => r.nativeWord.length + r.q + 1
  Pc := PcOf
  inPort := inPortB a
  inPort_inj := inPortB_inj a
  hw := fun _ => by omega
  hqw := fun _ => by omega
  hb := fun r => bottom_le_nw a r
  hm := fun r g hg => PCJ6e421fabe2aa4155_SourcePoolAdmissions.magnitude g (bottom_le_nw a r g hg)
  hqP := fun r => by
    have := (PCJ6e421fabe2aa4155_SourcePoolCapacity.small_bounds r.nativeWord.length r.q).1
    unfold PcOf
    omega
  hi := fun r => by
    have h := PoolGen.segment_bound (Packets.live (r.family a)) (r.family a).occurrences r.nativeWord.length (occ_le_nw a r)
      (bottom_le_nw a r)
    have h2 : PcOf r ≤ 1000 * (PcOf r + 2) ^ 2 := by nlinarith
    exact h.trans h2
  run := fun r R E hR hin hbl => bank_run a r R E hR hin hbl

end inst

end
end NearCubicWires.SourceStart.Bank

