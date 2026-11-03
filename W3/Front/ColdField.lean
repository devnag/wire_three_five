import W3.Front.ColdLayout

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec

namespace W3.NearCubicWires.RepairSource.Outer3.Front

section DecMap
variable (pB pU : Program) (tC : ℕ) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  {mw : Outer.MWSource} {SV : Outer.SuccinctVerifier H0 G0} (F : FrontSpecD mw SV)

theorem mDEC_val (k : Fin 2) (j : Fin (CloseoutWitness.Oracle.tapes + 1)) : (mDEC pB pU tC F k j).val =
    if j.val = 0 then 14 + 11 * k.val else if j.val = 1 then 13 + 11 * k.val else if j.val = 2 then 15 + 11 * k.val
    else if j.val = 3 then 16 + 11 * k.val else if j.val = 1379 then 18 + 11 * k.val
    else if j.val = 1299 then 17 + 11 * k.val else bDEC pB.tapeCount pU.tapeCount k + j.val := by
  unfold mDEC; split_ifs <;> simp [fs, cs, blk] <;> omega

theorem mDEC_inj (k : Fin 2) : Function.Injective (mDEC pB pU tC F k) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  rw [mDEC_val, mDEC_val] at hv
  have hi : i.val < 1381 := i.isLt
  have hj : j.val < 1381 := j.isLt
  have hk := k.isLt
  unfold bDEC at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- The decoder's map misses every stream outside its field block `13 … 18 + 11k` and its private block. -/
theorem mDEC_ne (k : Fin 2) (i : Fin (NS pB pU tC F + 1))
    (h1 : i.val < 13 + 11 * k.val ∨ 19 + 11 * k.val ≤ i.val)
    (h2 : i.val < bDEC pB.tapeCount pU.tapeCount k ∨ bDEC pB.tapeCount pU.tapeCount k + 1381 ≤ i.val) :
    ∀ j, mDEC pB pU tC F k j ≠ i := fun j e => by
  have hv := congrArg Fin.val e
  rw [mDEC_val] at hv
  have hj : j.val < 1381 := j.isLt
  split_ifs at hv <;> omega

end DecMap

theorem coldInput_apply (x bits ab : List Bool) (j : Fin (CloseoutWitness.Oracle.tapes + 1)) :
    CloseoutWitness.Oracle.coldInput x bits ab j =
      if j.val = 0 then RepairOrdinary.frame x else if j.val = 1 then RepairOrdinary.frame bits
      else if j.val = 2 then RepairOrdinary.frame ab else if j.val = 3 then List.replicate (value ab) true else [] := by
  unfold CloseoutWitness.Oracle.coldInput
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.addCases_left]; rfl
  · rw [Fin.addCases_right]
    have : (Fin.natAdd CloseoutWitness.Oracle.tapes i).val = 1380 + i.val := rfl
    rw [this, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

section Field
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

/-- Field stream `i` of field `k` in the cold layout. -/
noncomputable abbrev fsC (k : Fin 2) (i : ℕ) (h : i < 11) :=
  fs (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) F.t k i h

noncomputable abbrev wbOut := mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F (progB mw SV).outputTape

noncomputable def fieldCost (b : List Bool) (ℓ m q : ℕ) : ℕ :=
  (7 * b.length + 3 + 1 + (22 * b.length + 1 + 1 + 7) + 1 + (5 * (2 * b.length + 1) + 1)) + truncCost ℓ b.length +
    (40 * m + 20) + 200 * (q + 2) + (34 * q + 7) +
    CloseoutWitness.Oracle.budget (List.replicate m true) (Codec.prefixBits b ℓ) q.bits + 10

theorem fieldP_exec (k : Fin 2) (pre b rest : List Bool) (ℓ q : ℕ) (cap : ℕ)
    (σ : WState (NSC mw SV F degree) nrW)
    (hWT : σ.st (cWT _ _ _ _) = pre ++ (Worker.Format.countWord b.length ++ b) ++ rest)
    (hWTh : σ.sh (cWT _ _ _ _) = pre.length)
    (hfresh : ∀ (i : ℕ) (h : i < 8), σ.st (fsC mw SV F degree k i (by omega)) = [] ∧
      σ.sh (fsC mw SV F degree k i (by omega)) = 0)
    (hblk : ∀ i : Fin (NSC mw SV F degree + 1), bDEC (progB mw SV).tapeCount (progU mw SV).tapeCount k ≤ i.val →
      i.val < bDEC (progB mw SV).tapeCount (progU mw SV).tapeCount k + 1381 → σ.st i = [] ∧ σ.sh i = 0)
    (hQB : σ.st (wbOut mw SV F degree) = RepairOrdinary.frame q.bits) (hQBh : σ.sh (wbOut mw SV F degree) = 0)
    (hz : ∀ r ∈ [rOP, rK, rT, rD, rU, rLC, rK2, rZ k], σ.val r = 0)
    (hL : σ.val rL = ℓ) (hM : σ.val rM = 16 * ℓ + q + 4) (hQ : σ.val rQ = q)
    (hcap : 4 * ℓ + 2 * b.length + 2 * (16 * ℓ + q + 4) + 4 * q + 100 ≤ cap) :
    ∃ τ, WXExec cap (fieldP mw SV F degree k) σ τ
        (fieldCost b ℓ (16 * ℓ + q + 4) q) ∧
      τ.st (cWT _ _ _ _) = σ.st (cWT _ _ _ _) ∧
      τ.sh (cWT _ _ _ _) = pre.length + b.length + 1 + b.length ∧
      τ.val (rZ k) = (b.drop ℓ).count true ∧
      τ.st (fsC mw SV F degree k 7 (by decide)) =
        [(decodeBooleanCircuit q (value (Codec.prefixBits b ℓ))).isSome] ∧
      τ.sh (fsC mw SV F degree k 7 (by decide)) = 0 ∧
      (∀ c : BooleanCircuit q, decodeBooleanCircuit q (value (Codec.prefixBits b ℓ)) = some c →
        τ.st (fsC mw SV F degree k 6 (by decide)) = PCPPNative.descriptor c) ∧
      τ.sh (fsC mw SV F degree k 6 (by decide)) = 0 ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i ≠ cWT _ _ _ _ →
        (i.val < 11 + 11 * k.val ∨ 19 + 11 * k.val ≤ i.val) →
        (i.val < bDEC (progB mw SV).tapeCount (progU mw SV).tapeCount k ∨
          bDEC (progB mw SV).tapeCount (progU mw SV).tapeCount k + 1381 ≤ i.val) →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ rZ k → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  classical
  have hk := k.isLt
  set FB := fsC mw SV F degree k 0 (by decide) with hFB
  set TMP := fsC mw SV F degree k 1 (by decide) with hTMP
  set FBP := fsC mw SV F degree k 2 (by decide) with hFBP
  set XP := fsC mw SV F degree k 3 (by decide) with hXP
  set QB := fsC mw SV F degree k 4 (by decide) with hQBd
  set QU := fsC mw SV F degree k 5 (by decide) with hQUd
  set DD := fsC mw SV F degree k 6 (by decide) with hDD
  set DF := fsC mw SV F degree k 7 (by decide) with hDF
  set WT := cWT (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) F.t with hWTd
  have hwb : (wbOut mw SV F degree).val = 33 + (progB mw SV).outputTape.val := by
    have := (progB mw SV).outputFresh
    simp only [wbOut, mWB, if_neg this]; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zOP, zK, zT, zD, zU, zLC, zK2, zZ⟩ := hz
  -- 1. `FB := frame b`
  have e1 := Codec.fieldRW_spec cap WT FB (by simp [Fin.ext_iff, hWTd, hFB]; omega) rOP rK (by decide) pre b rest σ hWT hWTh
    (hfresh 0 (by decide)).1 (hfresh 0 (by decide)).2 zK zOP (by omega)
  set σ1 := (σ.seth WT (pre.length + b.length + 1 + b.length)).sets FB (RepairOrdinary.frame b) with hσ1
  have s1 : ∀ i, i ≠ FB → σ1.st i = σ.st i := fun i hi => by simp [hσ1, Function.update_of_ne hi]
  have sh1 : ∀ i, i ≠ WT → σ1.sh i = σ.sh i := fun i hi => by simp [hσ1, Function.update_of_ne hi]
  have nWT : ∀ (i : ℕ) (h : i < 11), fsC mw SV F degree k i h ≠ WT := fun i h e => by
    have := congrArg Fin.val e; simp [hWTd] at this; omega
  have nFB : ∀ (i : ℕ) (h : i < 11), 0 < i → fsC mw SV F degree k i h ≠ FB := fun i h hi e => by
    have := congrArg Fin.val e; simp [hFB] at this; omega
  -- 2. truncate
  obtain ⟨τ2, e2, h2P, h2Ph, h2Z, h2se⟩ := truncField_spec cap FB TMP FBP (nFB 1 (by decide) (by decide)).symm
    (nFB 2 (by decide) (by decide)).symm (fun e => by have := congrArg Fin.val e; simp [hTMP, hFBP] at this)
    rOP rL rLC (rZ k) rD
    (by simp [List.nodup_cons, Fin.ext_iff, rOP, rL, rLC, rZ, rD]; omega) b ℓ σ1
    (by simp [hσ1]) (by rw [sh1 _ (nWT 0 (by decide))]; exact (hfresh 0 (by decide)).2)
    (by rw [s1 _ (nFB 1 (by decide) (by decide))]; exact (hfresh 1 (by decide)).1)
    (by rw [sh1 _ (nWT 1 (by decide))]; exact (hfresh 1 (by decide)).2)
    (by rw [s1 _ (nFB 2 (by decide) (by decide))]; exact (hfresh 2 (by decide)).1)
    (by rw [sh1 _ (nWT 2 (by decide))]; exact (hfresh 2 (by decide)).2)
    (by simp [hσ1, zOP]) (by simp [hσ1, hL]) (by simp [hσ1, zLC]) (by simp [hσ1, zD])
    (by simp [hσ1, zZ]; omega)
  obtain ⟨se1, se2, se3⟩ := h2se
  have nT : ∀ i, i ≠ FB → i ≠ TMP → i ≠ FBP → τ2.st i = σ1.st i ∧ τ2.sh i = σ1.sh i := fun i a b c =>
    se1 i (by simp [a, b, c])
  have v2 : ∀ r, r ≠ rZ k → τ2.val r = σ.val r := fun r hr => by
    rw [se2 r (by simpa using hr)]; simp [hσ1]
  have nZ : ∀ r : Fin nrW, (r.val < 10 ∨ 12 ≤ r.val) → r ≠ rZ k := fun r h e => by
    have := congrArg Fin.val e; simp [rZ] at this; omega
  have nF : ∀ (i j : ℕ) (hi : i < 11) (hj : j < 11), i ≠ j → fsC mw SV F degree k i hi ≠ fsC mw SV F degree k j hj :=
    fun i j hi hj h e => by have := congrArg Fin.val e; simp at this; omega
  set m := 16 * ℓ + q + 4 with hm
  -- 3. the padding word
  have e3 := framedOnes_spec cap XP rM rU rOP (by decide) (by decide) (by decide) m τ2
    (by rw [(nT XP (nF 3 0 (by decide) (by decide) (by decide)) (nF 3 1 (by decide) (by decide) (by decide)) (nF 3 2 (by decide) (by decide) (by decide))).1,
        s1 _ (nF 3 0 (by decide) (by decide) (by decide))]; exact (hfresh 3 (by decide)).1)
    (by rw [(nT XP (nF 3 0 (by decide) (by decide) (by decide)) (nF 3 1 (by decide) (by decide) (by decide)) (nF 3 2 (by decide) (by decide) (by decide))).2,
        sh1 _ (nWT 3 (by decide))]; exact (hfresh 3 (by decide)).2)
    (by rw [v2 rM (nZ rM (by decide))]; exact hM) (by rw [v2 rU (nZ rU (by decide))]; exact zU)
    (by rw [v2 rOP (nZ rOP (by decide))]; exact zOP)
    (by omega)
  set τ3 := τ2.sets XP (RepairOrdinary.frame (List.replicate m true)) with hτ3
  -- 4. `QB := frame q.bits`
  have nWB : ∀ (i : ℕ) (h : i < 11), wbOut mw SV F degree ≠ fsC mw SV F degree k i h := fun i h e => by
    have := congrArg Fin.val e; rw [hwb] at this; simp at this; omega
  have nWBT : wbOut mw SV F degree ≠ WT := fun e => by
    have := congrArg Fin.val e; rw [hwb] at this; simp [hWTd] at this; omega
  have hqb := LitDecode.bits_len_le q
  have e4 := Codec.copyRW_spec cap (wbOut mw SV F degree) QB (nWB 4 (by decide)) rOP rT rD (by decide) (by decide)
    (by decide) q.bits [] τ3
    (by rw [hτ3, WState.sets_st, Function.update_of_ne (nWB 3 (by decide)),
        (nT _ (nWB 0 (by decide)) (nWB 1 (by decide)) (nWB 2 (by decide))).1, s1 _ (nWB 0 (by decide)), hQB,
        List.append_nil])
    (by rw [hτ3, WState.sets_sh, (nT _ (nWB 0 (by decide)) (nWB 1 (by decide)) (nWB 2 (by decide))).2,
        sh1 _ nWBT, hQBh])
    (by rw [hτ3, WState.sets_st, Function.update_of_ne (nF 4 3 (by decide) (by decide) (by decide)),
        (nT QB (nF 4 0 (by decide) (by decide) (by decide)) (nF 4 1 (by decide) (by decide) (by decide)) (nF 4 2 (by decide) (by decide) (by decide))).1,
        s1 _ (nF 4 0 (by decide) (by decide) (by decide))]; exact (hfresh 4 (by decide)).1)
    (by rw [hτ3, WState.sets_sh, (nT QB (nF 4 0 (by decide) (by decide) (by decide)) (nF 4 1 (by decide) (by decide) (by decide))
        (nF 4 2 (by decide) (by decide) (by decide))).2, sh1 _ (nWT 4 (by decide))]; exact (hfresh 4 (by decide)).2)
    (by rw [hτ3, WState.sets_val, v2 rOP (nZ rOP (by decide))]; exact zOP)
    (by rw [hτ3, WState.sets_val, v2 rT (nZ rT (by decide))]; exact zT)
    (by rw [hτ3, WState.sets_val, v2 rD (nZ rD (by decide))]; exact zD) (by omega)
  set τ4 := τ3.sets QB (RepairOrdinary.frame q.bits) with hτ4
  -- 5. `QU := 1^q`
  have e5 := TabMachine.writeOnes_spec cap (X := QU) (K := rQ) (K2 := rK2) (by decide) τ4 q
    (by rw [hτ4, WState.sets_st, Function.update_of_ne (nF 5 4 (by decide) (by decide) (by decide)), hτ3, WState.sets_st,
        Function.update_of_ne (nF 5 3 (by decide) (by decide) (by decide)),
        (nT QU (nF 5 0 (by decide) (by decide) (by decide)) (nF 5 1 (by decide) (by decide) (by decide)) (nF 5 2 (by decide) (by decide) (by decide))).1,
        s1 _ (nF 5 0 (by decide) (by decide) (by decide))]; exact (hfresh 5 (by decide)).1)
    (by rw [hτ4, WState.sets_sh, hτ3, WState.sets_sh, (nT QU (nF 5 0 (by decide) (by decide) (by decide)) (nF 5 1 (by decide) (by decide) (by decide))
        (nF 5 2 (by decide) (by decide) (by decide))).2, sh1 _ (nWT 5 (by decide))]; exact (hfresh 5 (by decide)).2)
    (by rw [hτ4, WState.sets_val, hτ3, WState.sets_val, v2 rQ (nZ rQ (by decide))]; exact hQ)
    (by rw [hτ4, WState.sets_val, hτ3, WState.sets_val, v2 rK2 (nZ rK2 (by decide))]; exact zK2) (by omega)
  set τ5 := τ4.sets QU (List.replicate q true) with hτ5
  -- 6. the cold decoder
  have hpl : (Codec.prefixBits b ℓ).length = ℓ := by simp [Codec.prefixBits]
  obtain ⟨out, hr, hflag, hdesc⟩ := CloseoutWitness.Oracle.cold_run (List.replicate m true) (Codec.prefixBits b ℓ)
    q.bits (by simp; omega) (by simp [hpl]; omega) (by simp; omega)
  -- the state `τ5` off the decoder's input ports equals `σ`
  have st5 : ∀ i, i ≠ WT → i ≠ FB → i ≠ TMP → i ≠ FBP → i ≠ XP → i ≠ QB → i ≠ QU → τ5.st i = σ.st i ∧
      τ5.sh i = σ.sh i := fun i a1 a2 a3 a4 a5 a6 a7 => by
    rw [hτ5, WState.sets_st, WState.sets_sh, Function.update_of_ne a7, hτ4, WState.sets_st, WState.sets_sh,
      Function.update_of_ne a6, hτ3, WState.sets_st, WState.sets_sh, Function.update_of_ne a5,
      (nT i a2 a3 a4).1, (nT i a2 a3 a4).2, s1 i a2, sh1 i a1]
    exact ⟨rfl, rfl⟩
  have hDECv := mDEC_val (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k
  have hbDEC : 33 ≤ bDEC (progB mw SV).tapeCount (progU mw SV).tapeCount k := by unfold bDEC; omega
  have eD := mach_ready cap hr (mDEC_inj (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k) τ5 (by
      intro j
      have hv := hDECv j
      by_cases j0 : j.val = 0
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = XP := Fin.ext (by
          rw [hv, if_pos j0]; simp [hXP]; omega)
        rw [he, hτ5, WState.sets_sh, hτ4, WState.sets_sh, hτ3, WState.sets_sh,
          (nT XP (nF 3 0 (by decide) (by decide) (by decide)) (nF 3 1 (by decide) (by decide) (by decide))
            (nF 3 2 (by decide) (by decide) (by decide))).2, sh1 _ (nWT 3 (by decide))]
        exact (hfresh 3 (by decide)).2
      by_cases j1 : j.val = 1
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = FBP := Fin.ext (by
          rw [hv, if_neg j0, if_pos j1]; simp [hFBP]; omega)
        rw [he, hτ5, WState.sets_sh, hτ4, WState.sets_sh, hτ3, WState.sets_sh]; exact h2Ph
      by_cases j2 : j.val = 2
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = QB := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_pos j2]; simp [hQBd]; omega)
        rw [he, hτ5, WState.sets_sh, hτ4, WState.sets_sh, hτ3, WState.sets_sh,
          (nT QB (nF 4 0 (by decide) (by decide) (by decide)) (nF 4 1 (by decide) (by decide) (by decide))
            (nF 4 2 (by decide) (by decide) (by decide))).2, sh1 _ (nWT 4 (by decide))]
        exact (hfresh 4 (by decide)).2
      by_cases j3 : j.val = 3
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = QU := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_neg j2, if_pos j3]; simp [hQUd]; omega)
        rw [he, hτ5, WState.sets_sh, hτ4, WState.sets_sh, hτ3, WState.sets_sh,
          (nT QU (nF 5 0 (by decide) (by decide) (by decide)) (nF 5 1 (by decide) (by decide) (by decide))
            (nF 5 2 (by decide) (by decide) (by decide))).2, sh1 _ (nWT 5 (by decide))]
        exact (hfresh 5 (by decide)).2
      have hne : ∀ x ∈ [WT, FB, TMP, FBP, XP, QB, QU], mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j ≠ x := by
        intro x hx e
        have := congrArg Fin.val e
        rw [hv, if_neg j0, if_neg j1, if_neg j2, if_neg j3] at this
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hj : j.val < 1381 := j.isLt
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hWTd, hFB, hTMP, hFBP, hXP, hQBd, hQUd] at this <;>
          split_ifs at this <;> omega
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hne
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hne
      rw [(st5 _ a1 a2 a3 a4 a5 a6 a7).2]
      by_cases j79 : j.val = 1379
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = DF := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_neg j2, if_neg j3, if_pos j79]; simp [hDF]; omega)
        rw [he]; exact (hfresh 7 (by decide)).2
      by_cases j99 : j.val = 1299
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = DD := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_neg j2, if_neg j3, if_neg j79, if_pos j99]; simp [hDD]; omega)
        rw [he]; exact (hfresh 6 (by decide)).2
      have hj : j.val < 1381 := j.isLt
      exact (hblk _ (by rw [hv]; simp [j0, j1, j2, j3, j79, j99]) (by rw [hv]; simp [j0, j1, j2, j3, j79, j99])).2)
    (by
      intro j
      rw [coldInput_apply]
      have hv := hDECv j
      by_cases j0 : j.val = 0
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = XP := Fin.ext (by
          rw [hv, if_pos j0]; simp [hXP]; omega)
        rw [he, if_pos j0, hτ5, WState.sets_st, Function.update_of_ne (nF 3 5 (by decide) (by decide) (by decide)),
          hτ4, WState.sets_st, Function.update_of_ne (nF 3 4 (by decide) (by decide) (by decide)), hτ3,
          WState.sets_st, Function.update_self]
      by_cases j1 : j.val = 1
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = FBP := Fin.ext (by
          rw [hv, if_neg j0, if_pos j1]; simp [hFBP]; omega)
        rw [he, if_neg j0, if_pos j1, hτ5, WState.sets_st, Function.update_of_ne (nF 2 5 (by decide) (by decide) (by decide)),
          hτ4, WState.sets_st, Function.update_of_ne (nF 2 4 (by decide) (by decide) (by decide)), hτ3,
          WState.sets_st, Function.update_of_ne (nF 2 3 (by decide) (by decide) (by decide)), h2P]
      by_cases j2 : j.val = 2
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = QB := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_pos j2]; simp [hQBd]; omega)
        rw [he, if_neg j0, if_neg j1, if_pos j2, hτ5, WState.sets_st,
          Function.update_of_ne (nF 4 5 (by decide) (by decide) (by decide)), hτ4, WState.sets_st, Function.update_self]
      by_cases j3 : j.val = 3
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = QU := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_neg j2, if_pos j3]; simp [hQUd]; omega)
        rw [he, if_neg j0, if_neg j1, if_neg j2, if_pos j3, hτ5, WState.sets_st, Function.update_self,
          LitDecode.value_bits]
      rw [if_neg j0, if_neg j1, if_neg j2, if_neg j3]
      have hne : ∀ x ∈ [WT, FB, TMP, FBP, XP, QB, QU], mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j ≠ x := by
        intro x hx e
        have := congrArg Fin.val e
        rw [hv, if_neg j0, if_neg j1, if_neg j2, if_neg j3] at this
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        have hj : j.val < 1381 := j.isLt
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [hWTd, hFB, hTMP, hFBP, hXP, hQBd, hQUd] at this <;>
          split_ifs at this <;> omega
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hne
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hne
      rw [(st5 _ a1 a2 a3 a4 a5 a6 a7).1]
      by_cases j79 : j.val = 1379
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = DF := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_neg j2, if_neg j3, if_pos j79]; simp [hDF]; omega)
        rw [he]; exact (hfresh 7 (by decide)).1
      by_cases j99 : j.val = 1299
      · have he : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = DD := Fin.ext (by
          rw [hv, if_neg j0, if_neg j1, if_neg j2, if_neg j3, if_neg j79, if_pos j99]; simp [hDD]; omega)
        rw [he]; exact (hfresh 6 (by decide)).1
      have hj : j.val < 1381 := j.isLt
      exact (hblk _ (by rw [hv]; simp [j0, j1, j2, j3, j79, j99]) (by rw [hv]; simp [j0, j1, j2, j3, j79, j99])).1)
  set τ6 := updS (mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k) τ5 (fun _ => 0) out with hτ6
  have hDFm : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k CloseoutWitness.Oracle.flagSlot = DF :=
    Fin.ext (by
      have h79 : (CloseoutWitness.Oracle.flagSlot).val = 1379 := rfl
      rw [hDECv, h79]; simp [hDF]; omega)
  have hDDm : mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k CloseoutWitness.Oracle.descriptorSlot = DD :=
    Fin.ext (by
      have h99 : (CloseoutWitness.Oracle.descriptorSlot).val = 1299 := rfl
      rw [hDECv, h99]; simp [hDD]; omega)
  have hinj := mDEC_inj (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k
  have out6 : ∀ i, (∀ j, mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j ≠ i) →
      τ6.st i = τ5.st i ∧ τ6.sh i = τ5.sh i := fun i hi =>
    ⟨updS_st_other _ _ _ _ i hi, updS_sh_other _ _ _ _ i hi⟩
  have hval6 : ∀ r, τ6.val r = τ2.val r := fun r => by simp [hτ6, hτ5, hτ4, hτ3]
  have hWTout : ∀ j, mDEC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j ≠ WT :=
    mDEC_ne _ _ _ F k WT (by simp [hWTd]; omega) (by simp [hWTd]; omega)
  refine ⟨τ6, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4)
    (WXExec.seq e5 eD))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold fieldCost
    have := LitDecode.bits_len_le q
    omega
  · have nWT' : ∀ (i : ℕ) (h : i < 11), WT ≠ fsC mw SV F degree k i h := fun i h e => nWT i h e.symm
    rw [(out6 WT hWTout).1, hτ5, WState.sets_st, Function.update_of_ne (nWT' 5 (by decide)), hτ4, WState.sets_st,
      Function.update_of_ne (nWT' 4 (by decide)), hτ3, WState.sets_st, Function.update_of_ne (nWT' 3 (by decide)),
      (nT WT (nWT' 0 (by decide)) (nWT' 1 (by decide)) (nWT' 2 (by decide))).1, s1 WT (nWT' 0 (by decide))]
  · have nWT' : ∀ (i : ℕ) (h : i < 11), WT ≠ fsC mw SV F degree k i h := fun i h e => nWT i h e.symm
    rw [(out6 WT hWTout).2, hτ5, WState.sets_sh, hτ4, WState.sets_sh, hτ3, WState.sets_sh,
      (nT WT (nWT' 0 (by decide)) (nWT' 1 (by decide)) (nWT' 2 (by decide))).2]
    simp [hσ1]
  · rw [hval6, h2Z]; simp [hσ1, zZ]
  · rw [← hDFm, hτ6, updS_st_slot _ _ _ _ hinj, hflag, LitDecode.value_bits]
  · rw [← hDFm, hτ6, updS_sh_slot _ _ _ _ hinj]
  · intro c hc
    rw [← hDDm, hτ6, updS_st_slot _ _ _ _ hinj]
    have hq : value q.bits = q := LitDecode.value_bits q
    revert hdesc
    rw [hq]
    intro hdesc
    exact hdesc c hc
  · rw [← hDDm, hτ6, updS_sh_slot _ _ _ _ hinj]
  · intro i hi1 hi2 hi3
    have hout := mDEC_ne _ _ _ F k i (by omega) hi3
    have nfs : ∀ (a : ℕ) (h : a < 11), a < 8 → i ≠ fsC mw SV F degree k a h := fun a h ha e => by
      have := congrArg Fin.val e; simp at this; omega
    rw [(out6 i hout).1, (out6 i hout).2]
    exact st5 i hi1 (nfs 0 (by decide) (by decide)) (nfs 1 (by decide) (by decide)) (nfs 2 (by decide) (by decide))
      (nfs 3 (by decide) (by decide)) (nfs 4 (by decide) (by decide)) (nfs 5 (by decide) (by decide))
  · intro r hr; rw [hval6, v2 r hr]
  · simp [hτ6, hτ5, hτ4, hτ3]; rw [se3]; simp [hσ1]

end Field

end W3.NearCubicWires.RepairSource.Outer3.Front
