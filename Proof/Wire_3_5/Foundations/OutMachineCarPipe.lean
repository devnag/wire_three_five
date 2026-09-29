import Proof.Wire_3_5.Foundations.OutMachineCarS

/-! # The output machine carrier phase, part 6: the pipeline

The carrier phase's machine **`carM Dt el`** on the outer layout: the prologue `s1P` (`T`, the log `0^T`), the
masked stage `m1P` (`1^n`, `1^L`), the masked stage `m2M` (PA's setup, the carrier tables), the epilogue `s3P`
(`1^{|carriers|}`, every stream of `el` to `0^T`). **`carPipe`**: from the request `frame w` (everything else blank,
heads and registers `0`) at ANY capacity `cap` above the stages' needs, with `T = (|w|+2)^{Dt}` above the masked
stages' costs, the run ends with the tables, the counts, the carriers' count, the request kept, the listed streams
`0^T`, the log `0^T`, every head and register `0`. The bound hypotheses are discharged in `CarBound`.

Paper quantity of the main type: the carriers' mask tables and counts (P3:3049-3050, 3071-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.FinalPass.Out.Car
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarKit NearCubicWires.WireExponent3_5.FinalPass.Out.CarS

theorem wenc_H_z {ns nr : ℕ} (cap : ℕ) (σ : WState ns nr) (hs : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) :
    (wenc cap σ).H = fun _ => 0 := by
  funext j
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
  · rw [wenc_H_s, hs]
  · rw [wenc_H_c]
  · rw [wenc_H_r, hv]

/-- **The carrier phase's machine**. -/
noncomputable def carM (Dt : ℕ) (el : List (Fin (NS + 1))) :=
  Composition.machine (s1P Dt).toProg.compile
    (Composition.machine (RecoveryFocus.machine mdock (MaskedReset.machine m1P.toProg.compile selIn))
      (Composition.machine (RecoveryFocus.machine mdock (MaskedReset.machine CarM2.m2M selIn))
        (s3P Dt el).toProg.compile))

/-- The two masked stages' capacities. -/
def c1Of (n : ℕ) : ℕ := Lof n + 4 * n + 4
def c2Of (N n : ℕ) : ℕ := 2 * N + n + Lof n + 20

/-- The pipeline's step bound. -/
noncomputable def pipeCost (cap Dt N n : ℕ) (codes : List ℕ) {n' : ℕ} (carriers : List (Stars.Carrier n')) : ℕ :=
  s1Cost cap Dt N + 1 + (2 * m1Cost (c1Of n) n + 2 + 1 + (2 * CarM2.m2Bnd (c2Of N n) n (Lof n) codes carriers + 2 + 1 +
    s3Cost cap Dt N 2))

theorem two_pow_nbl (n : ℕ) : 2 ^ (natBitLength n + 1) ≤ 4 * n + 4 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 h)
    rw [show Nat.log 2 n + 1 + 1 = Nat.log 2 n + 2 by omega, pow_add]
    omega

theorem nbl_le (n : ℕ) : natBitLength n ≤ n + 1 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 h)
    have h2 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
    omega

theorem inner_st (σ : OSt) (i : Fin (DS + 1)) : (CarL.inner σ).st i = σ.st (oS i) := rfl

theorem kept_not_erased (kp : List (Fin (DS + 1))) (j : Fin (DS + 1)) (hj : j ∈ kp) : oS j ∉ eraseOf kp := by
  intro h
  obtain ⟨j', hj', e⟩ := (mem_eraseOf kp _).1 h
  exact hj' (oS_inj e ▸ hj)

theorem log_not_erased (kp : List (Fin (DS + 1))) : oLog ∉ eraseOf kp := by
  intro h
  obtain ⟨j', _, e⟩ := (mem_eraseOf kp _).1 h
  exact oS_ne_log j' e

/-- **The pipeline**: from the request (everything else blank, heads and registers `0`), at any capacity above the
stages' needs, with `T` above the masked stages' costs. -/
theorem carPipe (Dt : ℕ) (kp : List (Fin (DS + 1))) (hk6 : CarM2.s6 ∈ kp) (hkIn : sIN ∈ kp)
    (n : ℕ) (mb : Bool) (codes : List ℕ) (carriers : List (Stars.Carrier n)) (tl : List Bool)
    (ha : codes.length ≤ 4) (hk : carriers.length ≤ 2) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ Lof n)
    (σ : OSt) (hIn : σ.st (oS sIN) = frame (reqW n mb codes (carriers.map Stars.Carrier.code) tl))
    (hbl : ∀ i, i ≠ oS sIN → σ.st i = []) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hc : σ.cell = false)
    (cap : ℕ) (hnN : n ≤ (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length)
    (hxN : ∀ x ∈ codes, (RepairRepresentation.natWord x).length ≤ (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length)
    (hyN : ∀ y ∈ carriers.map Stars.Carrier.code,
      (RepairRepresentation.natWord y).length ≤ (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length)
    (hT1 : m1Cost (c1Of n) n ≤ ((reqW n mb codes (carriers.map Stars.Carrier.code) tl).length + 2) ^ Dt)
    (hT2 : Lof n + CarM2.m2Bnd (c2Of (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length n) n (Lof n) codes
      carriers ≤ ((reqW n mb codes (carriers.map Stars.Carrier.code) tl).length + 2) ^ Dt)
    (hc1 : c1Of n ≤ cap) (hc2 : c2Of (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length n ≤ cap)
    (hTc : ((reqW n mb codes (carriers.map Stars.Carrier.code) tl).length + 2) ^ Dt ≤ cap)
    (hNc : 2 * (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length + 2 ≤ cap) :
    ∃ (τ : OSt) (m : ℕ), m ≤ pipeCost cap Dt (reqW n mb codes (carriers.map Stars.Carrier.code) tl).length n codes
        carriers ∧
      Step (carM Dt (eraseOf kp)) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      (∀ k : Fin 2, sCar k 5 ∈ kp → τ.st (oS (sCar k 5)) = List.replicate (carCnt carriers k.val) true) ∧
      (∀ k : Fin 2, sCar k 3 ∈ kp → τ.st (oS (sCar k 3)) = Seams.carTab carriers k.val) ∧
      τ.st (oS CarM2.s6) = List.replicate carriers.length true ∧ τ.st (oS sIN) = σ.st (oS sIN) ∧
      (∀ i, i ∈ eraseOf kp ∨ i = oLog →
        τ.st i = List.replicate (((reqW n mb codes (carriers.map Stars.Carrier.code) tl).length + 2) ^ Dt) false) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ r, τ.val r = 0) ∧ τ.cell = false := by
  set w := reqW n mb codes (carriers.map Stars.Carrier.code) tl with hw
  set N := w.length with hN
  set T := (N + 2) ^ Dt with hT
  have hnL : n ≤ Lof n := by
    unfold Lof; have := Nat.le_self_pow (show 26 ≠ 0 by decide) (n + 1); omega
  have hLof2 : 2 ≤ n + Lof n := by
    unfold Lof; have := Nat.one_le_pow 26 (n + 1) (Nat.succ_pos n); omega
  -- 1. the prologue
  have e1 := s1_spec cap Dt w σ hIn hsh hv (hbl _ (fun e => oS_ne_log sIN e.symm)) hTc hNc
  set σ1 := σ.sets oLog (List.replicate T false) with hσ1
  have st1 := Exec.step (WExec.exec cap e1)
  have h1H : (wenc cap σ1).H = fun _ => 0 := wenc_H_z cap σ1 (by simp [hσ1, hsh]) (by simp [hσ1, hv])
  have h0H : (wenc cap σ).H = fun _ => 0 := wenc_H_z cap σ hsh hv
  rw [h0H, h1H] at st1
  -- 2. `1^n`, `1^L`
  have hi1 : ∀ i : Fin (DS + 1), i ≠ sIN → (CarL.inner σ1).st i = [] := fun i hi => by
    show σ1.st (oS i) = []
    simp only [hσ1, WState.sets_st, Function.update_of_ne (oS_ne_log i)]
    exact hbl _ (fun e => hi (oS_inj e))
  have hIn1 : (CarL.inner σ1).st sIN = frame w := by
    show σ1.st (oS sIN) = frame w
    simp only [hσ1, WState.sets_st, Function.update_of_ne (oS_ne_log sIN)]; exact hIn
  have e2 := m1_spec (c1Of n) n mb codes (carriers.map Stars.Carrier.code) tl (CarL.inner σ1) hIn1 (fun i => hsh _)
    (fun r => hv r) (hi1 sNT (by decide)) (hi1 sLT (by decide)) (by unfold c1Of; omega)
    (by have := two_pow_nbl n; unfold c1Of; omega)
  set τ1 := (((CarL.inner σ1).seth sIN (PrimAsm.ParseNat.stp true * (RepairRepresentation.natWord n).length)).sets sLT
    (List.replicate (Lof n) true)).sets sNT (List.replicate n true) with hτ1
  have hτ1v : ∀ r, τ1.val r = 0 := fun r => hv r
  have st2 := step_up _ _ (c1Of n) cap hc1 (CarL.inner σ1) τ1 (fun r => hv r) hτ1v (Exec.step (WExec.exec (c1Of n) e2))
  rw [wenc_H_z cap (CarL.inner σ1) (fun i => hsh _) (fun r => hv r)] at st2
  have md1 := maskDock m1P.toProg.compile cap T (m1Cost (c1Of n) n) σ1 τ1 (by simp [hσ1]) hT1 st2
    (fun i hi => by simp [hτ1, Function.update_of_ne hi, CarL.inner, hσ1, hsh]) hτ1v
  set σ2 := outerZ τ1 (List.replicate T false) with hσ2
  -- 3. the carrier tables
  have hτ1st : ∀ i : Fin (DS + 1), τ1.st i = if i = sNT then List.replicate n true else if i = sLT then
      List.replicate (Lof n) true else (CarL.inner σ1).st i := by
    intro i
    simp only [hτ1, WState.sets_st, WState.seth_st, Function.update_apply]
  have hτ1len : ∀ i : Fin (DS + 1), i ≠ sIN → (τ1.st i).length ≤ Lof n := by
    intro i hi
    rw [hτ1st]
    split_ifs
    · simpa using hnL
    · simp
    · rw [hi1 i hi]; simp
  have hbs : ∀ i, Blank (CarL.inner σ2) (symTrip i) := by
    intro i
    have h0 : ∀ j : Fin 1789, (CarL.inner σ2).st (sSym i j) = [] := by
      intro j
      show σ2.st (oS (sSym i j)) = []
      rw [hσ2, outerZ_st_oS, hτ1st, if_neg (sSym_ne_low i j sNT (by decide)), if_neg (sSym_ne_low i j sLT (by decide))]
      exact hi1 _ (sSym_ne_low i j sIN (by decide))
    exact ⟨h0 0, rfl, h0 1, rfl, h0 2, rfl⟩
  have hbc : ∀ k : Fin 2, ∀ j : Fin 1357, (CarL.inner σ2).st (sCar k j) = [] := by
    intro k j
    show σ2.st (oS (sCar k j)) = []
    rw [hσ2, outerZ_st_oS, hτ1st, if_neg (sCar_ne_low k j sNT (by decide)), if_neg (sCar_ne_low k j sLT (by decide))]
    exact hi1 _ (sCar_ne_low k j sIN (by decide))
  have hIn2 : (CarL.inner σ2).st sIN = frame w := by
    rw [inner_st, hσ2, outerZ_st_oS, hτ1st, if_neg (show sIN ≠ sNT by decide), if_neg (show sIN ≠ sLT by decide)]
    exact hIn1
  have hNT2 : (CarL.inner σ2).st sNT = List.replicate n true := by
    rw [inner_st, hσ2, outerZ_st_oS, hτ1st, if_pos rfl]
  have hLT2 : (CarL.inner σ2).st sLT = List.replicate (Lof n) true := by
    rw [inner_st, hσ2, outerZ_st_oS, hτ1st, if_neg (show sLT ≠ sNT by decide), if_pos rfl]
  have hc2' : c2Of N n ≤ cap := hc2
  obtain ⟨τ2, m2, s2, b2, o2, hh2, v2, in2, s62, cl2, z2⟩ := CarM2b.m2_spec2 (c2Of N n) n (Lof n) mb codes carriers
    tl (CarL.inner σ2) ha hk hLX hLof2 hIn2 (fun _ => rfl) hNT2 hLT2 hbs hbc (fun r => hτ1v r)
    (by have := nbl_le n; unfold c2Of; omega)
    (by have := two_pow_nbl codes.length; unfold c2Of Lof; omega)
    (by have := two_pow_nbl carriers.length; unfold c2Of Lof; omega)
    (fun x hx => by have := hxN x hx; unfold c2Of; omega)
    (fun y hy => by have := hyN y hy; unfold c2Of; omega) (by unfold c2Of; omega)
  have st3 := step_up _ _ (c2Of N n) cap hc2' (CarL.inner σ2) τ2 (fun r => hτ1v r) v2 s2
  rw [wenc_H_z cap (CarL.inner σ2) (fun _ => rfl) (fun r => hτ1v r)] at st3
  have hm2T : m2 ≤ T := by omega
  have md2 := maskDock CarM2.m2M cap T m2 σ2 τ2 (by simp [hσ2]) hm2T st3 hh2 v2
  set σ3 := outerZ τ2 (List.replicate T false) with hσ3
  -- 4. the epilogue
  have hread : ∀ k : Fin 2, wbit σ3 (oS (sCar k 0)) = decide (k.val < carriers.length) := by
    intro k
    unfold wbit
    rw [show σ3.sh (oS (sCar k 0)) = 0 from rfl, hσ3, outerZ_st_oS, z2 k]
    split_ifs with h
    · rw [PrimAsm.Data.frame_natWord_head]; simp [h]
    · simp [h]; rfl
  have hLen : ∀ i ∈ eraseOf kp, (σ3.st i).length ≤ T := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := (mem_eraseOf kp i).1 hi
    rw [hσ3, outerZ_st_oS]
    have hjIn : j ≠ sIN := fun e => hj (e ▸ hkIn)
    have hlen := PrimAsm.Shell.Step.len s2 (sTape (nr := DR) j) (Lof n) (by rw [wenc_H_s]; show (0 : ℕ) ≤ _; omega)
      (by rw [wenc_A_s, inner_st, hσ2, outerZ_st_oS]; exact hτ1len j hjIn)
    rw [wenc_A_s] at hlen
    omega
  have h6_3 : σ3.st (oS CarM2.s6) = [] := by
    rw [hσ3, outerZ_st_oS, s62, inner_st, hσ2, outerZ_st_oS, hτ1st, if_neg (show CarM2.s6 ≠ sNT by decide),
      if_neg (show CarM2.s6 ≠ sLT by decide)]
    exact hi1 _ (show CarM2.s6 ≠ sIN by decide)
  have e4 := s3_spec cap Dt kp hk6 w (decide (0 < carriers.length)) (decide (1 < carriers.length)) σ3
    (by rw [hσ3, outerZ_st_oS, in2]; exact hIn2) (fun _ => rfl) (fun r => v2 r) (hread 0) (hread 1) h6_3 hLen hTc hNc
  have st4 := Exec.step (WExec.exec cap e4)
  rw [wenc_H_z cap σ3 (fun _ => rfl) (fun r => v2 r)] at st4
  set cnt := (decide (0 < carriers.length)).toNat + (decide (1 < carriers.length)).toNat with hcntdef
  set σ4 := setsAll (σ3.sets (oS CarM2.s6) (List.replicate cnt true)) (eraseOf kp) (List.replicate T false) with hσ4
  have h4H : (wenc cap σ4).H = fun _ => 0 := wenc_H_z cap σ4 (fun _ => rfl) (fun r => v2 r)
  rw [h4H] at st4
  have hcnt : cnt = carriers.length := by
    rw [hcntdef]
    rcases (by omega : carriers.length = 0 ∨ carriers.length = 1 ∨ carriers.length = 2) with h | h | h <;> simp [h]
  have hcnt2 : cnt ≤ 2 := by rw [hcnt]; exact hk
  have keep4 : ∀ j ∈ kp, j ≠ CarM2.s6 → σ4.st (oS j) = τ2.st j := by
    intro j hj hj6
    simp only [hσ4, setsAll, if_neg (kept_not_erased kp j hj), WState.sets_st,
      Function.update_of_ne (fun e => hj6 (oS_inj e)), hσ3, outerZ_st_oS]
  refine ⟨σ4, s1Cost cap Dt N + 1 + (2 * m1Cost (c1Of n) n + 2 + 1 + (2 * m2 + 2 + 1 + s3Cost cap Dt N cnt)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl, fun r => v2 r, ?_⟩
  · unfold pipeCost
    have : s3Cost cap Dt N cnt ≤ s3Cost cap Dt N 2 := by unfold s3Cost; omega
    omega
  · rw [h0H, h4H]
    exact Step.seq st1 (Step.seq md1 (Step.seq md2 st4))
  · intro k hk5
    rw [keep4 _ hk5 (by fin_cases k <;> decide)]
    exact (o2 k).2
  · intro k hk3
    rw [keep4 _ hk3 (by fin_cases k <;> decide)]
    exact (o2 k).1
  · simp only [hσ4, setsAll, if_neg (kept_not_erased kp _ hk6), WState.sets_st, Function.update_self, hcnt]
  · rw [keep4 _ hkIn (by decide), in2, hIn2, hIn]
  · rintro i (hi | rfl)
    · simp only [hσ4, setsAll, if_pos hi]
    · simp only [hσ4, setsAll, if_neg (log_not_erased kp), WState.sets_st,
        Function.update_of_ne (fun e => oS_ne_log CarM2.s6 e.symm), hσ3, outerZ_st_log]
  · show τ2.cell = false
    rw [cl2]; exact hc

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarPipe
