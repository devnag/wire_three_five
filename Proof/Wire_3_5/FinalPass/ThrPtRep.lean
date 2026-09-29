import Proof.Wire_3_5.FinalPass.MajMain

/-! # S2 (THR per point), part 1: a population's report VALUE in a register (P3:1449-1477, 3170-3178)

Stage 8 of a THR row reads the digit lists' reports `t_d^± = report(Z)` as numbers (`repWord`), while stage 5
(`mainI`, lifted as the majority machine's `mainM`) decides `[report(Z) = s]`. `repM` runs, on the majority
machine's layout (`MSt`): `M` read from the table (`setupM`); for `s = 1, …, M`: the compared state extended to
`unary s` (`extendU`), stage 5, and `R += s` when it answers `1` (`addSM`); then the compared state cleared
(`cleanupM`) and the cell set to `false`. Since `reportRef ≤ M` and at most one `s` matches, `R` ends at the report
(`accT_M`). Main declarations: `accT`, `accT_eq`, `reportRef_le`, `repBody`, `repLoop_spec`, **`repM_spec`**.
Paper quantity: the digit list's report `t_d^± = report(Z)` (row:thr-reported, P3:2615-2629). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.ListEval NearCubicWires.WireExponent3_5.FinalPass.Maj

/-! ## The accumulated value -/

section Acc
variable (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool)

/-- `Σ_{s' ≤ s} s'·[report = s']`. -/
def accT : ℕ → ℕ
  | 0 => 0
  | s + 1 => accT s + if reportRef M J W row Z = s + 1 then s + 1 else 0

theorem accT_eq : ∀ s, accT M J W row Z s =
    if 1 ≤ reportRef M J W row Z ∧ reportRef M J W row Z ≤ s then reportRef M J W row Z else 0
  | 0 => by
    simp only [accT]
    split_ifs with h <;> omega
  | s + 1 => by
    simp only [accT, accT_eq s]
    split_ifs <;> omega

theorem accT_le (s : ℕ) : accT M J W row Z s ≤ s := by
  rw [accT_eq]; split_ifs with h <;> omega

theorem reportRef_le : reportRef M J W row Z ≤ M := by
  unfold reportRef
  split
  · split <;> omega
  · omega

theorem accT_M : accT M J W row Z M = reportRef M J W row Z := by
  rw [accT_eq]
  have := reportRef_le M J W row Z
  split_ifs with h <;> omega

theorem levelWord_len : M + 1 ≤ (levelWord M J W row).length := by
  simp [levelWord, unary]

end Acc

variable (cap : ℕ)

/-! ## One state -/

/-- **One state**: `unary s` extended, `S` counted, stage 5, `R += S` on a match, `MC` counted down. -/
def repBody : MProg :=
  .seq extendU (.seq (.inc mS) (.seq mainM (.seq (.ifr mC (.seq addSM (.dec mC)) .skip) (.dec mMC))))

/-- One state's step bound. -/
def repBodyCost (M c5 : ℕ) : ℕ := 30 * M + 40 + mainCost c5

theorem m_cell (x : MSt) (b : Bool) : x.w.setc b = { x with cell := b }.w := rfl

/-- **Stage 5 at a phase record, the point read-alike**: `Maj.mainM_spec` with the point stream only READING like
`frame Z` (a longer blank tail allowed). -/
theorem mainM_spec' (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool) (s : ℕ) (x : MSt)
    (hpt : ∀ p, readTapeBit x.pt p = readTapeBit (frame Z) p) (ht5 : x.t5 = levelWord M J W row) (ht5h : x.t5h = 0)
    (hss : ∀ p, readTapeBit x.ss p = readTapeBit (unary s) p) (hssh : x.ssh = 0) (hc : x.c = 0)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hs : s ≤ M) (hcap : capOf M J W row Z.length ≤ cap) :
    WExec cap mainM x.w { x with c := if reportRef M J W row Z = s then 1 else 0, cell := false }.w
      (mainCost (capOf M J W row Z.length)) := by
  have h := mainI_spec M J W row Z s x.cell hrows hs
  have hrel : LiftRelR fsM frM (streams M J W row Z s) x.w (blank x.cell) := by
    refine ⟨fun i => ?_, fun i p => ?_, fun r => ?_, rfl⟩
    · fin_cases i
      · rfl
      · show x.t5h = 0; exact ht5h
      · show x.ssh = 0; exact hssh
    · fin_cases i
      · show readTapeBit x.pt p = readTapeBit (frame Z) p; exact hpt p
      · show readTapeBit x.t5 p = readTapeBit (levelWord M J W row) p; rw [ht5]
      · exact hss p
    · fin_cases r <;> first | rfl | (show x.c = 0; exact hc)
  obtain ⟨ω, hω, hrel', hout⟩ := RExec.liftR _ _ cap hcap fsM fsM_inj frM frM_inj h x.w hrel
  refine WExec.cast cap hω ?_ (le_refl _)
  apply WState.eq
  · funext i
    fin_cases i
    · exact hrel'.sh 0
    · exact (hrel'.sh 1).trans ht5h.symm
    · exact (hrel'.sh 2).trans hssh.symm
    · exact hout.2.1 3 fsM_ne3
  · exact hout.1
  · funext r
    fin_cases r
    all_goals first
      | exact hrel'.val 0
      | exact hrel'.val 1
      | exact hrel'.val 2
      | exact hrel'.val 3
      | exact hrel'.val 4
      | exact hrel'.val 5
      | exact hrel'.val 6
      | exact hrel'.val 7
      | exact hrel'.val 8
      | exact hrel'.val 9
      | exact hrel'.val 10
      | exact hrel'.val 11
      | exact hrel'.val 12
      | exact hrel'.val 13
      | exact hrel'.val 14
      | exact hout.2.2 _ (frM_ne _ (by decide) _)
  · exact hrel'.cell

theorem repBody_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hcap : capOf M J W row Z.length ≤ cap)
    (s k m : ℕ) (hs : s + 1 ≤ M) (hm1 : m + 1 ≤ M) (x : MSt) (hpt : ∀ p, readTapeBit x.pt p = readTapeBit (frame Z) p)
    (ht5 : x.t5 = levelWord M J W row) (ht5h : x.t5h = 0) (hss : x.ss = List.replicate s true ++ List.replicate k false) (hssh : x.ssh = 0)
    (hc0 : x.c = 0) (hS : x.s = s) (hr : x.r = accT M J W row Z s) (hmc : x.mc = m + 1) (h2 : x.t2 = 0) :
    WExec cap repBody x.w
      { x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := s + 1,
               r := accT M J W row Z (s + 1), mc := m, cell := false }.w
      (repBodyCost M (capOf M J W row Z.length)) := by
  have hlw := levelWord_len M J W row
  have hc4 : 4 * M + 8 ≤ cap := by unfold capOf at hcap; omega
  have hacc := accT_le M J W row Z s
  obtain ⟨pt, t5, t5h, ss, ssh, ft, fth, c, a, v, s0, r, mc, tt, f, t2, cell⟩ := x
  simp only at hpt ht5 ht5h hss hssh hc0 hS hr hmc h2
  subst t5 t5h ss ssh c s0 r mc t2
  -- 1: the compared state
  have s1 := extendU_spec cap s k ⟨pt, levelWord M J W row, 0, List.replicate s true ++ List.replicate k false,
    0, ft, fth, 0, a, v, s, accT M J W row Z s, m + 1, tt, f, 0, cell⟩ rfl rfl (by omega)
  -- 2: the state register
  have s2 := WExec.inc (cap := cap) mS (⟨pt, levelWord M J W row, 0,
    List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth, 0, a, v, s, accT M J W row Z s, m + 1,
    tt, f, 0, cell⟩ : MSt).w (show s < cap by omega)
  rw [m_s] at s2
  -- 3: stage 5
  have s3 := mainM_spec' cap M J W row Z (s + 1) ⟨pt, levelWord M J W row, 0,
    List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth, 0, a, v, s + 1, accT M J W row Z s,
    m + 1, tt, f, 0, cell⟩ hpt rfl rfl (fun p => read_ss (s + 1) (k - 1) p) rfl rfl hrows hs hcap
  -- 4: the match
  obtain ⟨n4, hn4, s4⟩ : ∃ n4, n4 ≤ 18 * s + 24 ∧ WExec cap (.ifr mC (.seq addSM (.dec mC)) .skip)
      (⟨pt, levelWord M J W row, 0, List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth,
        if reportRef M J W row Z = s + 1 then 1 else 0, a, v, s + 1, accT M J W row Z s, m + 1, tt, f, 0, false⟩ :
        MSt).w
      (⟨pt, levelWord M J W row, 0, List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth,
        0, a, v, s + 1, accT M J W row Z (s + 1), m + 1, tt, f, 0, false⟩ : MSt).w n4 := by
    by_cases hm : reportRef M J W row Z = s + 1
    · simp only [hm, if_true]
      have a1 := addS_spec cap (⟨pt, levelWord M J W row, 0,
        List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth, 1, a, v, s + 1,
        accT M J W row Z s, m + 1, tt, f, 0, false⟩ : MSt) rfl (by simp only; omega) (by simp only; omega)
      have a2 := WExec.dec (cap := cap) mC (⟨pt, levelWord M J W row, 0,
        List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth, 1, a, v, s + 1,
        accT M J W row Z s + (s + 1), m + 1, tt, f, 0, false⟩ : MSt).w (show 1 ≤ cap by omega)
      rw [m_c] at a2
      have ha : accT M J W row Z (s + 1) = accT M J W row Z s + (s + 1) := by simp [accT, hm]
      rw [ha]
      refine ⟨_, ?_, WExec.ifrT (show (1 : ℕ) ≠ 0 by omega) (WExec.seq a1 a2)⟩
      simp only
      omega
    · simp only [hm, if_false]
      have ha : accT M J W row Z (s + 1) = accT M J W row Z s := by simp [accT, hm]
      rw [ha]
      refine ⟨_, ?_, WExec.ifrF (show (0 : ℕ) = 0 from rfl) (WExec.skip _)⟩
      omega
  -- 5: the states left
  have s5 := WExec.dec (cap := cap) mMC (⟨pt, levelWord M J W row, 0,
    List.replicate (s + 1) true ++ List.replicate (k - 1) false, 0, ft, fth, 0, a, v, s + 1, accT M J W row Z (s + 1),
    m + 1, tt, f, 0, false⟩ : MSt).w (show m + 1 ≤ cap by omega)
  rw [m_mc] at s5
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5)))) rfl
    (by unfold repBodyCost; omega)

/-! ## The states -/

theorem repLoop_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hcap : capOf M J W row Z.length ≤ cap) :
    ∀ (m s k : ℕ) (x : MSt), s + m = M → (∀ p, readTapeBit x.pt p = readTapeBit (frame Z) p) → x.t5 = levelWord M J W row → x.t5h = 0 →
      x.ss = List.replicate s true ++ List.replicate k false → x.ssh = 0 → x.c = 0 → x.s = s →
      x.r = accT M J W row Z s → x.mc = m → x.t2 = 0 →
      ∃ b, WExec cap (.whr mMC repBody) x.w
        { x with ss := List.replicate M true ++ List.replicate (k - m) false, s := M,
                 r := accT M J W row Z M, mc := 0, cell := b }.w
        (m * (repBodyCost M (capOf M J W row Z.length) + 2) + 1)
  | 0, s, k, x, hsm, _, _, _, hss, _, _, hS, hr, hmc, _ => by
    refine ⟨x.cell, WExec.cast cap (WExec.whrF (show x.w.val mMC = 0 from hmc)) ?_ (by omega)⟩
    obtain ⟨pt, t5, t5h, ss, ssh, ft, fth, c, a, v, s0, r, mc, tt, f, t2, cell⟩ := x
    simp only at hS hr hmc hss ⊢
    subst s0 mc ss r
    simp only [Nat.add_zero] at hsm
    subst hsm
    simp
  | m + 1, s, k, x, hsm, hpt, ht5, ht5h, hss, hssh, hc0, hS, hr, hmc, h2 => by
    have b1 := repBody_spec cap M J W row Z hrows hcap s k m (by omega) (by omega) x hpt ht5 ht5h hss hssh hc0 hS hr hmc h2
    obtain ⟨b, ih⟩ := repLoop_spec M J W row Z hrows hcap m (s + 1) (k - 1)
      { x with ss := List.replicate (s + 1) true ++ List.replicate (k - 1) false, s := s + 1,
               r := accT M J W row Z (s + 1), mc := m, cell := false } (by omega) hpt ht5 ht5h rfl hssh hc0 rfl rfl rfl h2
    refine ⟨b, WExec.cast cap (WExec.whrT (show x.w.val mMC ≠ 0 by show x.mc ≠ 0; omega) b1 ih) ?_
      (by rw [Nat.succ_mul]; omega)⟩
    have e : k - 1 - m = k - (m + 1) := by omega
    rw [e]

/-! ## The report value -/

/-- **The report value** of the framed population on stream `0` against the table on stream `1`, into `R`. -/
def repM : MProg := .seq setupM (.seq (.whr mMC repBody) (.seq cleanupM (.setc false)))

/-- `repM`'s step bound. -/
def repCost (M c5 : ℕ) : ℕ :=
  ((11 * M + 7) + 1 + (5 * (M + 1) + 1)) + 1 + ((M * (repBodyCost M c5 + 2) + 1) + 1 +
    (((3 * M + 1) + 1 + ((9 * M + 1) + 1 + (5 * M + 1))) + 1 + 1))

/-- **`repM`'s run**: from the framed population `Z`, the table `levelWord M J W row` (rows of `Z`'s length), a
compared state all `false`, and `S = R = MC = C = T2 = 0` (the point only READING like `frame Z`), the result register holds `reportRef M J W row Z`; the
compared state is all `false` again, the cell `false`, everything else as it was. -/
theorem repM_spec (M J : ℕ) (W : ℕ → ℕ) (row : ℕ → List Bool) (Z : List Bool)
    (hrows : ∀ j ≤ J, (row j).length = Z.length) (hcap : capOf M J W row Z.length ≤ cap) (k : ℕ) (x : MSt)
    (hpt : ∀ p, readTapeBit x.pt p = readTapeBit (frame Z) p) (ht5 : x.t5 = levelWord M J W row) (ht5h : x.t5h = 0)
    (hss : x.ss = List.replicate k false) (hssh : x.ssh = 0) (hc0 : x.c = 0) (hS : x.s = 0) (hr : x.r = 0)
    (hmc : x.mc = 0) (h2 : x.t2 = 0) :
    WExec cap repM x.w
      { x with ss := List.replicate M false ++ List.replicate (k - M) false, r := reportRef M J W row Z,
               cell := false }.w (repCost M (capOf M J W row Z.length)) := by
  have hlw := levelWord_len M J W row
  have hc4 : 4 * M + 8 ≤ cap := by unfold capOf at hcap; omega
  obtain ⟨pt, t5, t5h, ss, ssh, ft, fth, c, a, v, s0, r, mc, tt, f, t2, cell⟩ := x
  simp only at hpt ht5 ht5h hss hssh hc0 hS hr hmc h2
  subst t5 t5h ss ssh c s0 r mc t2
  have s1 := setup_spec cap M J W row ⟨pt, levelWord M J W row, 0, List.replicate k false, 0, ft, fth, 0, a, v,
    0, 0, 0, tt, f, 0, cell⟩ rfl rfl rfl (by omega)
  obtain ⟨b, s2⟩ := repLoop_spec cap M J W row Z hrows hcap M 0 k ⟨pt, levelWord M J W row, 0,
    List.replicate k false, 0, ft, fth, 0, a, v, 0, 0, M, tt, f, 0, cell⟩ (by omega) hpt rfl rfl (by simp) rfl rfl
    rfl rfl rfl rfl
  have s3 := cleanup_spec cap M (k - M) (⟨pt, levelWord M J W row, 0,
    List.replicate M true ++ List.replicate (k - M) false, 0, ft, fth, 0, a, v, M, accT M J W row Z M, 0, tt, f, 0,
    b⟩ : MSt) rfl rfl rfl (by omega)
  have s4 := WExec.setc (cap := cap) false (⟨pt, levelWord M J W row, 0,
    List.replicate M false ++ List.replicate (k - M) false, 0, ft, fth, 0, a, v, 0, accT M J W row Z M, 0, tt, f, 0,
    b⟩ : MSt).w
  rw [m_cell] at s4
  rw [accT_M] at s2 s3 s4
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) rfl (by unfold repCost; omega)

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
