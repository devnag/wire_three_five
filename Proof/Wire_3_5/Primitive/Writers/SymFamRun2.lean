import Proof.Wire_3_5.Primitive.Writers.PopSetupSpecB2
import Proof.Wire_3_5.Primitive.Writers.SymFam

/-! # POP setup: the SYM writer at one call of the family over `PopSetupSpecB2`

`SymFamRun` (`symWM`, `sym_fam_run`) with the POP setup `Q : PopSetupSpecB2 W` (the need's measure reads the row
offset `r4`): the POP rows' bound `pn_block2` (`pn_block` with `+ r4` in the need's measure, `r4 ≤ 4·2^k ≤ K_A·Q`),
the machine `symWM2`, the run **`sym_fam_run2`**.

Paper quantity of the main type: the SYM tape `symTape` (C4's `BAT` word of the call, P3:3011-3016). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline

/-! ## The run at one call, within `costS` -/

section Blocks
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The POP rows' needs and pipeline bounds over `PopSetupSpecB2`** (`sym_ready`'s `hPN`). -/
theorem pn_block2 {W : PrimT.WalkBank.WalkBankProducer} (Q : PopSetup.PopSetupSpecB2 W) (h : SB)
    (hQ1 : Q.Kn = h.Qn) (hQ2 : Q.Dn = h.Qd)
    (hpp : ∀ (cap : ℕ) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
      (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length),
      PopPipe.popPipeBound cap Pl e L r4 G off (popMlab r4 G off L) (popLw Pl L) (popR Pl r4 G off L)
          (popCp Pl r4 G off L) (popRW Pl) (popRW Pl) sgn s hlabs ≤
        h.Kp * (cap + Pl.M + Pl.B + Pl.errExp + L + r4 + G + off + Fintype.card Pl.FlatSeed +
          (8 * L + 2) ^ (3 * lbP Pl + 1) + 2) ^ h.Dp * 2 ^ (h.Dp * Pl.errExp))
    {n a : ℕ} (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (Pl : FlatListParams) {L k kh T BS Qv KQ cap BPf BPp : ℕ}
    (hPe : Pl.errExp = L + 5) (hPM : Pl.M ≤ 4 * (n + 1) ^ 26) (hPB : Pl.B ≤ 8192 * BS)
    (hcP2 : 2 * Fintype.card Pl.FlatSeed ≤ KQ)
    (hx0 : (carriers.map (·.length)).getD 0 0 ≤ (n + 1) ^ 26)
    (hx1 : (carriers.map (·.length)).getD 1 0 ≤ (n + 1) ^ 26)
    (hy : ∀ j, (cyOf Cs).getD j 0 ≤ (n + 1) ^ 26) (hys : (cyOf Cs).sum ≤ 4 * (n + 1) ^ 26) (h2k : 2 * kh = k)
    (hY : ∀ Lp, Lp ≤ (n + 1) ^ 26 → (8 * Lp + 2) ^ (3 * lbP Pl + 1) ≤ 2 ^ T) (aT : 2 ^ T ≤ KQ)
    (a26 : 8 * (n + 1) ^ 26 ≤ KQ) (aBS : 8192 * BS ≤ KQ) (akk : 8 * 2 ^ k ≤ KQ) (aL : L + 5 ≤ KQ)
    (hml : ∀ row, row < 2 ^ k → (2 * (2 * row) + 4) * pbdG Cs carriers ≤ KQ)
    (hcapQ : h.Qn * (30 * KQ) ^ h.Qd ≤ cap) (hDpm : 2 ^ (h.Dp * (L + 5)) ≤ 32 ^ h.Dp * Qv)
    (hBPp : BPp = h.Kp * (cap + 30 * KQ) ^ h.Dp * (32 ^ h.Dp * Qv)) :
    ∀ i : ℕ, i < a → ∀ (e' : Pl.FlatSeed) (row : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1)), row < 2 ^ (2 * kh) →
      Q.need Pl (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) ≤ cap ∧
      ∀ hl : 4 * pbdL Cs i ≤ (sliceLabs (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)).length,
        PopPipe.popPipeBound cap Pl e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i)
          (popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i)) (popLw Pl (pbdL Cs i))
          (popR Pl (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popCp Pl (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i))
          (popRW Pl) (popRW Pl) sgn s hl ≤ BPf + BPp := by
  intro i hi e' row sgn s hrow
  rw [h2k] at hrow
  have hL' : pbdL Cs i ≤ (n + 1) ^ 26 := by unfold pbdL SymDec.sel4; split_ifs <;> exact hy _
  have hO' : pbdOff Cs carriers i ≤ 7 * (n + 1) ^ 26 := by
    have := hy 0; have := hy 1; have := hy 2
    unfold pbdOff SymDec.sel4; split_ifs <;> omega
  have hG' : pbdG Cs carriers ≤ 8 * (n + 1) ^ 26 := by unfold pbdG; omega
  have hmlK := hml row hrow
  have hY' := hY _ hL'
  have hmlb : popMlab (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) (pbdL Cs i) ≤ 3 * KQ := by
    unfold popMlab; omega
  refine ⟨?_, fun hl => ?_⟩
  · have hq := Q.need_le Pl (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i)
    rw [hQ1, hQ2] at hq
    refine le_trans hq (le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)) hcapQ)
    rw [hPe]
    omega
  · have hb := hpp cap Pl e' (pbdL Cs i) (2 * (2 * row)) (pbdG Cs carriers) (pbdOff Cs carriers i) sgn s hl
    refine le_trans hb ?_
    rw [hPe]
    calc _ ≤ h.Kp * (cap + 30 * KQ) ^ h.Dp * (32 ^ h.Dp * Qv) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)) hDpm
      _ = BPp := hBPp.symm
      _ ≤ BPf + BPp := Nat.le_add_left _ _

end Blocks

/-- **The SYM writer's machine over `PopSetupSpecB2`** at the gate and the base constants. -/
noncomputable def symWM2 (l : Literals) (F : GateFree l) (W : PrimT.WalkBank.WalkBankProducer)
    (FS : FiltSetup.FiltSetupSpec5 W) (Q : PopSetup.PopSetupSpecB2 W) (h : SB) :=
  ShellS.shellMS W (SymDec.decW W FS (SymDec.pbW W Q.toPopSetupSpec) F.cr F.filterErrDeg (gateCParams1 l).ζ (gateCδ1 l)
    (gateCap l)) h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA
    (NumsXS.numsMS h.KF F.cr (gateCParams1 l).ζ (gateCδ1 l) (gateCap l) 26 6)

section Run
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetup NearCubicWires.WireExponent3_5.PrimAsm.PopLink
open NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The SYM writer at one call of the family over `PopSetupSpecB2`**, within the budget `costS …` at the base
constants. -/
theorem sym_fam_run2 (l : Literals) (F : GateFree l) (kclk coef A a0 : ℕ) (ha0 : a0 ≤ kclk + 1)
    (W : PrimT.WalkBank.WalkBankProducer) (FS : FiltSetup.FiltSetupSpec5 W) (Q : PopSetup.PopSetupSpecB2 W) (h : SB)
    (hFS1 : FS.Cn = h.Cn) (hFS2 : FS.Dn = h.Dn) (hFS3 : FS.Cb = h.Cb) (hFS4 : FS.Db = h.Db)
    (hQ1 : Q.Kn = h.Qn) (hQ2 : Q.Dn = h.Qd) (hQ3 : Q.Kb = h.Qb) (hQ4 : Q.Db = h.Qe)
    (hwb : ∀ n, CallSize.wordBound 26 26 2 n ≤ h.Cw * (n + 1) ^ h.Dw)
    (hnw : ∀ n, PrimT.C4GateSym.needW n ≤ h.Cnw * (n + 1) ^ h.Dnw)
    (hfp : ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
      FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
        h.Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ h.Df * (L + 2) ^ (h.Df * (P.errExp + 1)))
    (hpp : ∀ (cap : ℕ) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
      (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length),
      PopPipe.popPipeBound cap Pl e L r4 G off (popMlab r4 G off L) (popLw Pl L) (popR Pl r4 G off L)
          (popCp Pl r4 G off L) (popRW Pl) (popRW Pl) sgn s hlabs ≤
        h.Kp * (cap + Pl.M + Pl.B + Pl.errExp + L + r4 + G + off + Fintype.card Pl.FlatSeed +
          (8 * L + 2) ^ (3 * lbP Pl + 1) + 2) ^ h.Dp * 2 ^ (h.Dp * Pl.errExp))
    (hZ : h.Z = CallIndexR.capZR l) (hZm : h.Zm = 80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)
    (hCsp : h.Csp = gateCsp l) (hJ : h.J = SymSizes.schedJ l) (hcX : h.cX = SymSizes.cXg l)
    (hKL : h.KLam = SymSizes.KLam l) (hK : h.capK = CallIndexR.capK F.cr) (hcr : h.cr = F.cr)
    (hfe : h.fe = F.filterErrDeg) (hcM : h.cM = CapNum.cMain (gateCap l) .sym)
    {n a : ℕ} (ha : a ≤ 4) (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ) (hcall : (callInputs l F kclk coef A a0 ha0).Call (symReq n a ha Cs carriers translation))
    (hs : (callInputs l F kclk coef A a0 ha0).StarAt n) :
    WriterIfaceJ.WriterRun (symWM2 l F W FS Q h)
      (ShellT.costS h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA (symReq n a ha Cs carriers translation).word.length n
        (Data.coreCost a Cs carriers (UnaryCalc.value h.D2 h.C2 n) (UnaryCalc.value h.D2 h.C2 n))
        (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
          (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2)
        (UnaryCalc.value h.D h.Kr (2 ^ NumsXS.mS h.KF ((callInputs l F kclk coef A a0 ha0).starParams n hs)
          (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6) - 1)
        (NumsXS.mS h.KF ((callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l) (gateZeta_lt l)
          (gateCδ1 l) (gateCap l) 26 6))
      (ShellX.shellInX W.x h.D h.D2 h.Dv 1) (ShellX.shellOutX W.x h.D h.D2 h.Dv 1)
      (symReq n a ha Cs carriers translation).word
      (WriterIface.symTape (callInputs l F kclk coef A a0 ha0) hs Cs carriers) := by
  -- the base constants' inequalities
  obtain ⟨cw, cc2, c13, csb, cfb, ctot, ccr, csp, cj, c40, ccm, c1, c3, c6, c7⟩ := h.cA_ge
  obtain ⟨kdw, kd2, k26, k1, kz, ksb, kfb, ktot, kfe, kfe4, ksa, kcsp, kzm, k208, k260, kdf, kdp⟩ := h.KF_ge
  obtain ⟨dcap1, dcapDn, dcapQd, kcap1, kcapN, kcapQ⟩ := h.cap_ge
  obtain ⟨hD3, hDb, hDq, hDp, hDf, hD1⟩ := h.D_ge
  obtain ⟨dC2, dD2⟩ := h.data_ge
  rw [hfe] at kfe kfe4 kdf
  -- the call's envelopes
  have hwl : (symReq n a ha Cs carriers translation).word.length ≤ h.Cw * (n + 1) ^ h.Dw :=
    le_trans (CallSize.gate_word_length_le l F kclk coef A a0 ha0 _ hcall) (hwb n)
  obtain ⟨hk2, hdesc, henv⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a0 ha0 n a ha Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a0 ha0 hs
  obtain ⟨L, hLd⟩ : ∃ x, x = Nat.clog 2 (n + 2) := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hLd]; exact Nat.clog_pos (by norm_num) (by omega)
  have hLn : L ≤ n + 2 := hLd ▸ clog_le_self _
  have hLq : Ledger.Lq n = L := by rw [hLd]; rfl
  -- the SYM cap
  obtain ⟨BS, hBSd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n := ⟨_, rfl⟩
  have hBS : BS ≤ h.capK * (n + 2) ^ h.Z := by rw [hBSd, hK, hZ]; exact sfam_capS l F kclk coef A a0 ha0 n
  have hBS1 : 1 ≤ BS := by rw [hBSd]; exact ((gate0 l F).budget kclk coef A a0 ha0).capOf_pos .sym n
  -- the dimension `m = k + L + K_F L² + T`
  have hm := sfam_mS l F kclk coef A a0 ha0 hs h.KF
  obtain ⟨k, hkd⟩ : ∃ x, x = ((gate0 l F).budget kclk coef A a0 ha0).kOf n := ⟨_, rfl⟩
  have h2kh := HashFam.fam_two_kh l F kclk coef A a0 ha0 hs
  rw [← hkd] at hm h2kh
  obtain ⟨kh, hkhd⟩ : ∃ x, x = SeedFix.callKh ((callInputs l F kclk coef A a0 ha0).starParams n hs) := ⟨_, rfl⟩
  have h2k : 2 * kh = k := by rw [hkhd]; exact h2kh
  rw [← hLd, ← hBSd] at hm
  obtain ⟨T, hTd⟩ : ∃ x, x = SymSizes.tSOf BS 26 6 L := ⟨_, rfl⟩
  rw [← hTd] at hm
  obtain ⟨m, hmd⟩ : ∃ x, x = NumsXS.mS h.KF ((callInputs l F kclk coef A a0 ha0).starParams n hs) (gateZeta_pos l)
      (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 := ⟨_, rfl⟩
  rw [← hmd] at hm
  obtain ⟨Qv, hQd⟩ : ∃ x, x = 2 ^ m + 1 := ⟨_, rfl⟩
  have hQv1 : 1 ≤ Qv := by rw [hQd]; exact Nat.le_add_left 1 _
  have hmQ : 2 ^ m ≤ Qv := by rw [hQd]; exact Nat.le_succ _
  have hKFm : h.KF * L ^ 2 ≤ m := by rw [hm]; exact le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)
  have hLL : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) _
  -- atoms below `K_A·Q`
  obtain ⟨KQ, hKQ⟩ : ∃ x, x = 2 ^ h.cA * Qv := ⟨_, rfl⟩
  have toKQ : ∀ {X c d a' : ℕ}, X ≤ 2 ^ c * ((n + 2) ^ d * 2 ^ (a' * L) * 2 ^ k * 2 ^ T) → c ≤ h.cA →
      d + a' ≤ h.KF → X ≤ KQ := by
    intro X c d a' hX hc hda
    rw [hLd] at hX
    have := atomQ (cA := h.cA) (KF := h.KF) hX hc hda
    rw [← hLd, ← hm, ← hQd, ← hKQ] at this
    exact this
  have toKQc : ∀ {X c d : ℕ}, X ≤ 2 ^ c * (n + 2) ^ d → c ≤ h.cA → d ≤ h.KF → X ≤ KQ := by
    intro X c d hX hc hd
    apply toKQ (a' := 0) _ hc (le_of_eq_of_le (Nat.add_zero d) hd)
    refine le_trans hX (Nat.mul_le_mul_left _ ?_)
    rw [zero_mul, pow_zero, mul_one]
    exact le_trans (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow) (Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
  have toKQp : ∀ {X K d : ℕ}, X ≤ K * (n + 2) ^ d → Nat.clog 2 K ≤ h.cA → d ≤ h.KF → X ≤ KQ := by
    intro X K d hX hK hd
    exact toKQc (le_trans hX (Nat.mul_le_mul_right _ (le_two_pow_clog K))) hK hd
  have p12 : ∀ d, (n + 1) ^ d ≤ (n + 2) ^ d := fun d => Nat.pow_le_pow_left (Nat.le_succ _) d
  have pp1 : ∀ d, 1 ≤ (n + 2) ^ d := fun d => Nat.one_le_pow _ _ (Nat.succ_pos _)
  have aW : (symReq n a ha Cs carriers translation).word.length ≤ KQ :=
    toKQp (le_trans hwl (Nat.mul_le_mul_left _ (p12 _))) cw kdw
  obtain ⟨V, hVd⟩ : ∃ x, x = UnaryCalc.value h.D2 h.C2 n := ⟨_, rfl⟩
  have aV : V ≤ KQ := toKQp (le_of_eq_of_le (hVd.trans (value_eq _ _ _)) (Nat.mul_le_mul_left _ (p12 _))) cc2 kd2
  have a26 : 8 * (n + 1) ^ 26 ≤ KQ :=
    toKQc (c := 3) (d := 26) (le_of_le_of_eq (Nat.mul_le_mul_left 8 (p12 26)) (by norm_num)) c3 k26
  have an : n + 2 ≤ KQ := toKQc (c := 0) (d := 1) (by rw [pow_one, pow_zero, one_mul]) (Nat.zero_le _) k1
  have aBS : 8192 * BS ≤ KQ := by
    apply toKQc (c := 13 + Nat.clog 2 h.capK) (d := h.Z) _ c13 kz
    calc 8192 * BS ≤ 8192 * (h.capK * (n + 2) ^ h.Z) := Nat.mul_le_mul_left _ hBS
      _ ≤ 8192 * (2 ^ Nat.clog 2 h.capK * (n + 2) ^ h.Z) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_two_pow_clog _))
      _ = 2 ^ (13 + Nat.clog 2 h.capK) * (n + 2) ^ h.Z := by rw [pow_add]; norm_num; ring
  have akk : 8 * 2 ^ k ≤ KQ := by
    apply toKQ (c := 3) (d := 0) (a' := 0) _ c3 (Nat.zero_le _)
    simp only [pow_zero, zero_mul, one_mul]
    have : 1 ≤ 2 ^ T := Nat.one_le_two_pow
    calc 8 * 2 ^ k = 2 ^ 3 * (2 ^ k * 1) := by norm_num
      _ ≤ 2 ^ 3 * (2 ^ k * 2 ^ T) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
  have aT : 2 ^ T ≤ KQ := by
    apply toKQ (c := 0) (d := 0) (a' := 0) _ (Nat.zero_le _) (Nat.zero_le _)
    simp only [pow_zero, zero_mul, one_mul]
    exact Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  -- the call's counts
  have hcx : ∀ c ∈ carriers.map (·.length), c ≤ (n + 1) ^ 26 := by
    intro c hc
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc
    exact (henv X hX).1
  have hcy : ∀ c ∈ cyOf Cs, c ≤ (n + 1) ^ 26 := by
    intro c hc
    unfold cyOf at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact Data.symGates_len_le (Cs i) _ (hdesc i)
  have hxs : (carriers.map (·.length)).sum ≤ 2 * (n + 1) ^ 26 := by
    have h1 := List.sum_le_card_nsmul (carriers.map (·.length)) ((n + 1) ^ 26) hcx
    rw [List.length_map, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ hk2)
  have hys : (cyOf Cs).sum ≤ 4 * (n + 1) ^ 26 := by
    have h1 := List.sum_le_card_nsmul (cyOf Cs) ((n + 1) ^ 26) hcy
    rw [cyOf_length, smul_eq_mul] at h1
    exact le_trans h1 (Nat.mul_le_mul_right _ ha)
  have hx0 : (carriers.map (·.length)).getD 0 0 ≤ (n + 1) ^ 26 := getD_le hcx 0
  have hx1 : (carriers.map (·.length)).getD 1 0 ≤ (n + 1) ^ 26 := getD_le hcx 1
  have hy : ∀ j, (cyOf Cs).getD j 0 ≤ (n + 1) ^ 26 := fun j => getD_le hcy j
  have hy4 := sum_getD4 (cyOf Cs) (by rw [cyOf_length]; exact ha)
  have hN26 : (n + 1) ^ 26 + 1 ≤ (n + 2) ^ 26 := CallIndex.succ_le_N26 n
  have hp26 := p12 26
  -- the seeds
  obtain ⟨sb, hsbd⟩ : ∃ x, x = (SymDec.gP n BS (F.filterErrDeg * Ledger.Lq n)).seedBits := ⟨_, rfl⟩
  have hsb : sb ≤ h.aSb * L + h.cSb := by
    have := sb_le n BS h.capK h.Z h.fe hBS
    rw [hfe, ← hsbd, ← hLd] at this
    unfold SB.aSb SB.cSb; rw [hfe]
    exact le_of_le_of_eq this (by ring)
  have p2sb : 2 ^ sb ≤ 2 ^ h.cSb * 2 ^ (h.aSb * L) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (le_of_le_of_eq hsb (Nat.add_comm _ _))
  have asb : 2 * 2 ^ sb ≤ KQ :=
    toKQ (c := h.cSb + 1) (d := 0) (a' := h.aSb)
      (atomE2 (le_of_le_of_eq (Nat.mul_le_mul_left 2 p2sb) (by rw [pow_succ, pow_zero]; ring))) csb ksb
  have pfbG : ∀ {M B : ℕ}, M ≤ 4 * (n + 1) ^ 26 → B ≤ 8192 * BS →
      2 ^ FlatNums.fbv M B (L + 5) ≤ 2 ^ h.cFb * 2 ^ (h.aFb * L) := by
    intro M B hM hB
    have hf := fbv_fam h hM (le_trans hB (Nat.mul_le_mul_left _ hBS))
    rw [← hLd] at hf
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (le_of_le_of_eq hf (Nat.add_comm _ _))
  have afbG : ∀ {M B : ℕ}, M ≤ 4 * (n + 1) ^ 26 → B ≤ 8192 * BS → 2 * 2 ^ FlatNums.fbv M B (L + 5) ≤ KQ := by
    intro M B hM hB
    exact toKQ (c := h.cFb + 1) (d := 0) (a' := h.aFb)
      (atomE2 (le_of_le_of_eq (Nat.mul_le_mul_left 2 (pfbG hM hB)) (by rw [pow_succ, pow_zero]; ring))) cfb kfb
  have h8192 : carriers.length * 4096 ≤ 8192 := le_trans (Nat.mul_le_mul_right 4096 hk2) (by norm_num)
  have hbV : SymDec.bV carriers.length BS ≤ 8192 * BS := by
    unfold SymDec.bV; exact Nat.mul_le_mul_right _ h8192
  have afb := afbG hys hbV
  -- the joint states and the units per state
  have ast : SymDec.stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤
      (n + 2) ^ 208 := by
    have hb : ∀ j, (cyOf Cs).getD j 0 + 1 ≤ (n + 2) ^ 26 := fun j => le_trans (Nat.add_le_add_right (hy j) 1) hN26
    exact le_of_le_of_eq (stV_le (hb 0) (hb 1) (hb 2) (hb 3))
      ((pow_mul (n + 2) 26 8).symm.trans (congrArg _ (by norm_num)))
  have aeu : SymDec.euV (cyOf Cs).sum carriers.length a ≤ 2 ^ 7 * (n + 2) ^ 26 := euV_le hys hk2 ha hp26 (pp1 26)
  have atot : SymDec.totV n BS (F.filterErrDeg * Ledger.Lq n) (cyOf Cs).sum carriers.length (Ledger.Lq n) kh a
      ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤ KQ := by
    unfold SymDec.totV
    rw [← hsbd, hLq, h2k]
    exact toKQ (prod5 p2sb (pfbG hys hbV) ast (le_refl _) aeu) ctot ktot
  -- the SYM tape's states
  have hsbF : ((callInputs l F kclk coef A a0 ha0).filterParams .sym n).seedBits = sb := by rw [hsbd, hBSd]; rfl
  have hPe : (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).errExp = L + 5 := by
    show 1 * Nat.clog 2 (n + 2) + 5 = L + 5
    rw [one_mul, hLd]
  have hPM : (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).M ≤ 4 * (n + 1) ^ 26 := by
    rw [← cy_sum (callInputs l F kclk coef A a0 ha0) Cs carriers]; exact hys
  have hPB : (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).B ≤ 8192 * BS := by
    show carriers.length * (4096 * ((gate0 l F).budget kclk coef A a0 ha0).capOf .sym n) ≤ 8192 * BS
    rw [← hBSd, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h8192
  have hcardF : Fintype.card (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).FlatSeed ≤
      2 ^ h.cFb * 2 ^ (h.aFb * L) := by
    rw [← FlatNums.card_eq, hPe]; exact pfbG hPM hPB
  have aNT : Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers * (2 ^ kh) ^ 2 *
      ((carriers.length + 2 * a) * ((symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).M + 3) + 2) ≤
      KQ := by
    unfold Enum.symNT
    have h1 : Fintype.card (GapSeed ((callInputs l F kclk coef A a0 ha0).filterParams .sym n)) ≤
        2 ^ h.cSb * 2 ^ (h.aSb * L) := by rw [card_gapSeed, hsbF]; exact p2sb
    have h3 : ∏ j, (Primitive.symM ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs j + 1) *
        (Primitive.symM ((callInputs l F kclk coef A a0 ha0).starParams n hs) Cs j + 1) ≤ (n + 2) ^ 208 := by
      refine le_of_le_of_eq (CallIndex.prod_le_pow4 ha _ (N := n + 2) (X := 52) (pp1 1 |>.trans (le_of_eq (pow_one _)))
        (fun j => ?_)) (congrArg _ (by norm_num))
      have hb2 : (Cs j).bottomCount + 1 ≤ (n + 2) ^ 26 :=
        le_trans (Nat.add_le_add_right (CallIndex.bottomCount_le (Cs j) (hdesc j)) 1) hN26
      show ((Cs j).bottomCount + 1) * ((Cs j).bottomCount + 1) ≤ (n + 2) ^ 52
      exact le_of_le_of_eq (Nat.mul_le_mul hb2 hb2) ((pow_add (n + 2) 26 26).symm.trans (congrArg _ (by norm_num)))
    have h4 : (2 ^ kh) ^ 2 ≤ 2 ^ k := le_of_eq (by rw [← pow_mul, Nat.mul_comm, h2k])
    have h5 := mix_le (nc := carriers.length) (a := a) hPM hk2 ha hp26 (pp1 26)
    exact toKQ (prod5 h1 hcardF h3 h4 h5) ctot ktot
  -- the n-only atoms
  have aerr : F.filterErrDeg * L ≤ KQ :=
    toKQ (c := 0) (d := 0) (a' := F.filterErrDeg)
      (atomE2 (le_of_le_of_eq (SymSizes.self_le_two_pow _) (by rw [pow_zero, pow_zero]; ring))) (Nat.zero_le _) kfe
  have afe4 : (F.filterErrDeg + 4) * (n + 3) ≤ KQ := by
    apply toKQ (c := 1) (d := 1) (a' := F.filterErrDeg + 4) (atomE2 _) c1 kfe4
    have q1 : F.filterErrDeg + 4 ≤ 2 ^ ((F.filterErrDeg + 4) * L) :=
      le_trans (SymSizes.self_le_two_pow _) (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hL1))
    calc (F.filterErrDeg + 4) * (n + 3) ≤ 2 ^ ((F.filterErrDeg + 4) * L) * (2 * (n + 2)) :=
          Nat.mul_le_mul q1 (n3_le n)
      _ = 2 ^ 1 * ((n + 2) ^ 1 * 2 ^ ((F.filterErrDeg + 4) * L)) := by ring
  have acr : 2 * F.cr + 20 ≤ KQ := by
    apply toKQc (c := 4 + Nat.clog 2 (2 * h.cr + 2)) (d := 0) _ ccr (Nat.zero_le _)
    rw [pow_zero, mul_one, pow_add, ← hcr]
    exact lin16 (le_two_pow_clog _)
  have asp : SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n - 1) ≤ KQ := by
    have e1 : 3 + 32 * SymSizes.cXg l * SymSizes.schedJ l = h.sA := by unfold SB.sA; rw [hcX, hJ]
    have e2 : 6 + 32 * SymSizes.cXg l * (SymSizes.schedJ l + 1) = h.sBc := by unfold SB.sBc; rw [hcX, hJ]
    have hsp := SymSizes.sparse_le_gate l n
    rw [e1, e2, ← hLd] at hsp
    apply toKQ (c := h.sBc) (d := 0) (a' := h.sA) (atomE2 (le_trans hsp (le_of_eq _))) csp ksa
    rw [pow_add, pow_zero]; ring
  have at5 : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n + 5 ≤ KQ := by
    have hr := SymSizes.rowBt_le l n
    rw [← hJ, ← hLd] at hr
    exact toKQc (c := 1 + Nat.clog 2 (h.J + 6)) (d := 1) (t5_le hr hLn (le_two_pow_clog _)) cj k1
  have asps : Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n ≤ KQ :=
    toKQc (c := 0) (d := h.Csp + 3) (by rw [pow_zero, one_mul, hCsp]; exact CallIndex.sp_le l n) (Nat.zero_le _) kcsp
  have acapN : 2 ^ 40 * (CallIndexR.capK F.cr * (n + 2) ^ (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32)) +
      CapNum.cMain (gateCap l) .sym ≤ 2 * KQ := by
    have t1 := toKQc (X := 2 ^ 40 * (h.capK * (n + 2) ^ h.Zm)) (c := 40 + Nat.clog 2 h.capK) (d := h.Zm)
      (by rw [pow_add, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_two_pow_clog _))) c40 kzm
    have t2 := toKQc (X := h.cM) (c := Nat.clog 2 h.cM) (d := 0) (by rw [pow_zero, mul_one]; exact le_two_pow_clog _)
      ccm (Nat.zero_le _)
    rw [← hK, ← hZm, ← hcM]
    exact le_of_le_of_eq (Nat.add_le_add t1 t2) (by ring)
  have aeuK : SymDec.euV (cyOf Cs).sum carriers.length a ≤ KQ := toKQc (c := 7) (d := 26) aeu c7 k26
  have astK : SymDec.stV ((cyOf Cs).getD 0 0) ((cyOf Cs).getD 1 0) ((cyOf Cs).getD 2 0) ((cyOf Cs).getD 3 0) ≤ KQ :=
    toKQc (c := 0) (d := 208) (by rw [pow_zero, one_mul]; exact ast) (Nat.zero_le _) k208
  have afb' : 2 * 2 ^ FlatNums.fbv (cyOf Cs).sum (SymDec.bV carriers.length BS) (Ledger.Lq n + 5) ≤ KQ := by
    rw [hLq]; exact afb
  have hLqn : Ledger.Lq n ≤ n + 2 := by rw [hLq]; exact hLn
  have hX9 : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by norm_num) _
  have aL5 : L + 5 ≤ KQ := le_trans (Nat.add_le_add_right hLn 5) (le_trans (L7 hX9) a26)
  -- the machine's numbers
  obtain ⟨U, hUd⟩ : ∃ x, x = Qv ^ h.dcap := ⟨_, rfl⟩
  have hQU : Qv ≤ U := by
    rw [hUd]; exact le_of_eq_of_le (pow_one Qv).symm (Nat.pow_le_pow_right hQv1 dcap1)
  have hU1 : 1 ≤ U := le_trans hQv1 hQU
  obtain ⟨cap, hcapd⟩ : ∃ x, x = h.Kcap * U := ⟨_, rfl⟩
  have hKA : h.KA = 2 ^ h.cA := rfl
  have hKQU : KQ ≤ h.KA * U := by rw [hKQ, hKA]; exact Nat.mul_le_mul_left _ hQU
  have hcapKQ : 100 * KQ + 200000 ≤ cap := by
    calc 100 * KQ + 200000 ≤ 100 * (h.KA * U) + 200000 * U :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hKQU) (Nat.le_mul_of_pos_right _ hU1)
      _ = (100 * h.KA + 200000) * U := by ring
      _ ≤ h.Kcap * U := Nat.mul_le_mul_right _ kcap1
      _ = cap := hcapd.symm
  have hQpow : ∀ d, d ≤ h.dcap → Qv ^ d ≤ U := fun d hd => by rw [hUd]; exact Nat.pow_le_pow_right hQv1 hd
  have hsetN : ∀ C D, C * (30 * h.KA) ^ D ≤ h.Kcap → D ≤ h.dcap → C * (30 * KQ) ^ D ≤ cap := by
    intro C D hC hD
    have a1 : (30 * KQ) ^ D ≤ (30 * h.KA) ^ D * U := by
      calc (30 * KQ) ^ D = (30 * h.KA * Qv) ^ D := by rw [hKQ, hKA, Nat.mul_assoc]
        _ = (30 * h.KA) ^ D * Qv ^ D := by rw [mul_pow]
        _ ≤ (30 * h.KA) ^ D * U := Nat.mul_le_mul_left _ (hQpow D hD)
    calc C * (30 * KQ) ^ D ≤ C * ((30 * h.KA) ^ D * U) := Nat.mul_le_mul_left _ a1
      _ = C * (30 * h.KA) ^ D * U := by ring
      _ ≤ h.Kcap * U := Nat.mul_le_mul_right _ hC
      _ = cap := hcapd.symm
  have hcapN : h.Cn * (30 * KQ) ^ h.Dn ≤ cap := hsetN _ _ kcapN dcapDn
  have hcapQ : h.Qn * (30 * KQ) ^ h.Qd ≤ cap := hsetN _ _ kcapQ dcapQd
  -- the pipelines' bound
  obtain ⟨BPf, hBPf⟩ : ∃ x, x = h.Kf * (30 * KQ) ^ h.Df * Qv := ⟨_, rfl⟩
  obtain ⟨BPp, hBPp⟩ : ∃ x, x = h.Kp * (cap + 30 * KQ) ^ h.Dp * (32 ^ h.Dp * Qv) := ⟨_, rfl⟩
  -- the FILTER rows
  have hsbF' : Fintype.card (GapSeed ((callInputs l F kclk coef A a0 ha0).filterParams .sym n)) = 2 ^ sb := by
    rw [card_gapSeed, hsbF]
  have hPl : ((callInputs l F kclk coef A a0 ha0).filterParams .sym n).len = 2 * (n + 1) ^ 26 := rfl
  have hPc : ((callInputs l F kclk coef A a0 ha0).filterParams .sym n).cap = BS := by rw [hBSd]; rfl
  have hPe' : ((callInputs l F kclk coef A a0 ha0).filterParams .sym n).errExp = F.filterErrDeg * L := by
    rw [hLd]; rfl
  have hexp : ∀ Ls, Ls ≤ 2 * (n + 1) ^ 26 → (Ls + 2) ^ (h.Df * (F.filterErrDeg * L + 1)) ≤ Qv := by
    intro Ls hLs
    have hx := exp_filter (fe := F.filterErrDeg) (Df := h.Df) (KF := h.KF) hLs kdf
    rw [← hLd] at hx
    exact le_trans hx (le_trans (Nat.pow_le_pow_right (by norm_num) hKFm) hmQ)
  have hFN := fn_block FS h hFS1 hFS2 hfp ((callInputs l F kclk coef A a0 ha0).filterParams .sym n)
    (nc := carriers.length) hPl hPc hPe' hsbF' hBS1 hx0 hx1 hys h2k a26 aBS aerr akk asb hcapN hexp hBPf (BPp := BPp)
  -- the POP rows
  have hcP2 : 2 * Fintype.card (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).FlatSeed ≤ KQ := by
    rw [← FlatNums.card_eq, hPe]; exact afbG hPM hPB
  have hDpm : 2 ^ (h.Dp * (L + 5)) ≤ 32 ^ h.Dp * Qv := by
    have d1 : h.Dp * L ≤ m := le_trans (le_trans (Nat.mul_le_mul_right _ kdp) (Nat.mul_le_mul_left _ hLL)) hKFm
    have e1 : h.Dp * (L + 5) = 5 * h.Dp + h.Dp * L := by ring
    have e2 : (2 : ℕ) ^ (5 * h.Dp) = 32 ^ h.Dp := by rw [pow_mul]; norm_num
    have e : 2 ^ (h.Dp * (L + 5)) = 32 ^ h.Dp * 2 ^ (h.Dp * L) := by rw [e1, pow_add, e2]
    rw [e]; exact Nat.mul_le_mul_left _ (le_trans (Nat.pow_le_pow_right (by norm_num) d1) hmQ)
  have hPB' : (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).B ≤ BS * 8192 :=
    le_of_le_of_eq hPB (Nat.mul_comm _ _)
  have hY : ∀ Lp, Lp ≤ (n + 1) ^ 26 →
      (8 * Lp + 2) ^ (3 * lbP (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers) + 1) ≤ 2 ^ T := by
    intro Lp hLp
    have := popY_fam hPB' hLp
    rw [← hLd, ← hTd] at this
    exact this
  have hml : ∀ row, row < 2 ^ k → (2 * (2 * row) + 4) * pbdG Cs carriers ≤ KQ := by
    intro row hrow
    have hG' : pbdG Cs carriers ≤ 8 * (n + 1) ^ 26 := by
      unfold pbdG
      exact le_trans (Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.add_le_add hx0 hx1)) hys) (le_of_eq (by ring))
    have hr4 : 2 * (2 * row) + 4 ≤ 8 * 2 ^ k := r4_le hrow
    apply toKQ (c := 6) (d := 26) (a' := 0) _ c6 k260
    calc (2 * (2 * row) + 4) * pbdG Cs carriers ≤ 8 * 2 ^ k * (8 * (n + 1) ^ 26) := Nat.mul_le_mul hr4 hG'
      _ = 2 ^ 6 * ((n + 1) ^ 26 * 1 * 2 ^ k * 1) := by ring
      _ ≤ 2 ^ 6 * ((n + 2) ^ 26 * 2 ^ (0 * L) * 2 ^ k * 2 ^ T) := by
          rw [zero_mul, pow_zero]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hp26))
            Nat.one_le_two_pow)
  have hPN := pn_block2 Q h hQ1 hQ2 hpp Cs carriers (symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers)
    hPe hPM hPB hcP2 hx0 hx1 hy hys h2k hY aT a26 aBS akk aL5 hml hcapQ hDpm hBPp (BPf := BPf)
  -- the scrub `R = K_r·Q^D`
  obtain ⟨Y, hYd⟩ : ∃ x, x = Qv ^ h.D := ⟨_, rfl⟩
  have eR : UnaryCalc.value h.D h.Kr (2 ^ m) = h.Kr * Y := by rw [value_eq, ← hQd, hYd]
  have eb : UnaryCalc.value 1 h.KA (2 ^ m) = KQ := by
    show h.KA * (2 ^ m + 1) ^ 1 = KQ
    rw [pow_one, ← hQd, hKQ, hKA]
  have yQ : ∀ d, d ≤ h.D → Qv ^ d ≤ Y := fun d hd => by rw [hYd]; exact Nat.pow_le_pow_right hQv1 hd
  have hUpow : ∀ j, U ^ j = Qv ^ (h.dcap * j) := fun j => by rw [hUd, ← pow_mul]
  have hY1 : 1 ≤ Y := by rw [hYd]; exact Nat.one_le_pow _ _ hQv1
  have fKQ : KQ ≤ h.KA * Y := by
    rw [hKQ, hKA]; exact Nat.mul_le_mul_left _ (le_of_eq_of_le (pow_one Qv).symm (yQ 1 hD1))
  have hcap1 : 1 ≤ cap := le_trans (by norm_num : 1 ≤ 200000) (le_trans (Nat.le_add_left _ _) hcapKQ)
  have fc3 : (cap + 2) * (cap + 2) * (cap + 2) ≤ (h.Kcap + 2) ^ 3 * Y := by
    have a1 : cap + 2 ≤ (h.Kcap + 2) * U := by
      rw [hcapd, Nat.add_mul]; exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hU1) _
    have a2 := Nat.mul_le_mul (Nat.mul_le_mul a1 a1) a1
    have e2 : (h.Kcap + 2) * U * ((h.Kcap + 2) * U) * ((h.Kcap + 2) * U) = (h.Kcap + 2) ^ 3 * U ^ 3 := by ring
    rw [e2, hUpow] at a2
    exact le_trans a2 (Nat.mul_le_mul_left _ (yQ _ (le_of_eq_of_le (Nat.mul_comm _ _) hD3)))
  have a2K : cap + 1 ≤ 2 * h.Kcap * U := by
    rw [Nat.mul_assoc, ← hcapd, two_mul]; exact Nat.add_le_add_left hcap1 _
  have fCb : FS.bound cap ≤ h.Cb * (2 * h.Kcap) ^ h.Db * Y := by
    have hp := FS.bound_poly cap
    unfold ValidatorPolynomialDomination.PolyBounded at hp
    rw [hFS3, hFS4] at hp
    have a2 : (cap + 1) ^ h.Db ≤ (2 * h.Kcap) ^ h.Db * U ^ h.Db :=
      le_of_le_of_eq (Nat.pow_le_pow_left a2K _) (by rw [mul_pow])
    have a3 : U ^ h.Db ≤ Y := by rw [hUpow]; exact yQ _ hDb
    calc FS.bound cap ≤ h.Cb * (cap + 1) ^ h.Db := hp
      _ ≤ h.Cb * ((2 * h.Kcap) ^ h.Db * Y) := Nat.mul_le_mul_left _ (le_trans a2 (Nat.mul_le_mul_left _ a3))
      _ = h.Cb * (2 * h.Kcap) ^ h.Db * Y := by ring
  have fQb : Q.bound cap ≤ h.Qb * (2 * h.Kcap) ^ h.Qe * Y := by
    have hp := Q.bound_le cap
    rw [hQ3, hQ4] at hp
    have a2 : (cap + 1) ^ h.Qe ≤ (2 * h.Kcap) ^ h.Qe * U ^ h.Qe :=
      le_of_le_of_eq (Nat.pow_le_pow_left a2K _) (by rw [mul_pow])
    have a3 : U ^ h.Qe ≤ Y := by rw [hUpow]; exact yQ _ hDq
    calc Q.bound cap ≤ h.Qb * (cap + 1) ^ h.Qe := hp
      _ ≤ h.Qb * ((2 * h.Kcap) ^ h.Qe * Y) := Nat.mul_le_mul_left _ (le_trans a2 (Nat.mul_le_mul_left _ a3))
      _ = h.Qb * (2 * h.Kcap) ^ h.Qe * Y := by ring
  have fBPf : BPf ≤ h.Kf * (30 * h.KA) ^ h.Df * Y := by
    rw [hBPf]
    have a1 : (30 * KQ) ^ h.Df ≤ (30 * h.KA) ^ h.Df * Qv ^ h.Df := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by rw [hKQ, hKA, Nat.mul_assoc]) _
    calc h.Kf * (30 * KQ) ^ h.Df * Qv ≤ h.Kf * ((30 * h.KA) ^ h.Df * Qv ^ h.Df) * Qv :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ a1)
      _ = h.Kf * (30 * h.KA) ^ h.Df * Qv ^ (h.Df + 1) := by rw [pow_succ]; ring
      _ ≤ h.Kf * (30 * h.KA) ^ h.Df * Y := Nat.mul_le_mul_left _ (yQ _ hDf)
  have fBPp : BPp ≤ h.Kp * (2 * h.Kcap + 30 * h.KA) ^ h.Dp * 32 ^ h.Dp * Y := by
    rw [hBPp]
    have a1 : cap + 30 * KQ ≤ (2 * h.Kcap + 30 * h.KA) * U := by
      have e : (2 * h.Kcap + 30 * h.KA) * U = 2 * (h.Kcap * U) + 30 * (h.KA * U) := by ring
      rw [e, ← hcapd]
      exact Nat.add_le_add (Nat.le_mul_of_pos_left _ (by norm_num)) (Nat.mul_le_mul_left _ hKQU)
    have a2 : (cap + 30 * KQ) ^ h.Dp ≤ (2 * h.Kcap + 30 * h.KA) ^ h.Dp * U ^ h.Dp :=
      le_of_le_of_eq (Nat.pow_le_pow_left a1 _) (by rw [mul_pow])
    have a3 : U ^ h.Dp * Qv ≤ Y := by rw [hUpow, ← pow_succ]; exact yQ _ hDp
    calc h.Kp * (cap + 30 * KQ) ^ h.Dp * (32 ^ h.Dp * Qv) ≤
          h.Kp * ((2 * h.Kcap + 30 * h.KA) ^ h.Dp * U ^ h.Dp) * (32 ^ h.Dp * Qv) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ a2)
      _ = h.Kp * (2 * h.Kcap + 30 * h.KA) ^ h.Dp * 32 ^ h.Dp * (U ^ h.Dp * Qv) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ a3
  -- the banks' budget
  obtain ⟨Bb, hBbd⟩ : ∃ x, x = SymDec.fbCost cap + FS.bound cap + (SymDec.pbCost cap + Q.bound cap) := ⟨_, rfl⟩
  have hFc : SymDec.fbCost cap + FS.bound cap ≤ Bb := by rw [hBbd]; exact Nat.le_add_right _ _
  have hQc : SymDec.pbCost cap + Q.bound cap ≤ Bb := by rw [hBbd]; exact Nat.le_add_left _ _
  -- the data
  have hnwV : PrimT.C4GateSym.needW n ≤ V := by
    rw [hVd, value_eq]
    exact le_trans (hnw n) (Nat.mul_le_mul dC2 (Nat.pow_le_pow_right (Nat.succ_pos _) dD2))
  have td := PrimT.C4GateSym.sym_data_hyps Cs carriers ha hk2 hdesc henv V hnwV
  have hDok : ShellD.DataOK Cs carriers V := ⟨ha, hk2, td.1, td.2.1, td.2.2.1, td.2.2.2.1, td.2.2.2.2.1,
    td.2.2.2.2.2.1, td.2.2.2.2.2.2.1, td.2.2.2.2.2.2.2.1, td.2.2.2.2.2.2.2.2.1⟩
  have hKb : ∀ c ∈ Data.symCodes a Cs, natBitLength c ≤ V := by
    intro c hc
    unfold Data.symCodes at hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    exact td.2.2.2.2.2.2.2.2.2.1 i
  have hC : ∀ c ∈ carriers.map (·.length) ++ cyOf Cs, c ≤ (n + 1) ^ 26 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcx c hc
    · exact hcy c hc
  have hul : (Data.unaryList (Data.symCounts a Cs carriers)).length ≤ KQ := by
    have hsc : ∀ c ∈ Data.symCounts a Cs carriers, c ≤ (n + 1) ^ 26 := by
      intro c hc
      unfold Data.symCounts at hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hcx c hc
      · exact hcy c hc
    have hl := PrimT.C4GateSym.unaryList_len_le _ _ hsc
    have hlen : (Data.symCounts a Cs carriers).length = carriers.length + a := by
      unfold Data.symCounts; simp
    rw [hlen] at hl
    have q := Nat.mul_le_mul_right ((n + 1) ^ 26 + 1) (Nat.add_le_add hk2 ha)
    have hX3 : 3 ≤ (n + 1) ^ 26 := le_trans (by norm_num : 3 ≤ 9) (le_trans (Nat.succ_le_succ hn8) hX9)
    exact le_trans hl (le_trans q (le_trans (ul_le hX3) a26))
  -- the capacity's conditions
  have hKQcap : KQ ≤ cap :=
    le_trans (le_trans (Nat.le_mul_of_pos_left KQ (by norm_num : 0 < 100)) (Nat.le_add_right _ 200000)) hcapKQ
  have e1 : (Data.symCodes a Cs).length = a := by unfold Data.symCodes; simp
  have hN1 := p1_block (cap := cap) (X := (n + 1) ^ 26) (symReq n a ha Cs carriers translation).word
    (Data.symCodes a Cs) (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (cyOf Cs) e1
    (List.length_map _) (List.length_map _) aW ha hk2 aV an hxs hys a26 hcapKQ
  obtain ⟨hI, hcF, hcB, hcS, hcP, hX⟩ := cap_block (nc := carriers.length) hcapKQ eb atot aeuK hys a26 h2k akk astK
    afb' hk2 hx0 hx1 (le_trans hbV aBS) hLqn an afe4 acr asp acapN
  have hcC := capNeed_of l F.cr n cap hX
  have hN2 := nn_block (cap := cap) hBS1 hcapKQ aBS a26 (by rw [hLq]; exact aerr) (by rw [← hsbd]; exact asb) hLqn an
    hbV hys afb' h2k akk atot hk2 ha hy4
  -- the shell's numbers
  obtain ⟨hcap, hR, hboot0⟩ := r_block h (cap := cap) eR fc3 fKQ aW an hY1
  have hboot : ShellD.bootCost (symReq n a ha Cs carriers translation).word n 0 0 ≤ UnaryCalc.value h.D h.Kr (2 ^ m) :=
    le_trans (HashSizes.bootCost_le (symReq n a ha Cs carriers translation).word n) hboot0
  have hTOT : Enum.symNT (callInputs l F kclk coef A a0 ha0) hs Cs carriers * (2 ^ kh) ^ 2 *
      ((carriers.length + 2 * a) * ((symListParams (callInputs l F kclk coef A a0 ha0) n a Cs carriers).M + 3) + 2) ≤
      UnaryCalc.value 1 h.KA (2 ^ m) := by rw [eb]; exact aNT
  have hfeL : F.filterErrDeg ≤ F.filterErrDeg * L := Nat.le_mul_of_pos_right _ hL1
  have hnU := nu_block h (n := n) (a := a) (nc := carriers.length) (V := V) (X := (n + 1) ^ 26) (ys := (cyOf Cs).sum)
    (cr := F.cr) (fe := (callInputs l F kclk coef A a0 ha0).filterErrDeg)
    (t := Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
    (sp := Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Lq := Ledger.Lq n)
    (b := UnaryCalc.value 1 h.KA (2 ^ m)) (R := UnaryCalc.value h.D h.Kr (2 ^ m))
    (le_trans an hKQcap) ha hk2 (le_trans aV hKQcap)
    (le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 8)) a26) hKQcap)
    (le_trans (le_trans hys (le_trans (Nat.mul_le_mul_right _ (by norm_num : 4 ≤ 8)) a26)) hKQcap)
    (le_trans (le_trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)) (Nat.le_add_right _ 20)) acr) hKQcap)
    (le_trans hfeL (le_trans aerr hKQcap) : F.filterErrDeg ≤ cap) (le_trans (Nat.le_add_right _ 5) (le_trans at5 hKQcap))
    (le_trans asps hKQcap) (le_trans hLqn (le_trans an hKQcap)) hBbd hul eb eR fKQ fc3 fCb fQb fBPf fBPp hY1
  have hBud : 2 * ShellT.shellCostG (symReq n a ha Cs carriers translation).word n h.D h.Kr h.D2 h.C2
      (Data.coreCost a Cs carriers V V) h.Dv h.Cv
      (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
        (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2) m 1 h.KA
      (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) + 2 ≤
      ShellT.costS h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA (symReq n a ha Cs carriers translation).word.length n
        (Data.coreCost a Cs carriers V V)
        (2 * NumsXS.numsStageCostS (UnaryCalc.value h.Dv h.Cv n) ((callInputs l F kclk coef A a0 ha0).starParams n hs)
          (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l) 26 6 h.KF F.cr + 2)
        (UnaryCalc.value h.D h.Kr (2 ^ m) - 1) m := by
    refine le_of_eq ?_
    unfold ShellT.costS
    rw [Nat.min_eq_left (Nat.sub_le _ _), ← ShellT.shellCostG_len]
  have hw := (ReqBridge.reqW_symReq ha Cs carriers translation).symm
  have hN := sneed_fam l F kclk coef A a0 ha0 h hZ hZm hCsp hJ hcX hKL hK hcr hcM hs
  -- the run
  subst hVd hBSd hkhd hmd
  exact SymDec.sym_ready cap W FS Q.toPopSetupSpec l F kclk coef A a0 ha0 h.D h.Kr h.D2 h.C2 h.Dv h.Cv 1 h.KA h.KF
    _ _ hs Cs carriers (RepairRepresentation.natListWord translation) (symReq n a ha Cs carriers translation).word
    _ ((n + 1) ^ 26) Bb (BPf + BPp) ha hk2 hw hKb hC hN1 hcS hcP hcC hN2 hI hBS1 hcF hFc hFN hQc hcB hPN hDok hN hcap
    hR hboot hTOT hnU hBud

end Run

end NearCubicWires.WireExponent3_5.PrimAsm.SymFam
