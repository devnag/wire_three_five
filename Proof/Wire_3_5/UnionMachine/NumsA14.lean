import Proof.Wire_3_5.UnionMachine.NumsA13

/-! # The SYM numbers' full register export with the tuple size `dA = a`

`numsAtG2` / `numsBankG2`: `NumsA13`'s `numsAtG` / `numsBankG` with `numsS_spec`'s `dA = |codes| = a` kept
(for `symFront` `vA` field and SWn's first number `a`).

* **`numsAtG2`**, **`numsBankG2`**.

Paper quantities of the main type: the SYM call's numbers (`a`, `|FlatSeed|`, the list parameters, the bottom counts,
`Q`) in registers (P3:2929-2941, 2994-3000, 3011-3016). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM numbers at a SYM request, the full register export** (`x = 0` bank, at `cap₀ ≥ K₀·X^{D₀}`). -/
theorem numsAtG2 {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (cap₀ : ℕ)
    (hc : K0 l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ D0 l F.filterErrDeg ≤ cap₀) :
    ∃ (τ : WState (LNS 0) LNR) (c : ℕ), WExec cap₀ (numsP l F)
        (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) [] 0 (Data.unaryList (Data.symCounts a' Cs carriers)))
        τ c ∧
      (∀ i, τ.val (SymDec.G i) = SymDec.numsVec n (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
        (F.filterErrDeg * Ledger.Lq n) (SymDec.cyOf Cs).sum carriers.length (Ledger.Lq n)
        (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) a' ((SymDec.cyOf Cs).getD 0 0)
        ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0) i) ∧
      τ.val SymDec.dN = n ∧ τ.val SymDec.dA = a' ∧ τ.val SymDec.dM0 = (SymDec.cyOf Cs).getD 0 0 ∧
      τ.val SymDec.dM1 = (SymDec.cyOf Cs).getD 1 0 ∧ τ.val SymDec.dM2 = (SymDec.cyOf Cs).getD 2 0 ∧
      τ.val SymDec.dM3 = (SymDec.cyOf Cs).getD 3 0 ∧
      τ.val (PrimT.C4Set.KB 52) = SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ∧
      (∀ q, τ.val q ≤ cap₀) ∧
      τ.st = (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) [] 0
        (Data.unaryList (Data.symCounts a' Cs carriers))).st ∧
      (∀ s, s ≠ sk 0 113 → τ.sh s = (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) [] 0
        (Data.unaryList (Data.symCounts a' Cs carriers))).sh s) ∧
      τ.cell = false ∧ c ≤ 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) := by
  obtain ⟨hk2, -, -⟩ := PrimT.C4GateSym.sym_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  have hn8 := HashFam.fam_n8 l F kclk coef A a ha hs
  have hcl : (Data.symCodes a' Cs).length = a' := by unfold Data.symCodes; simp
  -- the input and its length
  obtain ⟨w, hwd⟩ : ∃ v, v = fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ :=
    ⟨_, rfl⟩
  rw [← hwd] at hc ⊢
  have hnw : n ≤ w.length := by
    have := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A) (a := a) (ha := ha)
      ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
    rw [hwd]; exact this
  have hQw : SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ≤ w.length := by
    rw [hwd]; exact q_le_fpIn l F kclk coef A a ha ha' Cs carriers translation hcall hs
  have hkh := FinalPass.SymFr.kh_two l F kclk coef A a ha hs
  have hN : 2 ^ SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) ≤
      SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers :=
    Sampler.N_le_sampleCount _ _ _ _ (by omega) (by omega)
  -- the envelope
  obtain ⟨X, hXd⟩ : ∃ v, v = w.length + 1 := ⟨_, rfl⟩
  rw [← hXd] at hc
  have eKF : (nwSB l F).KF = KFa l F.filterErrDeg := KF_eq l F
  obtain ⟨KF, hKFd⟩ : ∃ v, v = KFa l F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨cA, hcAd⟩ : ∃ v, v = (nwSB l F).cA := ⟨_, rfl⟩
  obtain ⟨k, hkd⟩ : ∃ v, v = ((gate0 l F).budget kclk coef A a ha).kOf n := ⟨_, rfl⟩
  obtain ⟨kh, hkhd⟩ : ∃ v, v = SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs) := ⟨_, rfl⟩
  rw [← hkhd] at hN hkh
  rw [← hkd] at hkh
  have h2k : 2 ^ k ≤ X ^ 2 := by
    rw [← hkh, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (by omega) 2
  have hn2 : n + 2 ≤ 2 * X := by omega
  have hp : (n + 2) ^ KF ≤ 2 ^ KF * X ^ KF := by rw [← mul_pow]; exact Nat.pow_le_pow_left hn2 _
  obtain ⟨KQ, hKQd⟩ : ∃ v, v = 2 ^ (cA + KF) * (n + 2) ^ KF * 2 ^ k := ⟨_, rfl⟩
  have hKQle : KQ ≤ 2 ^ (cA + 2 * KF) * X ^ (KF + 2) := by
    rw [hKQd]
    calc 2 ^ (cA + KF) * (n + 2) ^ KF * 2 ^ k ≤ 2 ^ (cA + KF) * (2 ^ KF * X ^ KF) * X ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) h2k
      _ = 2 ^ (cA + 2 * KF) * X ^ (KF + 2) := by rw [two_mul, pow_add, pow_add, pow_add]; ring
  have hP1 : 1 ≤ X ^ (KF + 2) := Nat.one_le_pow _ _ (by omega)
  have hPX : X ≤ X ^ (KF + 2) := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ (KF + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have eK0 : K0 l F * X ^ D0 l F.filterErrDeg =
      100 * (2 ^ (cA + 2 * KF) * X ^ (KF + 2)) + 200002 * X ^ (KF + 2) := by
    unfold K0 D0; rw [← hKFd, ← hcAd]; ring
  rw [eK0] at hc
  have hKQ : 100 * KQ + 200000 ≤ cap₀ := by omega
  have hwc : 2 * w.length + 2 ≤ cap₀ := by omega
  -- the needs
  obtain ⟨hN1, hKb, hC, hcS, hcP, hcC, hN2, hv, hag⟩ := sym_needsG l F kclk coef A a ha (nwSB l F) (nw_hwb l F)
    (nw_hnw l F) rfl rfl rfl rfl rfl rfl rfl rfl rfl ha' Cs carriers translation hcall hs cap₀ KQ
    (fun {X c d a'} hX hc hda => by
      rw [hKQd, hcAd, hKFd, ← eKF, hkd]
      exact kq_atom _ _ _ _ hX hc hda) hKQ
  -- `numsS_spec`'s premises
  have a_hw : w = Data.reqW ((callInputs l F kclk coef A a ha).starParams n hs).n false (Data.symCodes a' Cs)
      (carriers.map Stars.Carrier.code) (RepairRepresentation.natListWord translation ++
        seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩) := by
    rw [hwd]
    exact (ReqBridge.reqW_word ⟨n, .sym, a', ha', Cs, carriers, translation⟩ _).symm
  have a_ccs : (carriers.map Stars.Carrier.code).length = (carriers.map (·.length)).length := by
    rw [List.length_map, List.length_map]
  have a_cx : (carriers.map (·.length)).length ≤ 2 := by rw [List.length_map]; exact hk2
  have a_cy : (SymDec.cyOf Cs).length ≤ 4 := by rw [SymDec.cyOf_length]; exact ha'
  have a_N1 : P1Need cap₀ w ((callInputs l F kclk coef A a ha).starParams n hs).n (Data.symCodes a' Cs)
      (carriers.map Stars.Carrier.code) (carriers.map (·.length)) (SymDec.cyOf Cs)
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) :=
    ⟨hwc, hN1.cP, hN1.cX, hN1.cC⟩
  have hQl : (PrimT.C4Set.symInOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) n
      (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) carriers.length a' (SymDec.cyOf Cs)).Q =
      SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers :=
    PrimT.C4SymL.symQ_link (callInputs l F kclk coef A a ha) Cs carriers hs ha' rfl rfl
  have a_Q : 2 * (PrimT.C4Set.symInOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
      ((callInputs l F kclk coef A a ha).starParams n hs).n
      (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n)
      (Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs))
      (carriers.map (·.length)).length (Data.symCodes a' Cs).length (SymDec.cyOf Cs)).Q ≤ cap₀ := by
    rw [List.length_map, hcl]
    show 2 * (PrimT.C4Set.symInOf (((gate0 l F).budget kclk coef A a ha).capOf .sym n) n
      (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) carriers.length a' (SymDec.cyOf Cs)).Q ≤ cap₀
    rw [hQl]
    omega
  have a_v : ∀ j : Fin 11, (![((gate0 l F).budget kclk coef A a ha).capOf .sym n,
      ((callInputs l F kclk coef A a ha).starParams n hs).n,
      F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n,
      Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n,
      SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs),
      (carriers.map (·.length)).length, (Data.symCodes a' Cs).length, (SymDec.cyOf Cs).getD 0 0,
      (SymDec.cyOf Cs).getD 1 0, (SymDec.cyOf Cs).getD 2 0, (SymDec.cyOf Cs).getD 3 0] : Fin 11 → ℕ) j ≤ cap₀ := by
    rw [List.length_map]; exact hv
  have a_N2 : SymDec.NumsNeed cap₀ ((callInputs l F kclk coef A a ha).starParams n hs).n
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
      (F.filterErrDeg * Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n) (SymDec.cyOf Cs).sum
      (carriers.map (·.length)).length (Ledger.Lq ((callInputs l F kclk coef A a ha).starParams n hs).n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) (Data.symCodes a' Cs).length
      ((SymDec.cyOf Cs).getD 0 0) ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0)
      ((SymDec.cyOf Cs).getD 3 0) := by
    rw [List.length_map, hcl]; exact hN2
  obtain ⟨τ, c, e, vN, vA, -, vM0, vM1, vM2, vM3, -, -, -, -, -, -, -, -, -, -, hG, hKB, -, hst, hsh, hcell, hcost⟩ :=
    PrimT.C4Set.numsS_spec cap₀ F.cr F.filterErrDeg (gateZeta_pos l) (gateZeta_lt l) (gateCδ1 l) (gateCap l)
      ((callInputs l F kclk coef A a ha).starParams n hs) rfl w (Data.symCodes a' Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation ++
        seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
      (carriers.map (·.length)) (SymDec.cyOf Cs) (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26)
      (((gate0 l F).budget kclk coef A a ha).capOf .sym n) (F.filterErrDeg * Ledger.Lq n) (Ledger.Lq n)
      (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) a_hw a_ccs a_cx a_cy hKb hC a_N1 rfl rfl
      rfl rfl hcS hcP hcC a_N2 (le_trans (by norm_num) hn8) a_Q a_v
  -- the steps
  have cP := hN1.cP
  have cC := hN1.cC
  have hsp := hcC.hs
  have hL := hcC.hL1
  have ht : Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n ≤ cap₀ := by
    unfold SparseNum.sparseBound at hcP
    omega
  have h4 : 4 * (n + 3) ≤ (F.filterErrDeg + 4) * (n + 3) := Nat.mul_le_mul_right _ (by omega)
  have h5 : F.filterErrDeg ≤ (F.filterErrDeg + 4) * (n + 3) :=
    le_trans (Nat.le_add_right _ 4) (Nat.le_mul_of_pos_right _ (by omega))
  have v1 := Nat.one_le_two_pow (n := natBitLength n)
  have v2 := Nat.one_le_two_pow (n := natBitLength (Data.symCodes a' Cs).length)
  have v3 := Nat.one_le_two_pow (n := natBitLength (carriers.map Stars.Carrier.code).length)
  have hB : PrimT.C4SymN.symBigCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum 0 ≤
      3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) + 0 :=
    PrimT.C4Bud.symBig_le cap₀ n F.cr F.filterErrDeg _ _ (Ledger.Lq n) a' carriers.length _ ((n + 1) ^ 26) _
    0 (by omega) ha' (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ht hsp hL
  have hcost' : c ≤ PrimT.C4Set.numsSCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum := by
    have := hcost
    rw [List.length_map, hcl] at this
    exact this
  have hsb : PrimT.C4Set.numsSCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum ≤
      PrimT.C4SymN.symBigCost cap₀ n F.cr F.filterErrDeg (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) (Ledger.Lq n) a' carriers.length
      (UnaryCalc.value (nwSB l F).D2 (nwSB l F).C2 n) ((n + 1) ^ 26) (SymDec.cyOf Cs).sum 0 := by
    unfold PrimT.C4SymN.symBigCost; omega
  have hv0 : ∀ q, (CellLoopD.blankCellD 0 w [] 0 (Data.unaryList (carriers.map (·.length) ++ SymDec.cyOf Cs))).val q ≤
      cap₀ := fun q => by simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
  have hvl := FinalPass.S5T.WExec.val_le cap₀ e hv0
  refine ⟨τ, c, e, fun i => ?_, vN, by rw [vA]; exact hcl, vM0, vM1, vM2, vM3, ?_, hvl, hst, hsh, hcell,
    le_trans hcost' (le_trans hsb (le_of_le_of_eq hB (Nat.add_zero _)))⟩
  · have h := hG i
    rw [List.length_map, hcl] at h
    exact h
  · rw [hKB, List.length_map, hcl]; exact hQl

/-- **The SYM numbers on NW's bank, the full register export**, at any `cap ≥ cap₀ ≥ K₀·X^{D₀}`. -/
theorem numsBankG2 (x : ℕ) {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (cap₀ cap : ℕ)
    (hc : K0 l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ D0 l F.filterErrDeg ≤ cap₀) (hcap : cap₀ ≤ cap)
    (ω : WState (LNS x) LNR)
    (hω : NumsIn x (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (Data.unaryList (Data.symCounts a' Cs carriers)) ω) :
    ∃ (ω' : WState (LNS x) LNR) (c h : ℕ), WExec cap ((numsP l F).liftW (fsN x) id) ω ω' c ∧
      ω'.st = ω.st ∧ ω'.sh = Function.update ω.sh (sk x 113) h ∧ h ≤ c ∧ ω'.cell = false ∧
      (∀ i, ω'.val (SymDec.G i) = SymDec.numsVec n (((gate0 l F).budget kclk coef A a ha).capOf .sym n)
        (F.filterErrDeg * Ledger.Lq n) (SymDec.cyOf Cs).sum carriers.length (Ledger.Lq n)
        (SeedFix.callKh ((callInputs l F kclk coef A a ha).starParams n hs)) a' ((SymDec.cyOf Cs).getD 0 0)
        ((SymDec.cyOf Cs).getD 1 0) ((SymDec.cyOf Cs).getD 2 0) ((SymDec.cyOf Cs).getD 3 0) i) ∧
      ω'.val SymDec.dN = n ∧ ω'.val SymDec.dA = a' ∧ ω'.val SymDec.dM0 = (SymDec.cyOf Cs).getD 0 0 ∧
      ω'.val SymDec.dM1 = (SymDec.cyOf Cs).getD 1 0 ∧ ω'.val SymDec.dM2 = (SymDec.cyOf Cs).getD 2 0 ∧
      ω'.val SymDec.dM3 = (SymDec.cyOf Cs).getD 3 0 ∧
      ω'.val (PrimT.C4Set.KB 52) = SeedFix.symCount (callInputs l F kclk coef A a ha) hs Cs carriers ∧
      (∀ q, ω'.val q ≤ cap₀) ∧ c ≤ 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) := by
  obtain ⟨τ, c, e, hG, hN, hA, h0, h1, h2, h3, hQ, hvl, hst, hsh, hcell, hcost⟩ :=
    numsAtG2 l F kclk coef A a ha ha' Cs carriers translation hcall hs cap₀ hc
  obtain ⟨ω', e', hL, hO⟩ := WExec.liftW cap₀ cap hcap (fsN x) (fsN_inj x) id Function.injective_id e ω
    (liftIn x _ _ ω hω)
  have hsl := WExec.sh_le cap₀ e (sk 0 113)
  have hsh0 : (CellLoopD.blankCellD 0 (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) [] 0
      (Data.unaryList (Data.symCounts a' Cs carriers))).sh (sk 0 113) = 0 := by
    simp [CellLoopD.blankCellD, CellState.blankCell, WState.sets]
  have hval : ∀ q, ω'.val q = τ.val q := fun q => hL.val q
  refine ⟨ω', c, τ.sh (sk 0 113), e', ?_, ?_, by omega, by rw [hL.cell, hcell], fun i => by rw [hval]; exact hG i,
    by rw [hval]; exact hN, by rw [hval]; exact hA, by rw [hval]; exact h0, by rw [hval]; exact h1, by rw [hval]; exact h2,
    by rw [hval]; exact h3, by rw [hval]; exact hQ, fun q => by rw [hval]; exact hvl q, hcost⟩
  · funext i
    by_cases hi : ∃ j, fsN x j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hL.st, hst, (liftIn x _ _ ω hω).st]
    · exact (hO.1 i (fun j e => hi ⟨j, e⟩)).2
  · funext i
    by_cases hi : ∃ j, fsN x j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [hL.sh]
      by_cases hj : j = sk 0 113
      · subst hj
        have e113 : fsN x (sk 0 113) = sk x 113 := rfl
        rw [e113, Function.update_self]
      · have hne : fsN x j ≠ sk x 113 := by
          intro e2
          apply hj
          have e113 : fsN x (sk 0 113) = sk x 113 := rfl
          exact fsN_inj x (e2.trans e113.symm)
        rw [Function.update_of_ne hne, hsh j hj, (liftIn x _ _ ω hω).sh]
    · have hne : i ≠ sk x 113 := fun e2 => hi ⟨sk 0 113, e2.symm ▸ rfl⟩
      rw [Function.update_of_ne hne]
      exact (hO.1 i (fun j e => hi ⟨j, e⟩)).1

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
