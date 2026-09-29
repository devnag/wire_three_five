import Proof.Wire_3_5.Primitive.Writers.SBCap2

/-! # SB: the capacity target, part 3 — **`sbCap : StarRStmt l → SBCapStmt l`**

`sbNeed ≤ KcF l F·(N+1)^{DD l}` at every star request (`N = |fpIn r|`): the phase sums, the cap
(`CallIndexR.cap_leR`), the sparse bound (`SymSizes.sparse_le_gate`, `TS4.spT_le`), `λ` (`SymSizes.lambda_le`), `t`
(`SymSizes.rowBt_le`), the counts (the envelope), the input length, the carrier pipeline's `2^{DtC}(N+1)^{DtC}`.

Paper quantity of the main type: SB's capacity (`prim:runtime`, P3:3105-3115; P3:3114-3115). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.FinalPass.Out.Car NearCubicWires.WireExponent3_5.FinalPass.Out.CarBound

theorem carCnt_le {n : ℕ} (cs : List (Stars.Carrier n)) (h : ∀ X ∈ cs, X.WithinEnvelope 26) (k : ℕ) :
    carCnt cs k ≤ (n + 1) ^ 26 := by
  unfold carCnt; split
  · exact (h _ (List.get_mem _ _)).1
  · exact Nat.zero_le _

/-- The capacity degree (the literals only). -/
noncomputable def DD (l : Literals) : ℕ := 26 + CallIndexR.capZR l + PrimT.TS4.spA l + PrimT.TS4.ZmL l + DtC + 3

/-- The capacity coefficient at a gate. -/
noncomputable def KcF (l : Literals) (F : GateFree l) : ℕ :=
  10 ^ 8 * (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l + 4 * F.filterErrDeg + 16) +
    2 ^ PrimT.TS4.spB l * 4 ^ PrimT.TS4.spA l +
    (2 ^ 40 * CallIndexR.capK F.cr * 2 ^ PrimT.TS4.ZmL l + CapNum.cMain (gateCap l) .thr +
      CapNum.cMain (gateCap l) .sym) +
    8 * SymSizes.KLam l + (3 * SymSizes.schedJ l + 1) + 6 + 2 ^ DtC + 3 * (F.filterErrDeg + 4) + 2 * F.cr + 20

theorem pow_up (N d D : ℕ) (h : d ≤ D) : (N + 1) ^ d ≤ (N + 1) ^ D := Nat.pow_le_pow_right (by omega) h

/-- **SB's capacity target, proved** (from the star identification `StarRStmt`). -/
theorem sbCap (l : Literals) (hR : SBIdent.StarRStmt l) : SBCapStmt l := by
  refine ⟨KcF l, fun _ => DD l, fun F kclk coef A a ha r hs => ?_⟩
  obtain ⟨hPr, -⟩ := hR F kclk coef A a ha r.1.n hs
  have hn : r.1.n ≤ (fpIn l F kclk coef A a ha r).length := FpInLen.n_le_fpIn r
  have henv : ∀ X ∈ r.1.carriers, X.WithinEnvelope 26 := r.2.2.1
  have hk : r.1.carriers.length ≤ 2 := r.2.2.2.2.1
  have hZ := sbNeed_Z l F.cr F.filterErrDeg ((callInputs l F kclk coef A a ha).starParams r.1.n hs) r.1.mode
    (fpIn l F kclk coef A a ha r).length (carCnt r.1.carriers 0) (carCnt r.1.carriers 1) r.1.carriers.length
  have hPn : ((callInputs l F kclk coef A a ha).starParams r.1.n hs).n = r.1.n := rfl
  simp only [hPn] at hZ
  have hc0 := carCnt_le r.1.carriers henv 0
  have hc1 := carCnt_le r.1.carriers henv 1
  -- the donors at `n`
  have hcap : Ledger.rowBCap (gateCap l) r.1.mode ((callInputs l F kclk coef A a ha).starParams r.1.n hs).r
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) r.1.n) r.1.n ≤
      CallIndexR.capK F.cr * (r.1.n + 2) ^ CallIndexR.capZR l := by
    rw [hPr]; exact CallIndexR.cap_leR l F.cr r.1.mode r.1.n
  have hsp : SparseNum.sparseBound (gateCParams1 l).ζ (gateCδ1 l) (Ledger.Lq r.1.n)
      (Ledger.rowBt (gateZeta_pos l) (gateZeta_lt l) r.1.n - 1) ≤
      2 ^ PrimT.TS4.spB l * 4 ^ PrimT.TS4.spA l * (r.1.n + 1) ^ PrimT.TS4.spA l :=
    (SymSizes.sparse_le_gate l r.1.n).trans (PrimT.TS4.spT_le l r.1.n)
  have hlam := SymSizes.lambda_le l r.1.n
  have hbt := SymSizes.rowBt_le l r.1.n
  have hcl := clog_le (r.1.n + 2)
  have hW : 2 ^ (natBitLength r.1.n + 1) ≤ 4 * (r.1.n + 1) := by
    rw [pow_succ]; have := two_pow_nbl_le r.1.n; omega
  have hcm : CapNum.cMain (gateCap l) r.1.mode ≤
      CapNum.cMain (gateCap l) .thr + CapNum.cMain (gateCap l) .sym := by cases r.1.mode <;> omega
  -- powers of `N + 1`
  obtain ⟨N, hNd⟩ : ∃ N, N = (fpIn l F kclk coef A a ha r).length := ⟨_, rfl⟩
  rw [← hNd] at hZ hn ⊢
  have hDz : CallIndexR.capZR l ≤ DD l := by unfold DD; omega
  have hDa : PrimT.TS4.spA l ≤ DD l := by unfold DD; omega
  have hDm : PrimT.TS4.ZmL l ≤ DD l := by unfold DD; omega
  have hDt : DtC ≤ DD l := by unfold DD; omega
  have p26 : (r.1.n + 1) ^ 26 ≤ (N + 1) ^ DD l :=
    (Nat.pow_le_pow_left (by omega) 26).trans (pow_up N 26 _ (by unfold DD; omega))
  have p1 : N + 1 ≤ (N + 1) ^ DD l := by
    have := pow_up N 1 (DD l) (by unfold DD; omega); rwa [pow_one] at this
  have p2 : r.1.n * r.1.n ≤ (N + 1) ^ DD l := by
    have h2 : r.1.n * r.1.n ≤ (N + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    exact h2.trans (pow_up N 2 _ (by unfold DD; omega))
  have pz : (r.1.n + 2) ^ CallIndexR.capZR l ≤ 2 ^ CallIndexR.capZR l * (N + 1) ^ DD l :=
    (PrimT.TS4.two_pow_le _ _).trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans (pow_up N _ _ hDz)))
  have pa : (r.1.n + 1) ^ PrimT.TS4.spA l ≤ (N + 1) ^ DD l := (Nat.pow_le_pow_left (by omega) _).trans (pow_up N _ _ hDa)
  have pm : (r.1.n + 2) ^ PrimT.TS4.ZmL l ≤ 2 ^ PrimT.TS4.ZmL l * (N + 1) ^ DD l :=
    (PrimT.TS4.two_pow_le _ _).trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by omega) _).trans (pow_up N _ _ hDm)))
  have p3 : (r.1.n + 2) ^ 3 ≤ 8 * (N + 1) ^ DD l := by
    have h3 : (r.1.n + 2) ^ 3 ≤ (2 * (N + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [mul_pow] at h3
    exact h3.trans (Nat.mul_le_mul_left _ (pow_up N 3 _ (by unfold DD; omega)))
  have pt : (N + 1) ^ DtC ≤ (N + 1) ^ DD l := pow_up N _ _ hDt
  have e1 : CallIndexR.capK F.cr * (r.1.n + 2) ^ CallIndexR.capZR l ≤
      (CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l) * (N + 1) ^ DD l := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ pz
  have e2 : 2 ^ PrimT.TS4.spB l * 4 ^ PrimT.TS4.spA l * (r.1.n + 1) ^ PrimT.TS4.spA l ≤
      (2 ^ PrimT.TS4.spB l * 4 ^ PrimT.TS4.spA l) * (N + 1) ^ DD l := Nat.mul_le_mul_left _ pa
  have e3 : 2 ^ 40 * (CallIndexR.capK F.cr * (r.1.n + 2) ^ PrimT.TS4.ZmL l) ≤
      (2 ^ 40 * CallIndexR.capK F.cr * 2 ^ PrimT.TS4.ZmL l) * (N + 1) ^ DD l := by
    have := Nat.mul_le_mul_left (2 ^ 40 * CallIndexR.capK F.cr) pm
    calc 2 ^ 40 * (CallIndexR.capK F.cr * (r.1.n + 2) ^ PrimT.TS4.ZmL l)
        = 2 ^ 40 * CallIndexR.capK F.cr * (r.1.n + 2) ^ PrimT.TS4.ZmL l := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have e4 : SymSizes.KLam l * (r.1.n + 2) ^ 3 ≤ (8 * SymSizes.KLam l) * (N + 1) ^ DD l := by
    have := Nat.mul_le_mul_left (SymSizes.KLam l) p3
    calc SymSizes.KLam l * (r.1.n + 2) ^ 3 ≤ SymSizes.KLam l * (8 * (N + 1) ^ DD l) := this
      _ = _ := by ring
  have e5 : SymSizes.schedJ l * (Nat.clog 2 (r.1.n + 2) + 1) ≤ (3 * SymSizes.schedJ l) * (N + 1) ^ DD l := by
    have := Nat.mul_le_mul_left (SymSizes.schedJ l) (show Nat.clog 2 (r.1.n + 2) + 1 ≤ 3 * (N + 1) ^ DD l by omega)
    calc SymSizes.schedJ l * (Nat.clog 2 (r.1.n + 2) + 1) ≤ SymSizes.schedJ l * (3 * (N + 1) ^ DD l) := this
      _ = _ := by ring
  have e6 : F.filterErrDeg * (2 * r.1.n + 4) ≤ (4 * F.filterErrDeg) * (N + 1) ^ DD l := by
    have := Nat.mul_le_mul_left F.filterErrDeg (show 2 * r.1.n + 4 ≤ 4 * (N + 1) ^ DD l by omega)
    calc F.filterErrDeg * (2 * r.1.n + 4) ≤ F.filterErrDeg * (4 * (N + 1) ^ DD l) := this
      _ = _ := by ring
  have e7 : (F.filterErrDeg + 4) * (r.1.n + 3) ≤ (3 * (F.filterErrDeg + 4)) * (N + 1) ^ DD l := by
    have := Nat.mul_le_mul_left (F.filterErrDeg + 4) (show r.1.n + 3 ≤ 3 * (N + 1) ^ DD l by omega)
    calc (F.filterErrDeg + 4) * (r.1.n + 3) ≤ (F.filterErrDeg + 4) * (3 * (N + 1) ^ DD l) := this
      _ = _ := by ring
  have e8 : 2 ^ DtC * (N + 1) ^ DtC ≤ 2 ^ DtC * (N + 1) ^ DD l := Nat.mul_le_mul_left _ pt
  have e9 : 2 * F.cr + 20 ≤ (2 * F.cr + 20) * (N + 1) ^ DD l := Nat.le_mul_of_pos_right _ (by omega)
  have hZm : (80 + 48 + (gateCsp l + 3) * 32 + 64 + gateBetaInv l * 32) = PrimT.TS4.ZmL l := rfl
  rw [hZm] at hZ
  unfold KcF
  generalize (N + 1) ^ DD l = PD at p26 p1 p2 pz pa pm p3 pt e1 e2 e3 e4 e5 e6 e7 e8 e9 ⊢
  generalize CallIndexR.capK F.cr * 2 ^ CallIndexR.capZR l = K1 at e1 ⊢
  generalize 2 ^ PrimT.TS4.spB l * 4 ^ PrimT.TS4.spA l = K2 at e2 hsp ⊢
  generalize 2 ^ 40 * CallIndexR.capK F.cr * 2 ^ PrimT.TS4.ZmL l = K3 at e3 ⊢
  have hexp : (10 ^ 8 * (K1 + 4 * F.filterErrDeg + 16) + K2 + (K3 + CapNum.cMain (gateCap l) .thr +
      CapNum.cMain (gateCap l) .sym) + 8 * SymSizes.KLam l + (3 * SymSizes.schedJ l + 1) + 6 + 2 ^ DtC +
      3 * (F.filterErrDeg + 4) + 2 * F.cr + 20) * PD =
      10 ^ 8 * (K1 * PD) + 10 ^ 8 * ((4 * F.filterErrDeg) * PD) + 16 * 10 ^ 8 * PD + K2 * PD + K3 * PD +
      (CapNum.cMain (gateCap l) .thr + CapNum.cMain (gateCap l) .sym) * PD + (8 * SymSizes.KLam l) * PD +
      (3 * SymSizes.schedJ l) * PD + PD + 6 * PD + 2 ^ DtC * PD + (3 * (F.filterErrDeg + 4)) * PD +
      (2 * F.cr + 20) * PD := by ring
  rw [hexp]
  have hcmP : CapNum.cMain (gateCap l) r.1.mode ≤
      (CapNum.cMain (gateCap l) .thr + CapNum.cMain (gateCap l) .sym) * PD :=
    hcm.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hsp2 := hsp.trans e2
  clear hexp
  generalize K1 * PD = A1 at e1 ⊢
  generalize (4 * F.filterErrDeg) * PD = A2 at e6 ⊢
  generalize K2 * PD = A3 at e2 hsp2 ⊢
  generalize K3 * PD = A4 at e3 ⊢
  generalize (CapNum.cMain (gateCap l) .thr + CapNum.cMain (gateCap l) .sym) * PD = A5 at hcmP ⊢
  generalize (8 * SymSizes.KLam l) * PD = A6 at e4 ⊢
  generalize (3 * SymSizes.schedJ l) * PD = A7 at e5 ⊢
  generalize 2 ^ DtC * PD = A8 at e8 ⊢
  generalize (3 * (F.filterErrDeg + 4)) * PD = A9 at e7 ⊢
  generalize (2 * F.cr + 20) * PD = A10 at e9 ⊢
  clear * - hZ hc0 hc1 hk hcap hsp2 hlam hbt hW hcmP p26 p1 p2 e1 e3 e4 e5 e6 e7 e8 e9 hn
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm