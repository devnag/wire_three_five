import Proof.Wire_3_5.Primitive.SeedFix.NwB8

/-! # NW phase (b), part 9: the register program before the docks, first half

**`wa1W`** (`wa1_spec`): from (c)'s exit (the input framed on `sIn`, every other stream blank, heads `0`, the
registers `n`, mode bit, `e`, `T_f` and nothing else): the saves `s0 … s3`, the request copied to stream `0`
(`inW`), phase A of the THR decode (`tAW`: `n`, `a'`, `|carriers|`, `|w|`, `k_h`, `f_e·L`), and `k_h`, `f_e·L` kept
in `sKH`, `sFL`; every register `≥ 270` outside `dN, dA, dNC, LEN` and the saves `0`.

Paper quantity of the main type: the call's numbers `n`, `k_h = s·⌊r/2⌋`, `f_e·L` of phase (b)'s value (P3:2987-3000,
3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

theorem fv {a b : Fin LNR} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

variable (cap : ℕ) (x : ℕ)

/-- **The first half before the docks.** -/
def wa1W (cr fe : ℕ) : WM (LNS x) LNR := .seq (saveW x) (.seq (inW x) (.seq (ThrDecF.tAW x cr fe) (keepW x)))

theorem wa1_spec (cr fe : ℕ) (P : Shared.StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (w : List Bool)
    (codes cc : List ℕ) (tl : List Bool) (hw : w = Data.reqW P.n true codes cc tl)
    (hKb : ∀ c ∈ codes, natBitLength c ≤ w.length) (σ : WState (LNS x) LNR) (vN vM vE vT : ℕ)
    (hin : σ.st (NumsPh2.sIn x) = frame w) (h0 : σ.st (sk x 0) = []) (hsh : ∀ i, σ.sh i = 0)
    (hN : σ.val NumsPh2.rN = vN) (hM : σ.val NumsPh2.rM = vM) (hE : σ.val NumsPh2.rE = vE)
    (hT : σ.val NumsPh2.rT = vT)
    (hz : ∀ q, q ≠ NumsPh2.rN → q ≠ NumsPh2.rM → q ≠ NumsPh2.rE → q ≠ NumsPh2.rT → σ.val q = 0)
    (cN : vN ≤ cap) (cM : vM ≤ cap) (cE : vE ≤ cap) (cT : vT ≤ cap) (hc1 : 2 * w.length + 2 ≤ cap)
    (hcP : 2 ^ (natBitLength P.n + 1) + 2 ^ (natBitLength codes.length + 1) + 2 ^ (natBitLength cc.length + 1) +
      w.length + P.n + codes.length + 1 ≤ cap)
    (hc3 : (fe + 4) * (P.n + 3) + 2 * cr + 20 ≤ cap)
    (hkc : P.s * (P.r / 2) ≤ cap) (hfc : fe * Nat.clog 2 (P.n + 2) ≤ cap) :
    ∃ τ c, WExec cap (wa1W x cr fe) σ τ c ∧
      c ≤ 7 * (vN + vM + vE + vT) + 8 + 1 + (40 * w.length + 60 * UnaryPow.sq cap + 1 +
        (ThrDecF.tACost P.n codes.length cc.length w.length cr fe cap + 1 +
          (7 * (P.s * (P.r / 2) + fe * Nat.clog 2 (P.n + 2)) + 4))) ∧
      τ.st (sk x 0) = frame w ∧ τ.st (NumsPh2.sIn x) = frame w ∧
      (∀ i, i ≠ sk x 0 → i ≠ NumsPh2.sIn x → τ.st i = σ.st i) ∧ (∀ i, τ.sh i = 0) ∧ τ.cell = σ.cell ∧
      τ.val s0 = vN ∧ τ.val s1 = vM ∧ τ.val s2 = vE ∧ τ.val s3 = vT ∧ τ.val sKH = P.s * (P.r / 2) ∧
      τ.val sFL = fe * Nat.clog 2 (P.n + 2) ∧ τ.val dN = P.n ∧ τ.val dNC = cc.length ∧ τ.val LEN = w.length ∧
      (∀ r : Fin LNR, 270 ≤ r.val → r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ LEN → (r.val < 450 ∨ 456 ≤ r.val) →
        τ.val r = 0) := by
  obtain ⟨τa, ca, ea, cale, aN, aM, aE, aT, a0, a1, a2, a3, afr, ast, ash, acl⟩ :=
    save_spec cap x σ vN vM vE vT hN hM hE hT (hz s0 (by decide) (by decide) (by decide) (by decide))
      (hz s1 (by decide) (by decide) (by decide) (by decide)) (hz s2 (by decide) (by decide) (by decide) (by decide))
      (hz s3 (by decide) (by decide) (by decide) (by decide)) cN cM cE cT
  have za : ∀ r, r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 → τa.val r = 0 := by
    intro r h0' h1' h2' h3'
    by_cases e1 : r = NumsPh2.rN
    · rw [e1]; exact aN
    by_cases e2 : r = NumsPh2.rM
    · rw [e2]; exact aM
    by_cases e3 : r = NumsPh2.rE
    · rw [e3]; exact aE
    by_cases e4 : r = NumsPh2.rT
    · rw [e4]; exact aT
    rw [afr r e1 e2 e3 e4 h0' h1' h2' h3']; exact hz r e1 e2 e3 e4
  obtain ⟨τb, cb, eb, cble, b0, b0h, bIn, bInh, bo, bv, bcl⟩ := in_spec cap x w τa (by rw [ast]; exact hin)
    (by rw [ash]; exact hsh _) (by rw [ast]; exact h0) (by rw [ash]; exact hsh _)
    (za rL (by decide) (by decide) (by decide) (by decide)) (za rC (by decide) (by decide) (by decide) (by decide))
    (za rTm (by decide) (by decide) (by decide) (by decide)) hc1
  have zb : ∀ r : Fin LNR, 250 ≤ r.val → r.val < 400 → τb.val r = 0 := fun r h1 h2 => by
    rw [bv]
    exact za r (fv (by show r.val ≠ 450; omega)) (fv (by show r.val ≠ 451; omega)) (fv (by show r.val ≠ 452; omega))
      (fv (by show r.val ≠ 453; omega))
  obtain ⟨τc, c3, ec, c3le, cN', cA, cNC, cL, c8, c10, cfr, cst, csh, ccl⟩ :=
    ThrDecF.tA_run cap x cr fe P hrP τb w true codes cc tl w.length hw hKb b0 b0h zb hc1 hcP hc3
  have zc : ∀ r : Fin LNR, 270 ≤ r.val → r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ LEN → r ≠ s0 → r ≠ s1 → r ≠ s2 → r ≠ s3 →
      τc.val r = 0 := fun r h1 k1 k2 k3 k4 n0 n1 n2 n3 => by
    rw [cfr r k1 k2 k3 k4 (Or.inr h1), bv]; exact za r n0 n1 n2 n3
  obtain ⟨τd, c4, ed, c4le, dK, dF, dfr, dst, dsh, dcl⟩ := keep_spec cap x τc _ _ c8 c10
    (zc sKH (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))
    (zc sFL (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) hkc hfc
  have kS : ∀ r : Fin LNR, 270 ≤ r.val → (r.val < 454 ∨ 456 ≤ r.val) → τd.val r = τc.val r := fun r h1 h2 =>
    dfr r (fv (by show r.val ≠ 258; omega)) (fv (by show r.val ≠ 260; omega)) (fv (by show r.val ≠ 454; omega))
      (fv (by show r.val ≠ 455; omega))
  have kT : ∀ r : Fin LNR, 270 ≤ r.val → r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ LEN → τc.val r = τa.val r :=
    fun r h1 k1 k2 k3 k4 => by rw [cfr r k1 k2 k3 k4 (Or.inr h1), bv]
  refine ⟨τd, _, WExec.seq ea (WExec.seq eb (WExec.seq ec ed)), by omega, by rw [dst, cst]; exact b0,
    by rw [dst, cst]; exact bIn, fun i hi0 hiI => by rw [dst, cst, (bo i hi0 hiI).1, ast], fun i => ?_,
    by rw [dcl, ccl, bcl, acl], ?_, ?_, ?_, ?_, dK, dF, ?_, ?_, ?_, ?_⟩
  · rw [dsh, csh]
    by_cases e0 : i = sk x 0
    · rw [e0]; exact b0h
    by_cases eI : i = NumsPh2.sIn x
    · rw [eI]; exact bInh
    rw [(bo i e0 eI).2, ash]; exact hsh i
  · rw [kS s0 (by decide) (by decide), kT s0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a0
  · rw [kS s1 (by decide) (by decide), kT s1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a1
  · rw [kS s2 (by decide) (by decide), kT s2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a2
  · rw [kS s3 (by decide) (by decide), kT s3 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a3
  · rw [kS dN (by decide) (by decide)]; exact cN'
  · rw [kS dNC (by decide) (by decide)]; exact cNC
  · rw [kS LEN (by decide) (by decide)]; exact cL
  · intro r h1 k1 k2 k3 k4 hr
    have hr' : r.val < 454 ∨ 456 ≤ r.val := by omega
    rw [kS r h1 hr']
    exact zc r h1 k1 k2 k3 k4 (fv (by show r.val ≠ 450; omega)) (fv (by show r.val ≠ 451; omega))
      (fv (by show r.val ≠ 452; omega)) (fv (by show r.val ≠ 453; omega))

/-- The star block `SGb = 250 … 269`, as a list. -/
def sgList : List (Fin LNR) := (List.finRange 20).map SGb

theorem sg_mem (i : Fin 20) : SGb i ∈ sgList := List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩

theorem sg_nmem (r : Fin LNR) (h : r.val < 250 ∨ 270 ≤ r.val) : r ∉ sgList := fun hm => by
  obtain ⟨i, -, hi⟩ := List.mem_map.1 hm
  have := congrArg Fin.val hi; rw [SGb_val] at this; have := i.isLt; omega

section W2
variable {alg : RepairRepresentation.DecompositionAlgorithm} {Dexp : ℕ}
  (T : PrimThrW.PortsE.TopFrontPort3 alg) (N : PrimThrW.Nums4.NumsPort4 alg Dexp)

/-- **The second half before the docks**: the star block cleared, `cap_T` (`capTW`), `Hb 0, Hb 1 := |carriers|,
cap_T`, the pre-dock program. -/
def wa2W (hx : ThrDecF.dX T N ≤ x) (cr : ℕ) (ζ : ℚ) (Cδ : ℕ) (C : Ledger.CapParams) : WM (LNS x) LNR :=
  .seq (NumsC.clearL sgList) (.seq (TS4.capTW x cr ζ Cδ C) (.seq (setHbW x) (ThrDecF.pbPreW T N x hx)))

theorem wa2_spec (hx : ThrDecF.dX T N ≤ x) (cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2) (Cδ : ℕ)
    (C : Ledger.CapParams) (n ncar len : ℕ) (w : List Bool) (σ : WState (LNS x) LNR)
    (hreq : σ.st (sk x 0) = frame w) (hreqh : σ.sh (sk x 0) = 0)
    (hbl : ∀ i : Fin (LNS x + 1), (130 ≤ i.val ∧ i.val ≤ 136) ∨ 161 ≤ i.val → σ.st i = [])
    (hhd : ∀ i : Fin (LNS x + 1), (130 ≤ i.val ∧ i.val ≤ 136) ∨ 161 ≤ i.val → σ.sh i = 0)
    (hN : σ.val dN = n) (hC : σ.val dNC = ncar) (hL : σ.val LEN = len)
    (hZ : ∀ r : Fin LNR, 270 ≤ r.val → r ≠ dN → r ≠ dA → r ≠ dNC → r ≠ LEN → (r.val < 450 ∨ 456 ≤ r.val) →
      σ.val r = 0)
    (hb : ∀ r, σ.val r ≤ cap)
    (hcS : 4 * n + 2 * cr + 20 ≤ cap)
    (hcP : SparseNum.sparseBound ζ Cδ (Ledger.Lq n) (Ledger.rowBt h0 h1 n - 1) ≤ cap)
    (hcC : SymDec.CapNeed C .thr n (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) cap)
    (hcA : len + (n + 1) ^ 26 * 2 + n + Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n +
      42 ≤ cap)
    (hCn : N.Cn ≤ cap)
    (hPD : (n + Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n + 1) ^ N.Dn ≤ cap)
    (hcB : ThrDecF.tV len n (Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n) N.Cn N.Dn +
      n + Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n + ncar + 42 ≤ cap) :
    ∃ τ c, WExec cap (wa2W x T N hx cr ζ Cδ C) σ τ c ∧
      c ≤ 20 * (3 * cap + 2) + 1 + (TS4.capTCost cap n cr (Ledger.rowBt h0 h1 n) (Ledger.rowBSparse h0 h1 2 Cδ n)
        (Ledger.Lq n) + 1 + (6 * cap + 6 + 2 * UnaryPow.sq cap + 1 + (150 * UnaryPow.sq cap +
        (N.Dn + 1) * (4 * UnaryPow.sq cap) + 40 * (ThrDecF.tV len n (Ledger.rowBCap C .thr (Ledger.rowBr cr n)
          (Ledger.rowBSparse h0 h1 2 Cδ n) n) N.Cn N.Dn + ncar +
          Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n) + 40))) ∧
      ThrDecF.DockInT T N x τ w (ThrDecF.tV len n (Ledger.rowBCap C .thr (Ledger.rowBr cr n)
        (Ledger.rowBSparse h0 h1 2 Cδ n) n) N.Cn N.Dn) ncar
        (Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n) ∧
      τ.val ThrDec.rRadK = 1 ∧
      (∀ r : Fin LNR, 400 ≤ r.val → r.val < 492 → (r.val < 450 ∨ 456 ≤ r.val) → τ.val r = 0) ∧
      (∀ r : Fin LNR, 450 ≤ r.val → r.val < 456 → τ.val r = σ.val r) ∧ τ.val dN = n ∧
      τ.val (Hb 13) = Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n ∧
      (∀ i : Fin (LNS x + 1), (i.val < 161 + ThrDecF.bT T N ∨ 161 + ThrDecF.bT T N + 3 ≤ i.val) → τ.st i = σ.st i) ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  obtain ⟨c1, e1, c1le⟩ := NumsC.clearL_spec cap cap le_rfl sgList σ (fun r _ => hb r)
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = NumsC.zeroL σ sgList := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have k1 : ∀ r : Fin LNR, (r.val < 250 ∨ 270 ≤ r.val) → σ1.val r = σ.val r := fun r h => by
    rw [hσ1, zeroL_val', if_neg (sg_nmem r h)]
  have st1 : σ1.st = σ.st := by rw [hσ1]; exact zeroL_st' x σ sgList
  have sh1 : σ1.sh = σ.sh := by rw [hσ1]; exact zeroL_sh' x σ sgList
  have cl1 : σ1.cell = σ.cell := by rw [hσ1]; exact zeroL_cell' x σ sgList
  have hSG : ∀ i, σ1.val (SGb i) = 0 := fun i => by rw [hσ1, zeroL_val', if_pos (sg_mem i)]
  have hG : ∀ i, σ1.val (Gb i) = 0 := fun i => by
    have := i.isLt
    rw [k1 _ (Or.inr (by rw [Gb_val]; omega))]
    exact hZ _ (by rw [Gb_val]; omega) (fv (by rw [Gb_val]; show 270 + i.val ≠ 320; omega))
      (fv (by rw [Gb_val]; show 270 + i.val ≠ 321; omega)) (fv (by rw [Gb_val]; show 270 + i.val ≠ 322; omega))
      (fv (by rw [Gb_val]; show 270 + i.val ≠ 369; omega)) (Or.inl (by rw [Gb_val]; omega))
  have hH : ∀ i, σ1.val (Hb i) = 0 := fun i => by
    have := i.isLt
    rw [k1 _ (Or.inr (by rw [Hb_val]; omega))]
    exact hZ _ (by rw [Hb_val]; omega) (fv (by rw [Hb_val]; show 337 + i.val ≠ 320; omega))
      (fv (by rw [Hb_val]; show 337 + i.val ≠ 321; omega)) (fv (by rw [Hb_val]; show 337 + i.val ≠ 322; omega))
      (fv (by rw [Hb_val]; show 337 + i.val ≠ 369; omega)) (Or.inl (by rw [Hb_val]; omega))
  have hxT : σ1.val xT = 0 := by
    rw [k1 _ (Or.inr (by decide))]
    exact hZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  obtain ⟨τ2, c2, e2, v13, o2, st2, sh2, cl2, c2le⟩ := TS4.capT_spec cap x cr h0 h1 Cδ C n σ1
    (by rw [k1 _ (Or.inr (by decide))]; exact hN) hSG hG hH hxT hcS hcP hcC
  have k2 : ∀ r : Fin LNR, 369 ≤ r.val → τ2.val r = σ.val r := fun r h => by
    rw [o2 r ⟨Or.inr (by omega), by omega, Or.inr h⟩, k1 r (Or.inr (by omega))]
  have k2' : ∀ r : Fin LNR, 294 ≤ r.val → r.val < 337 → r.val ≠ 296 → τ2.val r = σ.val r := fun r h1' h2' h3' => by
    rw [o2 r ⟨Or.inr h1', h3', Or.inl h2'⟩, k1 r (Or.inr (by omega))]
  have zC2 : τ2.val dNC = ncar := by rw [k2' dNC (by decide) (by decide) (by decide)]; exact hC
  have zT2 : τ2.val rTm = 0 := by
    rw [k2 rTm (by decide)]
    exact hZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inr (by decide))
  obtain ⟨τ3, c3, e3, c3le, h30, h31, o3, st3, sh3, cl3⟩ := setHb_spec cap x τ2 ncar _ zC2 v13 zT2
    (FinalPass.S5T.WExec.val_le cap e2 (FinalPass.S5T.WExec.val_le cap e1 hb))
  have k3 : ∀ r : Fin LNR, 369 ≤ r.val → τ3.val r = σ.val r := fun r h => by
    rw [o3 r (fv (by show r.val ≠ 337; omega)) (fv (by show r.val ≠ 338; omega)), k2 r h]
  have zL3 : τ3.val LEN = len := by rw [k3 LEN (by decide)]; exact hL
  have zN3 : τ3.val dN = n := by
    rw [o3 dN (by decide) (by decide), k2' dN (by decide) (by decide) (by decide)]
    exact hN
  have zH3 : ∀ k : Fin 40, 20 ≤ k.val → τ3.val (H k) = 0 := fun k hk => by
    have := k.isLt
    rw [k3 _ (by show 369 ≤ 472 + k.val; omega)]
    exact hZ _ (by show 270 ≤ 472 + k.val; omega) (fv (by show 472 + k.val ≠ 320; omega))
      (fv (by show 472 + k.val ≠ 321; omega)) (fv (by show 472 + k.val ≠ 322; omega))
      (fv (by show 472 + k.val ≠ 369; omega)) (Or.inr (by show 456 ≤ 472 + k.val; omega))
  have zTM3 : τ3.val TM = 0 := by
    rw [k3 TM (by decide)]
    exact hZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  have zR3 : τ3.val ThrDec.rRadK = 0 := by
    rw [k3 ThrDec.rRadK (by decide)]
    exact hZ _ (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))
  obtain ⟨τ4, c4, e4, c4le, dIn, dR, dH, o4, st4, sh4, cl4⟩ := pbPre_run' T N cap x hx τ3 w len n
    (Ledger.rowBCap C .thr (Ledger.rowBr cr n) (Ledger.rowBSparse h0 h1 2 Cδ n) n) ncar
    (by rw [st3, st2, st1]; exact hreq) (by rw [sh3, sh2, sh1]; exact hreqh)
    (fun i hi => by rw [st3, st2, st1]; exact hbl i hi) (fun i hi => by rw [sh3, sh2, sh1]; exact hhd i hi)
    zL3 zN3 h30 h31 zH3 zTM3 zR3 hcA hCn hPD hcB
  have hsl : sgList.length = 20 := by simp [sgList]
  rw [hsl] at c1le
  refine ⟨τ4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega, dIn, dR, fun r h1' h2' h3' => ?_,
    fun r h1' h2' => ?_, ?_, ?_, fun i hi => by rw [st4 i hi, st3, st2, st1], by rw [sh4, sh3, sh2, sh1],
    by rw [cl4, cl3, cl2, cl1]⟩
  · rw [o4 r (fv (by show r.val ≠ 398; omega)) (fv (by show r.val ≠ 492; omega)), k3 r (by omega)]
    exact hZ r (by omega) (fv (by show r.val ≠ 320; omega)) (fv (by show r.val ≠ 321; omega))
      (fv (by show r.val ≠ 322; omega)) (fv (by show r.val ≠ 369; omega)) h3'
  · rw [o4 r (fv (by show r.val ≠ 398; omega)) (fv (by show r.val ≠ 492; omega)), k3 r (by omega)]
  · rw [o4 dN (by decide) (by decide)]; exact zN3
  · rw [o4 (Hb 13) (by decide) (by decide), o3 (Hb 13) (by decide) (by decide)]; exact v13

end W2

end NearCubicWires.WireExponent3_5.PrimT.NwB
