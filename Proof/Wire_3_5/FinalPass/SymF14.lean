import Proof.Wire_3_5.FinalPass.SymF13

/-! # SWf (the SYM words writer's flat tables), part 14: the flat tables' writer `SWfT l`

The flat part `swfM l W F` (part 13) is a SYM-guarded word writer: **`swf W l : SWParts.SWfT l`**, with
the register capacity `KcW F·(|fpIn|+1)^{DkW fe}` and the step and residue bound `CsW F·(|fpIn|+1)^{DsW fe}` (degrees
on `l` and the filter degree `fe` only, coefficients on `l` and the gate).

* `cXP`, `BCP`, `BDP`; **`bud_symP`**: each of the four writers' budgets `budP ≤ BCP·(|fpIn|+1)^{BDP}` at a SYM request
  (`Sd.bud_poly` at the writer's dimension `2^m ≤ Q²(n+2)²`, `Q ≤ |fpIn|`, `n ≤ |fpIn|`);
* `KcW`, `DkW`, `CsW`, `DsW`; `cap_arith` (the front's and the requests' needs below the capacity), `swf_cost` (the
  steps and the residues below the bound);
* **`swf_runG`** (the run at a SYM request, words `SWParts.swWs l 8 4`), **`swf`**.

Paper quantity of the main type: the SYM call words `4·2 + c` (circuit `c`'s list seeds' flat tables, list:flatten
P3:1508-1520, P3:3170-3178) at every SYM request, on the writer's output streams, in time polynomial in the input. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimT.WalkBank NearCubicWires.SupplierPipeline NearCubicWires.BlockPlatform

/-! ## Arithmetic -/

/-- The front's and the requests' needs below `(K_F + C_F + 64c_X + 20)·X^{D_F + D_Fs + E₀}`. -/
theorem cap_arith (KF CF cX X DF DFs E0 n lw : ℕ) (hn : n + 1 ≤ X) (hE0 : 1 ≤ E0)
    (hlw : lw ≤ 16 * (cX * X ^ E0)) :
    KF * X ^ DF ≤ (KF + CF + 64 * cX + 20) * X ^ (DF + DFs + E0) ∧
    CF * X ^ DFs ≤ (KF + CF + 64 * cX + 20) * X ^ (DF + DFs + E0) ∧
    n + 4 * lw + 10 ≤ (KF + CF + 64 * cX + 20) * X ^ (DF + DFs + E0) := by
  have hX : 1 ≤ X := by omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (DF + DFs + E0) := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ d, d ≤ DF + DFs + E0 → X ^ d ≤ Y := fun d hd => by rw [hY]; exact Nat.pow_le_pow_right hX hd
  have p1 := pw DF (by omega)
  have p2 := pw DFs (by omega)
  have p3 := pw E0 (by omega)
  have p4 : X ≤ Y := by
    have := pw 1 (by omega)
    rwa [pow_one] at this
  have q1 : KF * X ^ DF ≤ KF * Y := Nat.mul_le_mul_left _ p1
  have q2 : CF * X ^ DFs ≤ CF * Y := Nat.mul_le_mul_left _ p2
  have q3 : cX * X ^ E0 ≤ cX * Y := Nat.mul_le_mul_left _ p3
  have e : (KF + CF + 64 * cX + 20) * Y = KF * Y + CF * Y + 64 * (cX * Y) + 20 * Y := by ring
  rw [e]
  exact ⟨by omega, by omega, by omega⟩

/-- The flat part's steps and residues below `(C_F + 1566K_c + 3200c_X + 4B_C + 20000)·X^{D_k + B_D + 2}`. -/
theorem swf_cost (CF Kc cX BC X DFs Dk BD E0 n lw : ℕ) (B : Fin 4 → ℕ) (hn : n + 1 ≤ X) (h1 : DFs ≤ Dk)
    (h2 : E0 ≤ Dk) (hlw : lw ≤ 16 * (cX * X ^ E0)) (hB : ∀ c, B c ≤ BC * X ^ BD) :
    CF * X ^ DFs + 1 + tailCost (Kc * X ^ Dk) B n lw ≤
      (CF + 1566 * Kc + 3200 * cX + 4 * BC + 20000) * X ^ (Dk + BD + 2) ∧
    CF * X ^ DFs + 2 * lw + 1 + (B 0 + B 1 + B 2 + B 3) ≤
      (CF + 1566 * Kc + 3200 * cX + 4 * BC + 20000) * X ^ (Dk + BD + 2) := by
  have hX : 1 ≤ X := by omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = X ^ (Dk + BD + 2) := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ d, d ≤ Dk + BD + 2 → X ^ d ≤ Y := fun d hd => by rw [hY]; exact Nat.pow_le_pow_right hX hd
  have p1 := pw DFs (by omega)
  have p2 := pw Dk (by omega)
  have p3 := pw E0 (by omega)
  have p4 := pw BD (by omega)
  have p5 : X * X ≤ Y := by
    have := pw 2 (by omega)
    rwa [sq] at this
  have hY1 : 1 ≤ Y := by
    have := pw 0 (by omega)
    rwa [pow_zero] at this
  have q1 : CF * X ^ DFs ≤ CF * Y := Nat.mul_le_mul_left _ p1
  have q2 : Kc * X ^ Dk ≤ Kc * Y := Nat.mul_le_mul_left _ p2
  have q3 : cX * X ^ E0 ≤ cX * Y := Nat.mul_le_mul_left _ p3
  have q4 : ∀ c, B c ≤ BC * Y := fun c => (hB c).trans (Nat.mul_le_mul_left _ p4)
  have b0 := q4 0
  have b1 := q4 1
  have b2 := q4 2
  have b3 := q4 3
  have hbl : natBitLength n ≤ n + 1 := Nat.add_le_add_right (Nat.log_le_self _ _) 1
  have rc : Sd.reqCost n lw ≤ 2200 * (X * X) + 50 * lw + 200 := by
    unfold Sd.reqCost
    have h : (natBitLength n + 10) * (100 * n + 200) ≤ (11 * X) * (200 * X) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (11 * X) * (200 * X) = 2200 * (X * X) := by ring
    omega
  have e : (CF + 1566 * Kc + 3200 * cX + 4 * BC + 20000) * Y =
      CF * Y + 1566 * (Kc * Y) + 3200 * (cX * Y) + 4 * (BC * Y) + 20000 * Y := by ring
  rw [e]
  unfold tailCost
  exact ⟨by omega, by omega⟩

/-! ## The constants -/

section Consts
variable (l : Literals)

/-- The budgets' base coefficient `K₀·2^{E₀}` (on `c_r` and `l`). -/
noncomputable def cXP (cr : ℕ) : ℕ := K0P cr * 2 ^ E0P l

/-- **The flat tables writer's budget coefficient** (on `c_r` and `l`). -/
noncomputable def BCP (cr : ℕ) : ℕ :=
  Sd.budC (9 * E0P l) (CWP (K0P cr)) (E0P l) (K0P cr) cr (cXP l cr) ThrData.thrDataStage2.Cc ThrData.thrDataStage2.Dc

/-- **The flat tables writer's budget degree** (on `l`). -/
noncomputable def BDP : ℕ := Sd.budD (9 * E0P l) (E0P l) (E0P l) ThrData.thrDataStage2.Dc

/-- The register capacity's coefficient (on the gate). -/
noncomputable def KcW (F : GateFree l) : ℕ := SymFront.KF l F + SymFront.CF l F + 64 * cXP l F.cr + 20

/-- The register capacity's degree (on the filter degree). -/
noncomputable def DkW (fe : ℕ) : ℕ := SymFront.DF l fe + SymFront.DFs l fe + E0P l

/-- The steps' and the residues' coefficient (on the gate). -/
noncomputable def CsW (F : GateFree l) : ℕ :=
  SymFront.CF l F + 1566 * KcW l F + 3200 * cXP l F.cr + 4 * BCP l F.cr + 20000

/-- The steps' and the residues' degree (on the filter degree). -/
noncomputable def DsW (fe : ℕ) : ℕ := DkW l fe + BDP l + 2

end Consts

/-! ## The run -/

section Gate
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The four writers' budgets at a SYM request**, below `BCP c_r·(|fpIn|+1)^{BDP}`. -/
theorem bud_symP {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (c : Fin 4) :
    budP F.cr (E0P l) (K0P F.cr) ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
        (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
        (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ c) ≤
      BCP l F.cr * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^
        BDP l := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  obtain ⟨a1, a2, a3, a4, a5⟩ :=
    atoms_symP l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ rfl c
  have hnF : n ≤ (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length :=
    FpInLen.n_le_fpIn (⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ : FReq l F kclk coef A a ha)
  have hkh := Sd.kh_le_sym l F kclk coef A a ha n a' Cs carriers translation hs
  have hQF := Sd.q_le_fpIn_sym l F kclk coef A a ha n a' ha' Cs carriers translation hcall hs
  set r : FReq l F kclk coef A a ha := ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ with hrd
  set P := (callInputs l F kclk coef A a ha).starParams n hs with hPd
  set Pl := symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers with hPl
  set L := symL l F kclk coef A a ha r c with hLd
  set Fn := (fpIn l F kclk coef A a ha r).length with hFn
  have hK0 : 1 ≤ K0P F.cr := by unfold K0P; omega
  have hE0 : 1 ≤ E0P l := by unfold E0P; omega
  have hQ : n + 2 ≤ 2 ^ NumsX.mOf P + 1 := n2_le_mP P
  have lift : ∀ v, v ≤ K0P F.cr * (n + 2) ^ E0P l → v ≤ K0P F.cr * (2 ^ NumsX.mOf P + 1) ^ E0P l := fun v h =>
    h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _))
  obtain ⟨-, -, h3, -⟩ := tabP_hyps (NumsX.mOf P) Pl n L (K0P F.cr) (E0P l) hQ hK0 hE0
    (lift _ a1) (lift _ a2) (lift _ a3) (lift _ a4) (lift _ a5)
  have hN2 : n + 2 ≤ K0P F.cr * (n + 2) ^ E0P l := by
    have h1 : n + 2 ≤ (n + 2) ^ E0P l := Nat.le_self_pow (by omega) _
    have h2 : (n + 2) ^ E0P l ≤ K0P F.cr * (n + 2) ^ E0P l := Nat.le_mul_of_pos_left _ hK0
    omega
  have hw : (reqP n Pl L).length ≤ 16 * (K0P F.cr * (n + 2) ^ E0P l) :=
    TabW.reqT_le n Pl.M Pl.B Pl.errExp L 0 (Fintype.card Pl.FlatSeed) _ hN2 a1 a2 a3 a4 (by omega) a5
  have hX : K0P F.cr * (n + 2) ^ E0P l ≤ cXP l F.cr * (Fn + 1) ^ E0P l := by
    have h1 : (n + 2) ^ E0P l ≤ (2 * (Fn + 1)) ^ E0P l := Nat.pow_le_pow_left (by omega) _
    rw [mul_pow] at h1
    unfold cXP
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ h1
  have hcc : ThrData.thrDataStage2.cost 0 (TabW.noCs n) ([] : List (Stars.Carrier n)) (UnaryCalc.value 1 64 n)
      (UnaryCalc.value 1 64 n) ≤ ThrData.thrDataStage2.Cc * (129 * (Fn + 1)) ^ ThrData.thrDataStage2.Dc := by
    have hp := ThrData.thrDataStage2.cost_le (TabW.noCs n) ([] : List (Stars.Carrier n)) (UnaryCalc.value 1 64 n)
      (UnaryCalc.value 1 64 n) 0 (by omega) (by simp) (fun i => i.elim0) (by simp) (fun i => i.elim0) (by simp)
      (by show 2 ≤ n + 64 * (n + 1) ^ 1; rw [pow_one]; omega)
    unfold ValidatorPolynomialDomination.PolyBounded at hp
    refine hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
    show 0 + n + 64 * (n + 1) ^ 1 + 64 * (n + 1) ^ 1 + 1 ≤ 129 * (Fn + 1)
    rw [pow_one]; omega
  unfold budP BCP BDP
  exact Sd.bud_poly (reqP n Pl L) n (9 * E0P l) (CWP (K0P F.cr)) _ F.cr (NumsX.mOf P) (E0P l) (K0P F.cr) _
    (K0P F.cr * (n + 2) ^ E0P l) Fn _ (cXP l F.cr) (E0P l) ThrData.thrDataStage2.Cc ThrData.thrDataStage2.Dc
    h3 hw hX hnF hcc (Sd.two_m_le P _ hkh) hQF

/-- **The flat part's run at a SYM request**, in `SWfT`'s form. -/
theorem swf_runG (W : WalkBankProducer) (r : FReq l F kclk coef A a ha) (hg : r.1.mode = .sym)
    (σ : WState (LNS (xW l W)) LNR) (hin : σ.st (NumsPh2.sIn (xW l W)) = frame (fpIn l F kclk coef A a ha r))
    (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ NumsPh2.sIn (xW l W) → σ.st i = []) (hv : ∀ q, σ.val q = 0)
    (hc : σ.cell = false) :
    ∃ (τ : WState (LNS (xW l W)) LNR) (m : ℕ),
      m ≤ CsW l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsW l F.filterErrDeg ∧
      Step (swfM l W F) m
        (wenc (KcW l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkW l F.filterErrDeg) σ).H
        (wenc (KcW l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkW l F.filterErrDeg) σ).A
        (wenc (KcW l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkW l F.filterErrDeg) τ).H
        (wenc (KcW l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DkW l F.filterErrDeg) τ).A ∧
      (∀ k : Fin 4, τ.st (tmC xFw (twW l W) k (woutW l W)) =
        SWParts.swWs l 8 4 (by norm_num) F kclk coef A a ha r k) ∧
      τ.st (NumsPh2.sIn (xW l W)) = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ NumsPh2.sIn (xW l W) → (∀ k, i ≠ tmC xFw (twW l W) k (woutW l W)) →
        (τ.st i).length ≤ CsW l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsW l F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  cases mode with
  | thr => exact absurd hg (by simp)
  | sym =>
    have hnF : n ≤ (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length :=
      FpInLen.n_le_fpIn (⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ : FReq l F kclk coef A a ha)
    set X := (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1 with hXd
    have hn : n + 1 ≤ X := by omega
    have hE0 : 1 ≤ E0P l := by unfold E0P; omega
    have hlw : lwW l F.cr n ≤ 16 * (cXP l F.cr * X ^ E0P l) := by
      have h1 : (n + 2) ^ E0P l ≤ (2 * X) ^ E0P l := Nat.pow_le_pow_left (by omega) _
      rw [mul_pow] at h1
      have h2 : K0P F.cr * (n + 2) ^ E0P l ≤ cXP l F.cr * X ^ E0P l := by
        unfold cXP
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ h1
      unfold lwW
      omega
    obtain ⟨hcF, hcR, hcN⟩ := cap_arith (SymFront.KF l F) (SymFront.CF l F) (cXP l F.cr) X
      (SymFront.DF l F.filterErrDeg) (SymFront.DFs l F.filterErrDeg) (E0P l) n (lwW l F.cr n) hn hE0 hlw
    obtain ⟨τ, m, hm, hst, hout, hin', hsh', hv', hc', hres⟩ := swf_run l W F kclk coef A a ha ha' Cs carriers
      translation hcall (KcW l F * X ^ DkW l F.filterErrDeg) hcF hcR hcN σ ⟨hin, hsh, hbl, hv, hc⟩
    obtain ⟨hM, hR⟩ := swf_cost (SymFront.CF l F) (KcW l F) (cXP l F.cr) (BCP l F.cr) X
      (SymFront.DFs l F.filterErrDeg) (DkW l F.filterErrDeg) (BDP l) (E0P l) n (lwW l F.cr n)
      (fun c => budP F.cr (E0P l) (K0P F.cr) ((callInputs l F kclk coef A a ha).starParams n hcall.2.2.2.2.2.1)
        (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
        (symL l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ c))
      hn (by unfold DkW; omega) (by unfold DkW; omega) hlw
      (fun c => bud_symP l F kclk coef A a ha ha' Cs carriers translation hcall c)
    refine ⟨τ, m, hm.trans hM, hst, fun k => (hout k).trans (swf_words l F kclk coef A a ha
      ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ rfl k).symm, hin',
      fun i h1 h2 => (hres i h1 h2).trans hR, hsh', hv'⟩

end Gate

/-! ## The writer -/

section Inst
variable (W : WalkBankProducer) (l : Literals)

theorem outW_ne (c : Fin 4) : tmC xFw (twW l W) c (woutW l W) ≠ NumsPh2.sIn (xW l W) := fun e => by
  have := congrArg Fin.val e
  rw [tmC_val] at this
  exact absurd this (by show ¬ (161 + (xFw + (c.val * twW l W + (woutW l W).val)) = 150); omega)

theorem outW_inj : Function.Injective (fun c : Fin 4 => tmC xFw (twW l W) c (woutW l W)) := fun c c' h =>
  (tmC_inj' xFw (twW l W) c c' _ _ h).1

/-- **The flat tables' writer** (`SWfT l`): the flat part `swfM` at the SYM requests, its outputs the four
circuits' flat tables words (the SYM slots `24 … 27`). -/
noncomputable def swf : SWParts.SWfT l where
  ns := LNS (xW l W)
  nr := LNR
  s := fun F => _
  M := fun F => swfM l W F
  sIn := NumsPh2.sIn (xW l W)
  sOut := ⟨fun c => tmC xFw (twW l W) c (woutW l W), outW_inj W l⟩
  out_ne := outW_ne W l
  Kc := KcW l
  Dk := DkW l
  Cs := CsW l
  Ds := DsW l
  run := fun F kclk coef A a ha r hg σ hin hsh hbl hv hc =>
    swf_runG l F kclk coef A a ha W r hg σ hin hsh hbl hv hc

end Inst

end NearCubicWires.WireExponent3_5.FinalPass.SymF
