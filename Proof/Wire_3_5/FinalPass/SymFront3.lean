import Proof.Wire_3_5.FinalPass.SymFront2
import Proof.Wire_3_5.UnionMachine.NumsA13
import Proof.Wire_3_5.UnionMachine.NumsA12
import Proof.Wire_3_5.UnionMachine.NumsC7

/-! # The SYM front, part 3: the front at a SYM request (build once)

**`frontM`**: the phase (c) (`NumsC.phC3`: `n` and the roles), the width and the data stage's inputs (`prepW`), PA's
data stage docked (`dataDockM`, part 1 with the tapes exported), the counts unframed onto `113`, the SYM numbers
program lifted (`numsBankG`: the whole register export), stream `113` rewound (part 2). The composition and its
arithmetic are `NumsA12.aRun` with `numsBankG` and the rewind in place of `numsBank` and the finish.

**`front_run`**: from `CoreWordsMJ`'s entry at a SYM request, within `CF·(|fpIn|+1)^{DFs}` steps at every capacity above
`KF·(|fpIn|+1)^{DF}` (degrees on `fe`, coefficients on `F`), the exit **`FrontOut`**: the input kept, every head `0`,
the flat list's `M, B, errExp, |FlatSeed|` in `G 32, 33, 34, 41` (`symListParams` exactly), `n` in `dN`, the population
lengths `|symGates C_j|` (`0` past the tuple) in `330 + j`, every register within the bound, every filled slot's scan
word and gate table on the data tapes, the empty slots' scan tapes blank, the streams past the data region blank,
every residue within the bound.

Paper quantity of the main type: the SYM call's flat list `symListParams` (P3:1491-1498, 3049-3050) and its slices,
at the request, in the bank. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFront
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g g_ne npow_le)
open NearCubicWires.SupplierPipeline

section Gate
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals)

/-- After the data stage: the counts unframed, the numbers, the rewind. -/
noncomputable def postF (F : GateFree l) : WM (LNS x) LNR :=
  .seq (unframeW (tOUT x hx) (sk x 113) (g 0) (g 1))
    (.seq ((numsP l F).liftW (fsN x) id) (rewW x (K1a l F) (D3a l F.filterErrDeg)))

/-- **The SYM front's machine** at a gate. -/
noncomputable def frontM (F : GateFree l) :=
  Composition.machine ((NumsC.phC3 x l).M F)
    (Composition.machine (Composition.machine (prepW x hx).toProg.compile (DataDock.dataDockM (nr := LNR) (tmapA x hx)))
      (postF x hx l F).toProg.compile)

/-- The front's capacity coefficient and degree. -/
noncomputable def KF (F : GateFree l) : ℕ := NumsC.KnC l F + Kua l F
noncomputable def DF (fe : ℕ) : ℕ := NumsC.DnC l fe + Dua l fe
/-- The front's step and residue coefficient and degree. -/
noncomputable def CF (F : GateFree l) : ℕ := NumsC.CsC l F + CsA l F + 1
noncomputable def DFs (fe : ℕ) : ℕ := NumsC.DsC l fe + DsA l fe + Dua l fe

/-- **The front's exit.** -/
structure FrontOut {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (Pl : FlatListParams)
    (w : List Bool) (B : ℕ) (τ : St x) : Prop where
  hin : τ.st (sIn x) = frame w
  heads : ∀ i, τ.sh i = 0
  cell : τ.cell = false
  vM : τ.val (SymDec.G 32) = Pl.M
  vB : τ.val (SymDec.G 33) = Pl.B
  vE : τ.val (SymDec.G 34) = Pl.errExp
  vK : τ.val (SymDec.G 41) = Fintype.card Pl.FlatSeed
  vN : τ.val SymDec.dN = n
  vL : ∀ (j : Fin 4) (h : j.val < a'), τ.val ⟨330 + j.val, by have := j.isLt; show 330 + j.val < 512; omega⟩ =
    (Stars.symGates (Cs ⟨j.val, h⟩)).length
  vL0 : ∀ j : Fin 4, a' ≤ j.val → τ.val ⟨330 + j.val, by have := j.isLt; show 330 + j.val < 512; omega⟩ = 0
  vle : ∀ q, τ.val q ≤ B
  scan : ∀ (i : Fin 4) (h : i.val < a'), τ.st (tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0)))) =
    Out.DataW.scanWord (Cs ⟨i.val, h⟩)
  gates : ∀ (i : Fin 4) (h : i.val < a'), τ.st (tmapA x hx (DataDock.iSym i)) =
    FinalPass.Corner.gatesW (PrimT.tabH (Stars.symGates (Cs ⟨i.val, h⟩))) (Stars.symGates (Cs ⟨i.val, h⟩))
  scan0 : ∀ i : Fin 4, a' ≤ i.val → τ.st (tmapA x hx (DataDock.iOf (Data.sSym i (PrimT.SymTab.scanSl 0)))) = []
  hi : ∀ k : Fin x, DataDock.DT + 3 ≤ k.val → τ.st (sT x k) = []
  resid : ∀ i, i ≠ sIn x → (τ.st i).length ≤ B

theorem cy_getD_zero {n a' : ℕ} (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (j : ℕ) (h : a' ≤ j) :
    (SymDec.cyOf Cs).getD j 0 = 0 := by
  rw [List.getD_eq_default]
  rw [SymDec.cyOf_length]
  exact h

/-- **The SYM front's run** at a SYM request. -/
theorem front_run (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (cap : ℕ)
    (hcap : KF l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^
      DF l F.filterErrDeg ≤ cap) (σ : St x)
    (hE : Entry x l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ σ) :
    ∃ (τ : St x) (m : ℕ),
      m ≤ CF l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^
        DFs l F.filterErrDeg ∧
      Step (frontM x hx l F) m (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      FrontOut x hx Cs (symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers)
        (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
        (CF l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^
          DFs l F.filterErrDeg) τ := by
  set r : FReq l F kclk coef A a ha := ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ with hrd
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  -- the numbers
  have hnw : n ≤ (fpIn l F kclk coef A a ha r).length := FinalPass.FpInLen.n_le_fpIn r
  obtain ⟨w, hwd⟩ : ∃ v, v = fpIn l F kclk coef A a ha r := ⟨_, rfl⟩
  rw [← hwd] at hcap hnw ⊢
  obtain ⟨X, hXd⟩ : ∃ v, v = w.length + 1 := ⟨_, rfl⟩
  rw [← hXd] at hcap ⊢
  have hX1 : 1 ≤ X := by omega
  have pwX : ∀ {a b : ℕ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Nat.pow_le_pow_right hX1 h
  -- the phase-(c) and phase-(a) capacities
  have hcapC : NumsC.KnC l F * X ^ NumsC.DnC l F.filterErrDeg ≤ cap := by
    refine le_trans ?_ hcap
    unfold KF DF
    exact Nat.mul_le_mul (Nat.le_add_right _ _) (pwX (Nat.le_add_right _ _))
  have hcapA : Kua l F * X ^ Dua l F.filterErrDeg ≤ cap := by
    refine le_trans ?_ hcap
    unfold KF DF
    exact Nat.mul_le_mul (Nat.le_add_left _ _) (pwX (Nat.le_add_left _ _))
  -- 0: phase (c)
  obtain ⟨σ0, m0, hm0, s0, hC⟩ := (NumsC.phC3 x l).run F kclk coef A a ha r cap
    (by rw [← hwd, ← hXd]; exact hcapC) σ hE
  have hCin : σ0.st (sIn x) = frame w := by rw [hC.hin, hwd]
  have hmo : mOf l F kclk coef A a ha r = 0 := by simp [mOf, hrd]
  have heN : eOf l F kclk coef A a ha r ≤ n := by unfold eOf; simp [hrd]
  obtain ⟨Du, hDud⟩ : ∃ v, v = Dua l F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ v, v = X ^ Du := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by rw [hUd]; exact Nat.one_le_pow _ _ (by omega)
  have lift : ∀ {d : ℕ}, d ≤ Du → X ^ d ≤ U := fun hd => by rw [hUd]; exact Nat.pow_le_pow_right hX1 hd
  have hDu : Du = 3 * D0 l F.filterErrDeg + FinalPass.Sd.R.ZTe l F.filterErrDeg + 27 := by rw [hDud]; rfl
  have hZT : FinalPass.Sd.R.ZT l F = FinalPass.Sd.R.ZTe l F.filterErrDeg := rfl
  have hXU : X ≤ U := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ U := lift (by omega)
  -- the width
  obtain ⟨W, hWd⟩ : ∃ v, v = wOf w.length n := ⟨_, rfl⟩
  have hW27 : W ≤ 27 * X ^ 26 := by
    rw [hWd]; unfold wOf
    have h1 : w.length ≤ X ^ 26 := by
      calc w.length ≤ X ^ 1 := by rw [pow_one]; omega
        _ ≤ X ^ 26 := Nat.pow_le_pow_right hX1 (by omega)
    have h2 : (n + 1) ^ 26 ≤ X ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have h3 : 1 ≤ X ^ 26 := Nat.one_le_pow _ _ (by omega)
    omega
  have hWU : W ≤ 27 * U := le_trans hW27 (Nat.mul_le_mul_left _ (lift (by omega)))
  -- `T_f`
  obtain ⟨KTZ, hKTZ⟩ : ∃ v, v = FinalPass.Sd.R.KT l F * 2 ^ FinalPass.Sd.R.ZT l F := ⟨_, rfl⟩
  have hTU : FinalPass.Sd.R.Tf l F kclk coef A a ha r ≤ KTZ * U := by
    show FinalPass.Sd.R.KT l F * (n + 2) ^ FinalPass.Sd.R.ZT l F ≤ KTZ * U
    have h1 := npow_le n X (FinalPass.Sd.R.ZT l F) (by omega)
    have h2 : X ^ FinalPass.Sd.R.ZT l F ≤ U := lift (by rw [hZT]; omega)
    rw [hKTZ, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_trans h1 (Nat.mul_le_mul_left _ h2))
  -- the numbers' capacity and the rewind bound
  obtain ⟨cap₀, hc0d⟩ : ∃ v, v = K0 l F * X ^ D0 l F.filterErrDeg := ⟨_, rfl⟩
  have hc0U : cap₀ ≤ K0 l F * U := by rw [hc0d]; exact Nat.mul_le_mul_left _ (lift (by omega))
  obtain ⟨Bh, hBhd⟩ : ∃ v, v = K1a l F * X ^ D3a l F.filterErrDeg := ⟨_, rfl⟩
  have hBhU : Bh ≤ K1a l F * U := by rw [hBhd]; exact Nat.mul_le_mul_left _ (lift (by unfold D3a; omega))
  have hcube : 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) ≤ Bh := by
    have h1 : cap₀ + 2 ≤ (K0 l F + 2) * X ^ D0 l F.filterErrDeg := by
      have := Nat.one_le_pow (D0 l F.filterErrDeg) X (by omega)
      rw [hc0d]; nlinarith
    have h2 : (cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2) ≤ (K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg := by
      calc (cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2) = (cap₀ + 2) ^ 3 := by ring
        _ ≤ ((K0 l F + 2) * X ^ D0 l F.filterErrDeg) ^ 3 := Nat.pow_le_pow_left h1 3
        _ = (K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg := by unfold D3a; rw [mul_pow, ← pow_mul]; ring_nf
    rw [hBhd]; unfold K1a
    calc 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) ≤ 3000000 * ((K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg) :=
          Nat.mul_le_mul_left _ h2
      _ = 3000000 * (K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg := by ring
  have hKu : Kua l F * U = (2 * K0 l F + K1a l F + KTZ + 3 * D0 l F.filterErrDeg + 1000) * U := by
    unfold Kua; rw [hKTZ]
  have hcapU : (2 * K0 l F + K1a l F + KTZ + 3 * D0 l F.filterErrDeg + 1000) * U ≤ cap := by
    rw [← hKu, hUd, hDud]; exact hcapA
  have hc0cap : cap₀ ≤ cap := by
    refine le_trans hc0U (le_trans (Nat.mul_le_mul_right U (by omega :
      K0 l F ≤ 2 * K0 l F + K1a l F + KTZ + 3 * D0 l F.filterErrDeg + 1000)) hcapU)
  obtain ⟨hcW, hcT, hcD, -, hcF⟩ := capA U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) cap₀ 0 Bh
    (FinalPass.Sd.R.Tf l F kclk coef A a ha r) W n (eOf l F kclk coef A a ha r) w.length cap hc0U (Nat.zero_le _)
    hBhU hTU hWU (by omega) (by omega) (by omega) hU1 hcapU
  -- 1: the width
  obtain ⟨cw, ew, hcw⟩ := width_run x cap w n σ0 hCin (hC.heads _) (by rw [hC.hn])
    (fun j => hC.regs _ (g_ne j).1 (g_ne j).2.1 (g_ne j).2.2.1 (g_ne j).2.2.2) (by rw [← hWd]; omega)
  rw [← hWd] at ew
  -- 2: the data stage's inputs, the stash
  obtain ⟨τ1, ct, et, hPD, hct⟩ := tapes_run x hx cap w n W
    (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (σ0.setv (g 2) W)
    (by rw [WState.setv_st]; exact hCin) (fun i hi => by rw [WState.setv_st]; exact hC.clean i hi)
    (fun i => by rw [WState.setv_sh]; exact hC.heads i) (by rw [WState.setv_cell]; exact hC.cell)
    (by rw [WState.setv_val, Function.update_of_ne (show rN ≠ g 2 by decide)]; exact hC.hn)
    (by rw [WState.setv_val, Function.update_self])
    (by rw [WState.setv_val, Function.update_of_ne (show rE ≠ g 2 by decide)]; exact hC.he)
    (by rw [WState.setv_val, Function.update_of_ne (show rT ≠ g 2 by decide)]; exact hC.ht)
    (fun q a1 a2 a3 a4 => by
      rw [WState.setv_val, Function.update_of_ne a4]
      by_cases hq : q = rM
      · subst hq; rw [hC.hm, hmo]
      · exact hC.regs q a1 hq a2 a3)
    hcT
  -- 3: the data stage, the counts onto stream `113`, the tapes exported
  obtain ⟨tout, ρ, cu, sD, eu, hNI, hSN, hSE, hST, hW0, hW1, hres, hscan, hgates, hscan0, hoth, hcu⟩ :=
    dataPostW l F kclk coef A a ha x hx n a' ha' Cs carriers translation hcall w hwd W hWd cap
      (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r) τ1 hPD (by omega)
  -- 4: the SYM numbers, the whole register export
  obtain ⟨ω', cn, h, en, hst, hsh', hhc, hcell, hG, hdN, hd0, hd1, hd2, hd3, -, hval, hcn⟩ :=
    numsBankG l F kclk coef A a ha x ha' Cs carriers translation hcall hs cap₀ cap (by rw [hc0d, hXd, hwd])
      hc0cap ρ (by rw [← hwd]; exact hNI)
  -- 5: the rewind
  obtain ⟨cr, er, hcr⟩ := rew_run x cap (K1a l F) (D3a l F.filterErrDeg) h cap₀ w ω'
    (by rw [hst]; exact hNI.hin) (fun i hi => by rw [hsh', Function.update_of_ne hi]; exact hNI.heads i)
    (by rw [hsh', Function.update_self]) (by rw [← hXd, ← hBhd]; omega) hval (by rw [← hXd, ← hBhd]; omega)
  set τ : St x := ⟨fun _ => 0, ω'.st, fun q => if q ∈ scrR then 0 else ω'.val q, ω'.cell⟩ with hτ
  -- the registers
  have tv : ∀ q : Fin LNR, ¬ (480 ≤ q.val ∧ q.val ≤ 486) → τ.val q = ω'.val q := fun q hq => by
    show (if q ∈ scrR then 0 else ω'.val q) = _
    rw [if_neg (fun hm => hq ((mem_scrR q).1 hm))]
  have gv : ∀ i : Fin 64, τ.val (SymDec.G i) = ω'.val (SymDec.G i) := fun i => tv _ (by
    rw [SymDec.G_val]; have := i.isLt; omega)
  -- the steps
  have hKu1 : 1 ≤ Kua l F := by unfold Kua; omega
  have hK1K : K1a l F ≤ Kua l F := by unfold Kua; omega
  have hKK3 : Kua l F ≤ Kua l F ^ 3 := Nat.le_self_pow (by norm_num) _
  have hUU3 : U ≤ U ^ 3 := Nat.le_self_pow (by norm_num) _
  have hDsA : DsA l F.filterErrDeg = 3 * Du + 26 * Data.symDc := by unfold DsA; rw [hDud]
  have hUX : U ≤ X ^ DsA l F.filterErrDeg := by rw [hUd]; exact Nat.pow_le_pow_right hX1 (by rw [hDsA]; omega)
  have hU3X : U ^ 3 ≤ X ^ DsA l F.filterErrDeg := by
    rw [hUd, ← pow_mul]; exact Nat.pow_le_pow_right hX1 (by rw [hDsA]; omega)
  have hZX : X ^ (26 * Data.symDc) ≤ X ^ DsA l F.filterErrDeg := Nat.pow_le_pow_right hX1 (by rw [hDsA]; omega)
  have hKuU : Kua l F * U ≤ Kua l F ^ 3 * U ^ 3 := Nat.mul_le_mul hKK3 hUU3
  have hK1U : K1a l F * U ≤ Kua l F ^ 3 * U ^ 3 := Nat.mul_le_mul (le_trans hK1K hKK3) hUU3
  have hKuP : Kua l F ^ 3 * U ^ 3 ≤ Kua l F ^ 3 * X ^ DsA l F.filterErrDeg := Nat.mul_le_mul_left _ hU3X
  have hcw2 : cw ≤ 4000 * 2 ^ 27 * U := by
    have h1 : w.length + n + 2 ≤ 2 * X := by omega
    have h2 : (w.length + n + 2) ^ 27 ≤ (2 * X) ^ 27 := Nat.pow_le_pow_left h1 27
    have h3 : (2 * X) ^ 27 = 2 ^ 27 * X ^ 27 := mul_pow 2 X 27
    have h4 : X ^ 27 ≤ U := lift (by omega)
    calc cw ≤ 4000 * (w.length + n + 2) ^ 27 := hcw
      _ ≤ 4000 * (2 ^ 27 * X ^ 27) := by rw [← h3]; exact Nat.mul_le_mul_left _ h2
      _ ≤ 4000 * (2 ^ 27 * U) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
      _ = 4000 * 2 ^ 27 * U := by ring
  have hs := sumle U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) n W (eOf l F kclk coef A a ha r)
    (FinalPass.Sd.R.Tf l F kclk coef A a ha r) hU1 (by omega) hWU (by omega) hTU
  rw [← hKu] at hs
  have hct2 : ct ≤ 100 * (Kua l F * U) := by omega
  have hfd : Data.symCc * (3 * W + 1) ^ Data.symDc ≤ Data.symCc * 82 ^ Data.symDc * X ^ (26 * Data.symDc) := by
    have h0 := Nat.one_le_pow 26 X (by omega)
    have h1 : 3 * W + 1 ≤ 82 * X ^ 26 := by omega
    have h2 : (3 * W + 1) ^ Data.symDc ≤ (82 * X ^ 26) ^ Data.symDc := Nat.pow_le_pow_left h1 _
    have h3 : (82 * X ^ 26) ^ Data.symDc = 82 ^ Data.symDc * X ^ (26 * Data.symDc) := by rw [mul_pow, ← pow_mul]
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_of_le_of_eq h2 h3)
  have hcu2 : cu ≤ 1100 * U := by omega
  have hcn2 : cn ≤ K1a l F * U := le_trans hcn (le_trans hcube hBhU)
  have hcr2 : cr ≤ 5000 * (27 * (Kua l F ^ 3 * U ^ 3)) := by
    have hMf := mfle U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) (D3a l F.filterErrDeg) cap₀ 0 Bh 0 0 0
      w.length hU1 hc0U (Nat.zero_le _) hBhU (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (by omega)
      (by unfold D3a; omega)
    rw [← hKu] at hMf
    have hcr' := hcr
    rw [← hXd, ← hBhd] at hcr'
    unfold rewCost at hcr'
    have h3 := Nat.pow_le_pow_left (show cap₀ + Bh + w.length + K1a l F + D3a l F.filterErrDeg + 2 ≤
      3 * (Kua l F * U) by omega) 3
    have h4 : (3 * (Kua l F * U)) ^ 3 = 27 * (Kua l F ^ 3 * U ^ 3) := by ring
    rw [h4] at h3
    omega
  have hres2 : Data.symCc * (3 * W + 1) ^ Data.symDc + 3 * W + n + eOf l F kclk coef A a ha r +
      FinalPass.Sd.R.Tf l F kclk coef A a ha r + 2 ≤ CsA l F * X ^ DsA l F.filterErrDeg := by
    have e1 : CsA l F * X ^ DsA l F.filterErrDeg = 10 ^ 12 * X ^ DsA l F.filterErrDeg +
        200000 * (Kua l F ^ 3 * X ^ DsA l F.filterErrDeg) +
        Data.symCc * 82 ^ Data.symDc * X ^ DsA l F.filterErrDeg := by unfold CsA; ring
    have hA : Kua l F * U ≤ Kua l F ^ 3 * X ^ DsA l F.filterErrDeg := le_trans hKuU hKuP
    have hB : Data.symCc * (3 * W + 1) ^ Data.symDc ≤ Data.symCc * 82 ^ Data.symDc * X ^ DsA l F.filterErrDeg :=
      le_trans hfd (Nat.mul_le_mul_left _ hZX)
    rw [e1]
    linarith
  have hfin := costA U (X ^ DsA l F.filterErrDeg) (X ^ (26 * Data.symDc)) (Kua l F) (Data.symCc * 82 ^ Data.symDc)
    cw ct (Data.symCc * (3 * W + 1) ^ Data.symDc) cu cn cr (Kua l F * U) (K1a l F * U) (Kua l F ^ 3 * U ^ 3) hU1 hUX
    hcw2 hct2 hfd hcu2 hcn2 hcr2 hKuU hK1U (Nat.mul_le_mul_left _ hZX) hKuP
  -- the bounds at the front's degree
  have hDFs1 : X ^ NumsC.DsC l F.filterErrDeg ≤ X ^ DFs l F.filterErrDeg := pwX (by unfold DFs; omega)
  have hDFs2 : X ^ DsA l F.filterErrDeg ≤ X ^ DFs l F.filterErrDeg := pwX (by unfold DFs; omega)
  have hDFs3 : U ≤ X ^ DFs l F.filterErrDeg := by rw [hUd, hDud]; exact pwX (by unfold DFs; omega)
  have hCsA : CsA l F * X ^ DsA l F.filterErrDeg ≤ CsA l F * X ^ DFs l F.filterErrDeg := Nat.mul_le_mul_left _ hDFs2
  have hCF : CF l F * X ^ DFs l F.filterErrDeg = NumsC.CsC l F * X ^ DFs l F.filterErrDeg +
      CsA l F * X ^ DFs l F.filterErrDeg + X ^ DFs l F.filterErrDeg := by unfold CF; ring
  have hX1' : 1 ≤ X ^ DFs l F.filterErrDeg := Nat.one_le_pow _ _ hX1
  have hc0B : cap₀ ≤ CF l F * X ^ DFs l F.filterErrDeg := by
    have : cap₀ ≤ Kua l F * U := le_trans hc0U (Nat.mul_le_mul_right _ (by unfold Kua; omega))
    have h2 : Kua l F * U ≤ CsA l F * X ^ DFs l F.filterErrDeg := by
      calc Kua l F * U ≤ Kua l F ^ 3 * U ^ 3 := hKuU
        _ ≤ Kua l F ^ 3 * X ^ DsA l F.filterErrDeg := hKuP
        _ ≤ CsA l F * X ^ DsA l F.filterErrDeg := Nat.mul_le_mul_right _ (by unfold CsA; omega)
        _ ≤ _ := hCsA
    omega
  -- the machine's run
  have sP := Exec.step (WExec.exec cap (WExec.seq ew et))
  have sQ := Exec.step (WExec.exec cap (WExec.seq eu (WExec.seq en er)))
  refine ⟨τ, _, ?_, Step.seq s0 (Step.seq (Step.seq sP sD) sQ), ?_⟩
  · have h1 : m0 ≤ NumsC.CsC l F * X ^ DFs l F.filterErrDeg := by
      have := hm0
      rw [← hwd, ← hXd] at this
      exact le_trans this (Nat.mul_le_mul_left _ hDFs1)
    have h2 : cw + 1 + ct + 1 + Data.symCc * (3 * W + 1) ^ Data.symDc + 1 + (cu + 1 + (cn + 1 + cr)) ≤
        CsA l F * X ^ DFs l F.filterErrDeg := le_trans (by unfold CsA; exact hfin) hCsA
    rw [hCF]
    omega
  · -- the exit
    have sv : ∀ i, τ.st i = ρ.st i := fun i => by show ω'.st i = ρ.st i; rw [hst]
    exact
      { hin := by rw [sv]; exact hNI.hin
        heads := fun _ => rfl
        cell := hcell
        vM := by rw [gv, hG]; exact ident_M l F kclk coef A a ha Cs carriers
        vB := by rw [gv, hG]; exact ident_B l F kclk coef A a ha Cs carriers
        vE := by rw [gv, hG]; exact ident_err l F kclk coef A a ha Cs carriers
        vK := by rw [gv, hG]; exact ident_flat l F kclk coef A a ha Cs carriers
        vN := by rw [tv _ (by show ¬ (480 ≤ 320 ∧ 320 ≤ 486); omega)]; exact hdN
        vL := fun j hj => by
          rw [tv _ (by have := j.isLt; show ¬ (480 ≤ 330 + j.val ∧ 330 + j.val ≤ 486); omega),
            ← cy_getD_len Cs j.val hj]
          fin_cases j
          · exact hd0
          · exact hd1
          · exact hd2
          · exact hd3
        vL0 := fun j hj => by
          rw [tv _ (by have := j.isLt; show ¬ (480 ≤ 330 + j.val ∧ 330 + j.val ≤ 486); omega),
            ← cy_getD_zero Cs j.val hj]
          fin_cases j
          · exact hd0
          · exact hd1
          · exact hd2
          · exact hd3
        vle := fun q => by
          show (if q ∈ scrR then 0 else ω'.val q) ≤ _
          split
          · omega
          · exact le_trans (hval q) hc0B
        scan := fun i hi => by rw [sv]; exact hscan i hi
        gates := fun i hi => by rw [sv]; exact hgates i hi
        scan0 := fun i hi => by rw [sv]; exact hscan0 i hi
        hi := fun k hk => by
          rw [sv, hoth _ (tmapA_ne x hx _ (by rw [sT_val]; omega) (Or.inr (by rw [sT_val]; omega)))
            (fne (by rw [sT_val]; show 161 + k.val ≠ 113; omega))]
          exact hPD.blank _ (by rw [sT_val]; omega) (by rw [sT_val]; have := DT_val; omega)
            (by rw [sT_val]; have := DT_val; omega) (by rw [sT_val]; have := DT_val; omega)
            (by rw [sT_val]; have := DT_val; omega) (by rw [sT_val]; have := DT_val; omega)
            (by rw [sT_val]; have := DT_val; omega) (by rw [sT_val]; omega)
        resid := fun i hi => by
          rw [sv]
          have := hres i hi
          omega }

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFront
