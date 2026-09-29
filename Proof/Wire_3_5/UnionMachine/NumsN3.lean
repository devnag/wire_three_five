import Proof.Wire_3_5.UnionMachine.NumsN2
import Proof.Wire_3_5.FinalPass.SymFront6

/-! # SWn, part 3: the eighteen numbers' registers, the three per-circuit phases

After the SYM front (`FrontOutB`), SWn's post program computes, per circuit `j < 4`, the gate table's width
`tabH G_j` (phase H: `tabHW` on the slot tape), the flat table's length `tabLen` (phase T: `tabLenW`, moved out of the
scratch), and the stage-5 template's length (phase Q: the template length program, an ARGUMENT `tp` with the interface
**`TplIface`**, the statement for `tplLen_spec`). Each phase writes its four registers and keeps every
other register (the invariants `InvH`, `InvT`, `InvQ`, one generic step each, chained four times).

* registers `rH j = 100+j`, `rP = 104`, `rT j = 108+j`, `rQ j = 112+j`, `rOP = 127`, `wB = 130 … 159`, the front's
  `rL j = 330+j`; the template scratch streams `oT j = sT (DT+3+j)`;
* `tplNum`, **`TplIface`**; `tabHs`/`InvH`/`invH_step`/**`tabHs_run`**; `tabLenP`/`tvOf`/`InvT`/`invT_step`/
  **`tabLens_run`**; `tpls`/`InvQ`/`invQ_step`/**`tpls_run`**.

Paper quantities of the main types: the SYM call numbers `tabH G_j`, `tabLen`, the template's length (P3:3170-3178,
list:flatten P3:1508-1520, list:base P3:1449-1477). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

/-! ## Registers and streams -/

/-- Circuit `j`'s gate table width. -/
def rH (j : Fin 4) : Fin LNR := ⟨100 + j.val, by have := j.isLt; show 100 + j.val < 512; omega⟩
/-- `tabHW`'s scratch. -/
def rP : Fin LNR := ⟨104, by decide⟩
/-- Circuit `j`'s flat table length. -/
def rT (j : Fin 4) : Fin LNR := ⟨108 + j.val, by have := j.isLt; show 108 + j.val < 512; omega⟩
/-- Circuit `j`'s template length. -/
def rQ (j : Fin 4) : Fin LNR := ⟨112 + j.val, by have := j.isLt; show 112 + j.val < 512; omega⟩
/-- The output counter. -/
def rOP : Fin LNR := ⟨127, by decide⟩
/-- The front's population length of circuit `j` (`FrontOut.vL`). -/
def rL (j : Fin 4) : Fin LNR := ⟨330 + j.val, by have := j.isLt; show 330 + j.val < 512; omega⟩
/-- The template length program's block. -/
def wB : Fin 30 ↪ Fin LNR := ⟨fun i => ⟨130 + i.val, by have := i.isLt; show 130 + i.val < 512; omega⟩,
  fun i j h => by simp only [Fin.mk.injEq] at h; exact Fin.ext (by omega)⟩

theorem rH_val (j : Fin 4) : (rH j).val = 100 + j.val := rfl
theorem rP_val : rP.val = 104 := rfl
theorem rT_val (j : Fin 4) : (rT j).val = 108 + j.val := rfl
theorem rQ_val (j : Fin 4) : (rQ j).val = 112 + j.val := rfl
theorem rOP_val : rOP.val = 127 := rfl
theorem rL_val (j : Fin 4) : (rL j).val = 330 + j.val := rfl
theorem wB_val (i : Fin 30) : (wB i).val = 130 + i.val := rfl
theorem G32_val : (SymDec.G 32).val = 440 := rfl
theorem G33_val : (SymDec.G 33).val = 441 := rfl
theorem G35_val : (SymDec.G 35).val = 443 := rfl
theorem G39_val : (SymDec.G 39).val = 447 := rfl
theorem G41_val : (SymDec.G 41).val = 449 := rfl
theorem dA_val : SymDec.dA.val = 321 := rfl

/-- A register other than the one written keeps its value. -/
theorem setv_other {ns nr : ℕ} (σ : WState ns nr) (r q : Fin nr) (v : ℕ) (h : q.val ≠ r.val) :
    (σ.setv r v).val q = σ.val q := by
  simp only [WState.setv_val]
  exact Function.update_of_ne (fne h) _ _

/-- The template scratch stream of circuit `j`. -/
def oT (x : ℕ) (hx : DataDock.DT + 8 ≤ x) (j : Fin 4) : Fin (LNS x + 1) :=
  sT x ⟨DataDock.DT + 3 + j.val, by have := j.isLt; omega⟩

theorem oT_val (x : ℕ) (hx : DataDock.DT + 8 ≤ x) (j : Fin 4) : (oT x hx j).val = 161 + (DataDock.DT + 3 + j.val) :=
  rfl

theorem oT_inj (x : ℕ) (hx : DataDock.DT + 8 ≤ x) : Function.Injective (oT x hx) := fun i j h => by
  have := congrArg Fin.val h
  rw [oT_val, oT_val] at this
  exact Fin.ext (by omega)

/-! ## The template length's interface (item 6) -/

/-- The stage-5 template's length at `M`, `B`, rows of length `L`. -/
def tplNum (M B L : ℕ) : ℕ :=
  (FinalPass.ListEval.levelWord M (⟨M, B⟩ : Lists.BaseListParams).J (⟨M, B⟩ : Lists.BaseListParams).W
    (fun _ => List.replicate L false)).length

/-- **The template length program's interface** (the statement of `tplLen_spec`, with `tp` for the program). -/
def TplIface (Kt Et : ℕ)
    (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr) :
    Prop :=
  ∀ {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RM RB RJ RL RT : Fin nr),
    [RM, RB, RJ, RL, RT].Nodup → (∀ i, W i ∉ [RM, RB, RJ, RL, RT]) → ∀ (σ : WState ns nr) (M B L : ℕ),
    σ.val RM = M → σ.val RB = B → σ.val RJ = (⟨M, B⟩ : Lists.BaseListParams).J → σ.val RL = L → σ.val RT = 0 →
    (∀ i, σ.val (W i) = 0) → σ.st O = [] → σ.sh O = 0 → Kt * (M + B + L + 2) ^ Et ≤ cap →
    ∃ (τ : WState ns nr) (c : ℕ), WExec cap (tp O W RM RB RJ RL RT) σ τ c ∧ τ.val RT = tplNum M B L ∧
      (∀ q, q ≠ RT → τ.val q = σ.val q) ∧ (∀ i, i ≠ O → τ.st i = σ.st i) ∧
      (τ.st O).length ≤ Kt * (M + B + L + 2) ^ Et ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧ c ≤ Kt * (M + B + L + 2) ^ Et

/-! ## Phase H: the gate tables' widths -/

section PhaseH
variable {ns : ℕ} (S : Fin 4 → Fin (ns + 1))

/-- Phase H: `tabHW` on each slot tape. -/
def tabHs : WM ns LNR :=
  .seq (tabHW (S 0) (rH 0) rP) (.seq (tabHW (S 1) (rH 1) rP) (.seq (tabHW (S 2) (rH 2) rP) (tabHW (S 3) (rH 3) rP)))

/-- Phase H after `k` circuits. -/
def InvH {n : ℕ} (G : Fin 4 → List (NormalizedThresholdGate n)) (σ0 σ : WState ns LNR) (k : ℕ) : Prop :=
  (∀ j : Fin 4, j.val < k → σ.val (rH j) = PrimT.tabH (G j)) ∧
  (∀ q : Fin LNR, (∀ j : Fin 4, j.val < k → q ≠ rH j) → σ.val q = σ0.val q) ∧
  σ.st = σ0.st ∧ σ.sh = σ0.sh ∧ σ.cell = σ0.cell

theorem invH_step (cap : ℕ) {n : ℕ} (G : Fin 4 → List (NormalizedThresholdGate n)) (σ0 σ : WState ns LNR) (k : ℕ)
    (j : Fin 4) (hj : j.val = k) (hI : InvH G σ0 σ k) (hh : σ0.sh (S j) = 0) (hz : σ0.val (rH j) = 0)
    (hP : σ0.val rP = 0)
    (hO : σ0.st (S j) = FinalPass.Corner.gatesW (PrimT.tabH (G j)) (G j) ∨ (σ0.st (S j) = [] ∧ G j = []))
    (hcap : 2 * PrimT.tabH (G j) + 1 ≤ cap) :
    WExec cap (tabHW (S j) (rH j) rP) σ (σ.setv (rH j) (PrimT.tabH (G j))) (30 * PrimT.tabH (G j) + 10) ∧
      InvH G σ0 (σ.setv (rH j) (PrimT.tabH (G j))) (k + 1) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hI
  have hjl := j.isLt
  have nHP : rH j ≠ rP := fne (by rw [rH_val, rP_val]; omega)
  have z1 : σ.val (rH j) = 0 := by
    rw [i2 _ (fun j' hj' e => by have := congrArg Fin.val e; rw [rH_val, rH_val] at this; omega)]
    exact hz
  have z2 : σ.val rP = 0 := by
    rw [i2 _ (fun j' hj' e => by have := congrArg Fin.val e; rw [rH_val, rP_val] at this; have := j'.isLt; omega)]
    exact hP
  refine ⟨tabHW_spec cap (S j) (rH j) rP nHP (G j) σ (by rw [i4]; exact hh) z1 z2 (by rw [i3]; exact hO) hcap,
    fun j' hj' => ?_, fun q hq => ?_, i3, i4, i5⟩
  · by_cases e : j' = j
    · subst e
      simp only [WState.setv_val, Function.update_self]
    · have hv : j'.val ≠ j.val := fun h => e (Fin.ext h)
      rw [setv_other _ _ _ _ (by rw [rH_val, rH_val]; omega)]
      exact i1 j' (by omega)
  · have hq1 : q.val ≠ (rH j).val := fun h => hq j (by omega) (Fin.ext h)
    rw [setv_other _ _ _ _ hq1]
    exact i2 q (fun j' hj' => hq j' (by omega))

/-- **Phase H's run**: the four widths into `rH j`, every other register, stream, head and the cell kept. -/
theorem tabHs_run (cap : ℕ) {n : ℕ} (G : Fin 4 → List (NormalizedThresholdGate n)) (σ0 : WState ns LNR)
    (hh : ∀ j, σ0.sh (S j) = 0) (hz : ∀ j, σ0.val (rH j) = 0) (hP : σ0.val rP = 0)
    (hO : ∀ j, σ0.st (S j) = FinalPass.Corner.gatesW (PrimT.tabH (G j)) (G j) ∨ (σ0.st (S j) = [] ∧ G j = []))
    (hcap : ∀ j, 2 * PrimT.tabH (G j) + 1 ≤ cap) :
    ∃ (τ : WState ns LNR) (c : ℕ), WExec cap (tabHs S) σ0 τ c ∧ c ≤ 4 * (30 * cap + 10) + 3 ∧ InvH G σ0 τ 4 := by
  have I0 : InvH G σ0 σ0 0 := ⟨fun j h => absurd h (Nat.not_lt_zero _), fun q _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨e0, I1⟩ := invH_step S cap G σ0 σ0 0 0 rfl I0 (hh 0) (hz 0) hP (hO 0) (hcap 0)
  obtain ⟨e1, I2⟩ := invH_step S cap G σ0 _ 1 1 rfl I1 (hh 1) (hz 1) hP (hO 1) (hcap 1)
  obtain ⟨e2, I3⟩ := invH_step S cap G σ0 _ 2 2 rfl I2 (hh 2) (hz 2) hP (hO 2) (hcap 2)
  obtain ⟨e3, I4⟩ := invH_step S cap G σ0 _ 3 3 rfl I3 (hh 3) (hz 3) hP (hO 3) (hcap 3)
  refine ⟨_, _, WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)), ?_, I4⟩
  have c0 := hcap 0
  have c1 := hcap 1
  have c2 := hcap 2
  have c3 := hcap 3
  omega

end PhaseH

/-! ## Phase T: the flat tables' lengths -/

section PhaseT
variable {ns : ℕ}

/-- The flat table length of a population of length `L` (J, walk length `t`). -/
def tvOf (L J Wl : ℕ) : ℕ := ((2 * L + 1) * (J + 1) + 1) * Wl + 1

/-- Circuit `j`'s flat table length into `rT j` (through `R7 0`). -/
def tabLenP (j : Fin 4) : WM ns LNR := .seq (tabLenW (rL j) (SymDec.G 35) (SymDec.G 39)) (WM.move (R7 0) (rT j))

theorem tabLenP_run (cap : ℕ) (j : Fin 4) (σ : WState ns LNR) (L J Wl : ℕ) (vL : σ.val (rL j) = L)
    (vJ : σ.val (SymDec.G 35) = J) (vW : σ.val (SymDec.G 39) = Wl)
    (hz : ∀ q : Fin LNR, 120 ≤ q.val → q.val ≤ 126 → σ.val q = 0) (hT : σ.val (rT j) = 0)
    (hc : ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) + L + J + 2 ≤ cap) :
    ∃ c, WExec cap (tabLenP j) σ (σ.setv (rT j) (tvOf L J Wl)) c ∧ c ≤ 400 * (L + J + Wl + 2) ^ 3 + 7 * cap + 2 := by
  have hjl := j.isLt
  obtain ⟨c1, e1, hc1⟩ := tabLen_run cap (rL j) (SymDec.G 35) (SymDec.G 39) (Or.inr (by rw [rL_val]; omega))
    (Or.inr (by rw [G35_val]; omega)) (Or.inr (by rw [G39_val]; omega)) σ L J Wl vL vJ vW hz hc
  have k1 : ((2 * L + 1) * (J + 1) + 1) * (Wl + 1) = ((2 * L + 1) * (J + 1) + 1) * Wl + ((2 * L + 1) * (J + 1) + 1) := by
    ring
  have hvc : tvOf L J Wl ≤ cap := by unfold tvOf; omega
  have r70 : (R7 0).val = 120 := rfl
  have n0T : R7 0 ≠ rT j := fne (by rw [r70, rT_val]; omega)
  have z0 : σ.val (R7 0) = 0 := hz _ (by rw [r70]) (by rw [r70]; omega)
  have e2 := wmove_spec cap (R7 0) (rT j) n0T (tvOf L J Wl) (σ.setv (R7 0) (tvOf L J Wl))
    (by simp only [WState.setv_val, Function.update_self])
    (by simp only [WState.setv_val, Function.update_self]; unfold tvOf at hvc ⊢; exact hvc)
    (by rw [setv_other _ _ _ _ (by rw [r70, rT_val]; omega), hT]; simp only [WState.setv_val, Function.update_self]
        unfold tvOf at hvc ⊢; omega)
  rw [show (σ.setv (R7 0) (tvOf L J Wl)).val (rT j) + (σ.setv (R7 0) (tvOf L J Wl)).val (R7 0) = tvOf L J Wl by
    rw [setv_other _ _ _ _ (by rw [r70, rT_val]; omega), hT]; simp only [WState.setv_val, Function.update_self]
    unfold tvOf; omega] at e2
  rw [wsetv_setv] at e2
  have es : σ.setv (R7 0) 0 = σ := by
    have := wsetv_same σ (R7 0)
    rwa [z0] at this
  rw [es] at e2
  refine ⟨_, WExec.seq e1 e2, ?_⟩
  omega

/-- Phase T: the four flat table lengths. -/
def tabLens : WM ns LNR := .seq (tabLenP 0) (.seq (tabLenP 1) (.seq (tabLenP 2) (tabLenP 3)))

/-- Phase T after `k` circuits. -/
def InvT (L : Fin 4 → ℕ) (J Wl : ℕ) (σ0 σ : WState ns LNR) (k : ℕ) : Prop :=
  (∀ j : Fin 4, j.val < k → σ.val (rT j) = tvOf (L j) J Wl) ∧
  (∀ q : Fin LNR, (∀ j : Fin 4, j.val < k → q ≠ rT j) → σ.val q = σ0.val q) ∧
  σ.st = σ0.st ∧ σ.sh = σ0.sh ∧ σ.cell = σ0.cell

theorem invT_step (cap : ℕ) (L : Fin 4 → ℕ) (J Wl : ℕ) (σ0 σ : WState ns LNR) (k : ℕ) (j : Fin 4) (hj : j.val = k)
    (hI : InvT L J Wl σ0 σ k) (vL : σ0.val (rL j) = L j) (vJ : σ0.val (SymDec.G 35) = J)
    (vW : σ0.val (SymDec.G 39) = Wl) (hz : ∀ q : Fin LNR, 120 ≤ q.val → q.val ≤ 126 → σ0.val q = 0)
    (hT : σ0.val (rT j) = 0) (hc : ((2 * L j + 1) * (J + 1) + 1) * (Wl + 1) + L j + J + 2 ≤ cap) :
    ∃ c, WExec cap (tabLenP j) σ (σ.setv (rT j) (tvOf (L j) J Wl)) c ∧
      c ≤ 400 * (L j + J + Wl + 2) ^ 3 + 7 * cap + 2 ∧ InvT L J Wl σ0 (σ.setv (rT j) (tvOf (L j) J Wl)) (k + 1) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := hI
  have hjl := j.isLt
  have keep : ∀ q : Fin LNR, (q.val < 108 ∨ 112 ≤ q.val) → σ.val q = σ0.val q := fun q hq =>
    i2 q (fun j' _ e => by have := congrArg Fin.val e; rw [rT_val] at this; have := j'.isLt; omega)
  obtain ⟨c, e, hc'⟩ := tabLenP_run cap j σ (L j) J Wl (by rw [keep _ (by rw [rL_val]; omega)]; exact vL)
    (by rw [keep _ (by rw [G35_val]; omega)]; exact vJ) (by rw [keep _ (by rw [G39_val]; omega)]; exact vW)
    (fun q h1 h2 => by rw [keep q (by omega)]; exact hz q h1 h2)
    (by rw [i2 _ (fun j' hj' e => by have := congrArg Fin.val e; rw [rT_val, rT_val] at this; omega)]; exact hT) hc
  refine ⟨c, e, hc', fun j' hj' => ?_, fun q hq => ?_, i3, i4, i5⟩
  · by_cases e' : j' = j
    · subst e'
      simp only [WState.setv_val, Function.update_self]
    · have hv : j'.val ≠ j.val := fun h => e' (Fin.ext h)
      rw [setv_other _ _ _ _ (by rw [rT_val, rT_val]; omega)]
      exact i1 j' (by omega)
  · have hq1 : q.val ≠ (rT j).val := fun h => hq j (by omega) (Fin.ext h)
    rw [setv_other _ _ _ _ hq1]
    exact i2 q (fun j' hj' => hq j' (by omega))

/-- **Phase the run**: the four flat table lengths into `rT j`, every other register, stream, head and the cell kept. -/
theorem tabLens_run (cap : ℕ) (L : Fin 4 → ℕ) (J Wl Y : ℕ) (σ0 : WState ns LNR) (vL : ∀ j, σ0.val (rL j) = L j)
    (vJ : σ0.val (SymDec.G 35) = J) (vW : σ0.val (SymDec.G 39) = Wl)
    (hz : ∀ q : Fin LNR, 120 ≤ q.val → q.val ≤ 126 → σ0.val q = 0) (hT : ∀ j, σ0.val (rT j) = 0)
    (hc : ∀ j, ((2 * L j + 1) * (J + 1) + 1) * (Wl + 1) + L j + J + 2 ≤ cap)
    (hY : ∀ j, 400 * (L j + J + Wl + 2) ^ 3 ≤ Y) :
    ∃ (τ : WState ns LNR) (c : ℕ), WExec cap tabLens σ0 τ c ∧ c ≤ 4 * (Y + 7 * cap + 2) + 3 ∧
      InvT L J Wl σ0 τ 4 := by
  have I0 : InvT L J Wl σ0 σ0 0 := ⟨fun j h => absurd h (Nat.not_lt_zero _), fun q _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c0, e0, h0, I1⟩ := invT_step cap L J Wl σ0 σ0 0 0 rfl I0 (vL 0) vJ vW hz (hT 0) (hc 0)
  obtain ⟨c1, e1, h1, I2⟩ := invT_step cap L J Wl σ0 _ 1 1 rfl I1 (vL 1) vJ vW hz (hT 1) (hc 1)
  obtain ⟨c2, e2, h2, I3⟩ := invT_step cap L J Wl σ0 _ 2 2 rfl I2 (vL 2) vJ vW hz (hT 2) (hc 2)
  obtain ⟨c3, e3, h3, I4⟩ := invT_step cap L J Wl σ0 _ 3 3 rfl I3 (vL 3) vJ vW hz (hT 3) (hc 3)
  refine ⟨_, _, WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)), ?_, I4⟩
  have y0 := hY 0
  have y1 := hY 1
  have y2 := hY 2
  have y3 := hY 3
  omega

end PhaseT

/-! ## Phase Q: the templates' lengths -/

section PhaseQ
variable {ns : ℕ} (Kt Et : ℕ)
  (tp : ∀ {ns nr : ℕ}, Fin (ns + 1) → (Fin 30 ↪ Fin nr) → Fin nr → Fin nr → Fin nr → Fin nr → Fin nr → WM ns nr)
  (O : Fin 4 → Fin (ns + 1))

/-- Phase Q: the template length program per circuit, each on its own scratch stream. -/
def tpls : WM ns LNR :=
  .seq (tp (O 0) wB (SymDec.G 32) (SymDec.G 33) (SymDec.G 35) (rL 0) (rQ 0))
    (.seq (tp (O 1) wB (SymDec.G 32) (SymDec.G 33) (SymDec.G 35) (rL 1) (rQ 1))
      (.seq (tp (O 2) wB (SymDec.G 32) (SymDec.G 33) (SymDec.G 35) (rL 2) (rQ 2))
        (tp (O 3) wB (SymDec.G 32) (SymDec.G 33) (SymDec.G 35) (rL 3) (rQ 3))))

/-- Phase Q after `k` circuits. -/
def InvQ (M B : ℕ) (L : Fin 4 → ℕ) (σ0 σ : WState ns LNR) (k : ℕ) : Prop :=
  (∀ j : Fin 4, j.val < k → σ.val (rQ j) = tplNum M B (L j)) ∧
  (∀ q : Fin LNR, (∀ j : Fin 4, j.val < k → q ≠ rQ j) → σ.val q = σ0.val q) ∧
  (∀ i, (∀ j : Fin 4, j.val < k → i ≠ O j) → σ.st i = σ0.st i) ∧
  (∀ j : Fin 4, j.val < k → (σ.st (O j)).length ≤ Kt * (M + B + L j + 2) ^ Et) ∧
  σ.sh = σ0.sh ∧ σ.cell = σ0.cell

theorem tp_regs (j : Fin 4) : [SymDec.G 32, SymDec.G 33, SymDec.G 35, rL j, rQ j].Nodup ∧
    ∀ i, wB i ∉ [SymDec.G 32, SymDec.G 33, SymDec.G 35, rL j, rQ j] := by
  have hjl := j.isLt
  refine ⟨List.Nodup.of_map Fin.val ?_, fun i h => ?_⟩
  · change [440, 441, 443, 330 + j.val, 112 + j.val].Nodup
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false, not_false_eq_true,
      and_true]
    omega
  · have hil := i.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with e | e | e | e | e <;>
    · have := congrArg Fin.val e
      simp only [wB_val, G32_val, G33_val, G35_val, rL_val, rQ_val] at this
      omega

theorem invQ_step (htp : TplIface Kt Et tp) (hOi : Function.Injective O) (cap : ℕ) (M B : ℕ) (L : Fin 4 → ℕ)
    (σ0 σ : WState ns LNR) (k : ℕ) (j : Fin 4) (hj : j.val = k) (hI : InvQ Kt Et O M B L σ0 σ k)
    (vM : σ0.val (SymDec.G 32) = M) (vB : σ0.val (SymDec.G 33) = B)
    (vJ : σ0.val (SymDec.G 35) = (⟨M, B⟩ : Lists.BaseListParams).J) (vL : σ0.val (rL j) = L j)
    (hQ : σ0.val (rQ j) = 0) (hW : ∀ i, σ0.val (wB i) = 0) (hO : σ0.st (O j) = []) (hOh : σ0.sh (O j) = 0)
    (hcap : Kt * (M + B + L j + 2) ^ Et ≤ cap) :
    ∃ (τ : WState ns LNR) (c : ℕ), WExec cap (tp (O j) wB (SymDec.G 32) (SymDec.G 33) (SymDec.G 35) (rL j) (rQ j)) σ τ c ∧
      c ≤ Kt * (M + B + L j + 2) ^ Et ∧ InvQ Kt Et O M B L σ0 τ (k + 1) := by
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := hI
  have hjl := j.isLt
  have keep : ∀ q : Fin LNR, (q.val < 112 ∨ 116 ≤ q.val) → σ.val q = σ0.val q := fun q hq =>
    i2 q (fun j' _ e => by have := congrArg Fin.val e; rw [rQ_val] at this; have := j'.isLt; omega)
  have hOj : ∀ j' : Fin 4, j'.val < k → O j ≠ O j' := fun j' hj' e => by
    have := congrArg Fin.val (hOi e); omega
  obtain ⟨hnd, hwn⟩ := tp_regs j
  obtain ⟨τ, c, e, v1, v2, s1, l1, sh1, ce1, hc1⟩ := htp cap (O j) wB (SymDec.G 32) (SymDec.G 33) (SymDec.G 35) (rL j)
    (rQ j) hnd hwn σ M B (L j) (by rw [keep _ (by rw [G32_val]; omega)]; exact vM)
    (by rw [keep _ (by rw [G33_val]; omega)]; exact vB) (by rw [keep _ (by rw [G35_val]; omega)]; exact vJ)
    (by rw [keep _ (by rw [rL_val]; omega)]; exact vL)
    (by rw [i2 _ (fun j' hj' e => by have := congrArg Fin.val e; rw [rQ_val, rQ_val] at this; omega)]; exact hQ)
    (fun i => by rw [keep _ (by rw [wB_val]; omega)]; exact hW i) (by rw [i3 _ hOj]; exact hO)
    (by rw [i5]; exact hOh) hcap
  refine ⟨τ, c, e, hc1, fun j' hj' => ?_, fun q hq => ?_, fun i hi => ?_, fun j' hj' => ?_, by rw [sh1, i5],
    by rw [ce1, i6]⟩
  · by_cases e' : j' = j
    · subst e'
      exact v1
    · have hv : j'.val ≠ j.val := fun h => e' (Fin.ext h)
      rw [v2 _ (fne (by rw [rQ_val, rQ_val]; omega))]
      exact i1 j' (by omega)
  · rw [v2 q (hq j (by omega))]
    exact i2 q (fun j' hj' => hq j' (by omega))
  · rw [s1 i (hi j (by omega))]
    exact i3 i (fun j' hj' => hi j' (by omega))
  · by_cases e' : j' = j
    · subst e'
      exact l1
    · have hv : j'.val ≠ j.val := fun h => e' (Fin.ext h)
      rw [s1 _ (fun h => e' (hOi h))]
      exact i4 j' (by omega)

/-- **Phase Q's run**: the four template lengths into `rQ j`, each template on its scratch stream `O j`; every other
register, stream, head and the cell kept. -/
theorem tpls_run (htp : TplIface Kt Et tp) (hOi : Function.Injective O) (cap : ℕ) (M B : ℕ) (L : Fin 4 → ℕ)
    (σ0 : WState ns LNR) (vM : σ0.val (SymDec.G 32) = M) (vB : σ0.val (SymDec.G 33) = B)
    (vJ : σ0.val (SymDec.G 35) = (⟨M, B⟩ : Lists.BaseListParams).J) (vL : ∀ j, σ0.val (rL j) = L j)
    (hQ : ∀ j, σ0.val (rQ j) = 0) (hW : ∀ i, σ0.val (wB i) = 0) (hO : ∀ j, σ0.st (O j) = [])
    (hOh : ∀ j, σ0.sh (O j) = 0) (hcap : ∀ j, Kt * (M + B + L j + 2) ^ Et ≤ cap) :
    ∃ (τ : WState ns LNR) (c : ℕ), WExec cap (tpls tp O) σ0 τ c ∧ c ≤ 4 * cap + 3 ∧ InvQ Kt Et O M B L σ0 τ 4 := by
  have I0 : InvQ Kt Et O M B L σ0 σ0 0 :=
    ⟨fun j h => absurd h (Nat.not_lt_zero _), fun q _ => rfl, fun i _ => rfl, fun j h => absurd h (Nat.not_lt_zero _),
      rfl, rfl⟩
  obtain ⟨σ1, c0, e0, h0, I1⟩ := invQ_step Kt Et tp O htp hOi cap M B L σ0 σ0 0 0 rfl I0 vM vB vJ (vL 0) (hQ 0) hW
    (hO 0) (hOh 0) (hcap 0)
  obtain ⟨σ2, c1, e1, h1, I2⟩ := invQ_step Kt Et tp O htp hOi cap M B L σ0 σ1 1 1 rfl I1 vM vB vJ (vL 1) (hQ 1) hW
    (hO 1) (hOh 1) (hcap 1)
  obtain ⟨σ3, c2, e2, h2, I3⟩ := invQ_step Kt Et tp O htp hOi cap M B L σ0 σ2 2 2 rfl I2 vM vB vJ (vL 2) (hQ 2) hW
    (hO 2) (hOh 2) (hcap 2)
  obtain ⟨σ4, c3, e3, h3, I4⟩ := invQ_step Kt Et tp O htp hOi cap M B L σ0 σ3 3 3 rfl I3 vM vB vJ (vL 3) (hQ 3) hW
    (hO 3) (hOh 3) (hcap 3)
  refine ⟨_, _, WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3)), ?_, I4⟩
  have y0 := hcap 0
  have y1 := hcap 1
  have y2 := hcap 2
  have y3 := hcap 3
  omega

end PhaseQ

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA
