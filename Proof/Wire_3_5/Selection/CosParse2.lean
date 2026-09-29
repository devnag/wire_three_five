import Proof.Wire_3_5.Selection.CosParse1

/-! # C1.5 parse, part 2: the shape registers, the widths and the ruler (P3:1188-1197, 1337-1345)

Paper: "The center bits can be divided into two halves differing in size by at most one while keeping each code block on
its assigned side" (P3:1196-1197): the gate routine reads the partition's shape in unary registers (`h = r/2`, `b`, `s`,
the free counts `⌈(n − rb)/2⌉`, `⌊(n − rb)/2⌋`, `V + 1`); the words it adds have width `W`. `shapeP` copies them from
PA's block (PA's `halveM` for the free counts); `widthP` computes `W = 8(L + n + 2)`, `2W + 1` and the rewind bound `8W²`
(PA's `dbl`, `mulAddW`); `rulerP` writes the conversion ruler `false :: 1^W` (`convNatW` and C6's `ratReadW` step
along it). Main declarations: `shapeP_spec`, `widthP_spec`, `rulerP_spec`. Paper quantity: the partition's shape and the
arithmetic width. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Cos
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (emitW)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (dbl dbl_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (halveM halveM_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith (mulAddW mulAddW_spec)

/-! ## The shape registers -/

/-- `b := a` over `b = 0`, as a state step. -/
theorem cp_spec (cap : ℕ) (a b t : Fin 112) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (σ : WState 49 112) (v : ℕ)
    (ha : σ.val a = v) (hb : σ.val b = 0) (ht : σ.val t = 0) (hv : v ≤ cap) :
    WExec cap (FinalPass.Hash4.wcopyR a b t) σ (σ.setv b v) (18 * v + 3) := by
  have x := FinalPass.Hash4.wcopyR_spec cap a b t hab hat hbt σ hb ht (by rw [ha]; exact hv)
  rw [ha] at x; exact x

/-- `r += 1` as a state step. -/
theorem inc_spec' (cap : ℕ) (r : Fin 112) (σ : WState 49 112) (v : ℕ) (hr : σ.val r = v) (hv : v < cap) :
    WExec cap (.inc r) σ (σ.setv r (v + 1)) 3 := by
  have x := WExec.inc (cap := cap) r σ (by rw [hr]; exact hv)
  rw [hr] at x; exact x

/-- `w := w/2` with the remainder cleared, as two state steps. -/
theorem half_spec (cap : ℕ) (w : Fin 112) (hw : w ≠ 91) (hw' : w ≠ 90) (σ : WState 49 112) (v : ℕ) (hv : σ.val w = v)
    (h91 : σ.val 91 = 0) (h90 : σ.val 90 = 0) (hc : v + 1 ≤ cap) :
    WExec cap (halveM w 91 90) σ ((σ.setv w (v / 2)).setv 90 (v % 2)) (9 * v + 6) ∧
      WExec cap (WM.clear 90) ((σ.setv w (v / 2)).setv 90 (v % 2)) (σ.setv w (v / 2)) (3 * (v % 2) + 1) := by
  have x1 := halveM_spec cap w 91 90 hw hw' (by decide) σ h91 h90 (by omega) (by omega)
  rw [hv] at x1
  have x2 := wclear_spec (cap := cap) 90 (v % 2) ((σ.setv w (v / 2)).setv 90 (v % 2)) (by simp) (by simp; omega)
  refine ⟨x1, WExec.cast cap x2 ?_ le_rfl⟩
  rw [wsetv_setv, Gate.wsetv_zero _ _ (by simp [Ne.symm hw', h90])]

/-- The shape's cost. -/
def shapeCost (a b c d L n : ℕ) : ℕ :=
  18 * a + 3 + 1 + (18 * b + 3 + 1 + (18 * c + 3 + 1 + (18 * d + 3 + 1 + (3 + 1 + (9 * (d + 1) + 6 + 1 +
    (3 * ((d + 1) % 2) + 1 + 1 + (18 * d + 3 + 1 + (9 * d + 6 + 1 + (3 * (d % 2) + 1 + 1 + (18 * L + 3 + 1 +
      (3 + 1 + (18 * n + 3 + 1 + 3))))))))))))

theorem shape5_spec (cap : ℕ) (σ : WState 49 112) (L n : ℕ) (h85 : σ.val 85 = L) (h64 : σ.val 64 = n)
    (h5 : σ.val 5 = 0) (h60 : σ.val 60 = 0) (h89 : σ.val 89 = 0) (hc : L + n + 2 ≤ cap) :
    WExec cap (.seq (FinalPass.Hash4.wcopyR 85 5 89) (.seq (.inc 5) (.seq (FinalPass.Hash4.wcopyR 64 60 89)
      (.inc 60)))) σ ((σ.setv 5 (L + 1)).setv 60 (n + 1)) (18 * L + 3 + 1 + (3 + 1 + (18 * n + 3 + 1 + 3))) := by
  have x1 := cp_spec cap 85 5 89 (by decide) (by decide) (by decide) σ L h85 h5 h89 (by omega)
  have x2 := inc_spec' cap 5 (σ.setv 5 L) L (by simp) (by omega)
  rw [wsetv_setv] at x2
  have x3 := cp_spec cap 64 60 89 (by decide) (by decide) (by decide) (σ.setv 5 (L + 1)) n (by simp [h64])
    (by simp [h60]) (by simp [h89]) (by omega)
  have x4 := inc_spec' cap 60 ((σ.setv 5 (L + 1)).setv 60 n) n (by simp) (by omega)
  rw [wsetv_setv] at x4
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))

theorem shape4_spec (cap : ℕ) (σ : WState 49 112) (d L n : ℕ) (h71 : σ.val 71 = d) (h85 : σ.val 85 = L)
    (h64 : σ.val 64 = n) (h4 : σ.val 4 = 0) (h5 : σ.val 5 = 0) (h60 : σ.val 60 = 0) (h89 : σ.val 89 = 0)
    (h90 : σ.val 90 = 0) (h91 : σ.val 91 = 0) (hc : d + L + n + 2 ≤ cap) :
    WExec cap (.seq (FinalPass.Hash4.wcopyR 71 4 89) (.seq (halveM 4 91 90) (.seq (WM.clear 90)
      (.seq (FinalPass.Hash4.wcopyR 85 5 89) (.seq (.inc 5) (.seq (FinalPass.Hash4.wcopyR 64 60 89) (.inc 60)))))))
      σ (((σ.setv 4 (d / 2)).setv 5 (L + 1)).setv 60 (n + 1))
      (18 * d + 3 + 1 + (9 * d + 6 + 1 + (3 * (d % 2) + 1 + 1 + (18 * L + 3 + 1 + (3 + 1 + (18 * n + 3 + 1 + 3)))))) := by
  have x1 := cp_spec cap 71 4 89 (by decide) (by decide) (by decide) σ d h71 h4 h89 (by omega)
  have x2 := half_spec cap 4 (by decide) (by decide) (σ.setv 4 d) d (by simp) (by simp [h91]) (by simp [h90]) (by omega)
  rw [wsetv_setv] at x2
  have x3 := shape5_spec cap (σ.setv 4 (d / 2)) L n (by simp [h85]) (by simp [h64]) (by simp [h5]) (by simp [h60])
    (by simp [h89]) (by omega)
  exact WExec.seq x1 (WExec.seq x2.1 (WExec.seq x2.2 x3))

theorem shape3_spec (cap : ℕ) (σ : WState 49 112) (d L n : ℕ) (h71 : σ.val 71 = d) (h85 : σ.val 85 = L)
    (h64 : σ.val 64 = n) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = 0) (h5 : σ.val 5 = 0) (h60 : σ.val 60 = 0)
    (h89 : σ.val 89 = 0) (h90 : σ.val 90 = 0) (h91 : σ.val 91 = 0) (hc : d + L + n + 3 ≤ cap) :
    WExec cap (.seq (FinalPass.Hash4.wcopyR 71 3 89) (.seq (.inc 3) (.seq (halveM 3 91 90) (.seq (WM.clear 90)
      (.seq (FinalPass.Hash4.wcopyR 71 4 89) (.seq (halveM 4 91 90) (.seq (WM.clear 90)
        (.seq (FinalPass.Hash4.wcopyR 85 5 89) (.seq (.inc 5) (.seq (FinalPass.Hash4.wcopyR 64 60 89) (.inc 60)))))))))))
      σ ((((σ.setv 3 ((d + 1) / 2)).setv 4 (d / 2)).setv 5 (L + 1)).setv 60 (n + 1))
      (18 * d + 3 + 1 + (3 + 1 + (9 * (d + 1) + 6 + 1 + (3 * ((d + 1) % 2) + 1 + 1 + (18 * d + 3 + 1 + (9 * d + 6 + 1 +
        (3 * (d % 2) + 1 + 1 + (18 * L + 3 + 1 + (3 + 1 + (18 * n + 3 + 1 + 3)))))))))) := by
  have x1 := cp_spec cap 71 3 89 (by decide) (by decide) (by decide) σ d h71 h3 h89 (by omega)
  have x2 := inc_spec' cap 3 (σ.setv 3 d) d (by simp) (by omega)
  rw [wsetv_setv] at x2
  have x3 := half_spec cap 3 (by decide) (by decide) (σ.setv 3 (d + 1)) (d + 1) (by simp) (by simp [h91])
    (by simp [h90]) (by omega)
  rw [wsetv_setv] at x3
  have x4 := shape4_spec cap (σ.setv 3 ((d + 1) / 2)) d L n (by simp [h71]) (by simp [h85]) (by simp [h64])
    (by simp [h4]) (by simp [h5]) (by simp [h60]) (by simp [h89]) (by simp [h90]) (by simp [h91]) (by omega)
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3.1 (WExec.seq x3.2 x4)))

/-- **The shape registers** `Q 0 … Q 5` and `Q 60 = n + 1` from PA's block. -/
theorem shapeP_spec (cap : ℕ) (σ : WState 49 112) (a b c d L n : ℕ) (h70 : σ.val 70 = a) (h69 : σ.val 69 = b)
    (h68 : σ.val 68 = c) (h71 : σ.val 71 = d) (h85 : σ.val 85 = L) (h64 : σ.val 64 = n)
    (hz : ∀ r : Fin 112, (r.val ≤ 5 ∨ r = 60 ∨ r = 89 ∨ r = 90 ∨ r = 91) → σ.val r = 0)
    (hcap : a + b + c + d + L + n + 3 ≤ cap) :
    WExec cap shapeP σ (((((((σ.setv 0 a).setv 1 b).setv 2 c).setv 3 ((d + 1) / 2)).setv 4 (d / 2)).setv 5 (L + 1)).setv
      60 (n + 1)) (shapeCost a b c d L n) := by
  have z : ∀ r : Fin 112, (r.val ≤ 5 ∨ r = 60 ∨ r = 89 ∨ r = 90 ∨ r = 91) → σ.val r = 0 := hz
  have x1 := cp_spec cap 70 0 89 (by decide) (by decide) (by decide) σ a h70 (z 0 (by decide)) (z 89 (by decide))
    (by omega)
  have x2 := cp_spec cap 69 1 89 (by decide) (by decide) (by decide) (σ.setv 0 a) b (by simp [h69])
    (by simp [z 1 (by decide)]) (by simp [z 89 (by decide)]) (by omega)
  have x3 := cp_spec cap 68 2 89 (by decide) (by decide) (by decide) ((σ.setv 0 a).setv 1 b) c (by simp [h68])
    (by simp [z 2 (by decide)]) (by simp [z 89 (by decide)]) (by omega)
  have x4 := shape3_spec cap (((σ.setv 0 a).setv 1 b).setv 2 c) d L n (by simp [h71]) (by simp [h85]) (by simp [h64])
    (by simp [z 3 (by decide)]) (by simp [z 4 (by decide)]) (by simp [z 5 (by decide)]) (by simp [z 60 (by decide)])
    (by simp [z 89 (by decide)]) (by simp [z 90 (by decide)]) (by simp [z 91 (by decide)]) (by omega)
  exact WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))) rfl (by unfold shapeCost; omega)

/-! ## The widths -/

/-- `r := 2r` as a state step. -/
theorem dbl_spec' (cap : ℕ) (p : Fin 112) (hp : p ≠ 89) (σ : WState 49 112) (v : ℕ) (hv : σ.val p = v)
    (h89 : σ.val 89 = 0) (hc : 2 * v ≤ cap) : WExec cap (dbl p 89) σ (σ.setv p (2 * v)) (18 * v + 3) := by
  have x := dbl_spec cap p 89 hp σ h89 (by rw [hv]; exact hc)
  rw [hv] at x; exact x

/-- The widths' suffixes. -/
def wT5 : WM 49 112 := .seq (dbl 87 89) (.seq (dbl 87 89) (dbl 87 89))
def wT4 : WM 49 112 := .seq (FinalPass.Hash4.wcopyR 86 92 89) (.seq (mulAddW zMul) (.seq (WM.clear 92) wT5))
def wT3 : WM 49 112 := .seq (FinalPass.Hash4.wcopyR 86 95 89) (.seq (dbl 95 89) (.seq (.inc 95) wT4))
def wT2 : WM 49 112 := .seq (dbl 86 89) (.seq (dbl 86 89) (.seq (dbl 86 89) wT3))

theorem widthP_eq : widthP = .seq (FinalPass.Hash4.wcopyR 85 86 89) (.seq (addR 64 89 86) (.seq (.inc 86)
    (.seq (.inc 86) wT2))) := rfl

/-- The suffixes' costs. -/
def cT5 (u : ℕ) : ℕ := 18 * u + 3 + 1 + (18 * (2 * u) + 3 + 1 + (18 * (2 * (2 * u)) + 3))
def cT4 (W : ℕ) : ℕ := 18 * W + 3 + 1 + (W * (18 * W + 8) + 18 * W + 10 + 1 + (3 * W + 1 + 1 + cT5 (W * W)))
def cT3 (W : ℕ) : ℕ := 18 * W + 3 + 1 + (18 * W + 3 + 1 + (3 + 1 + cT4 W))
def cT2 (u : ℕ) : ℕ := 18 * u + 3 + 1 + (18 * (2 * u) + 3 + 1 + (18 * (2 * (2 * u)) + 3 + 1 + cT3 (8 * u)))

/-- The widths' cost. -/
def widthCost (L n : ℕ) : ℕ :=
  18 * L + 3 + 1 + (n * (3 + 8) + 1 + 1 + (7 * n + 1) + 1 + (3 + 1 + (3 + 1 + cT2 (L + n + 2))))

theorem wT5_spec (cap : ℕ) (σ : WState 49 112) (u : ℕ) (h87 : σ.val 87 = u) (h89 : σ.val 89 = 0)
    (hc : 8 * u ≤ cap) : WExec cap wT5 σ (σ.setv 87 (8 * u)) (cT5 u) := by
  have x1 := dbl_spec' cap 87 (by decide) σ u h87 h89 (by omega)
  have x2 := dbl_spec' cap 87 (by decide) (σ.setv 87 (2 * u)) (2 * u) (by simp) (by simp [h89]) (by omega)
  rw [wsetv_setv] at x2
  have x3 := dbl_spec' cap 87 (by decide) (σ.setv 87 (2 * (2 * u))) (2 * (2 * u)) (by simp) (by simp [h89]) (by omega)
  rw [wsetv_setv, show 2 * (2 * (2 * u)) = 8 * u by ring] at x3
  exact WExec.seq x1 (WExec.seq x2 x3)

theorem wT4_spec (cap : ℕ) (σ : WState 49 112) (W : ℕ) (h86 : σ.val 86 = W) (h87 : σ.val 87 = 0)
    (h89 : σ.val 89 = 0) (h92 : σ.val 92 = 0) (h93 : σ.val 93 = 0) (hc : 8 * (W * W) + W + 1 ≤ cap) :
    WExec cap wT4 σ (σ.setv 87 (8 * (W * W))) (cT4 W) := by
  have hWW : W ≤ W * W := Nat.le_mul_self W
  have x1 := cp_spec cap 86 92 89 (by decide) (by decide) (by decide) σ W h86 h92 h89 (by omega)
  have x2 := mulAddW_spec cap zMul (σ.setv 92 W) (by simp [zMul, h89]) (by simp [zMul, h93]) (by simp [zMul]; omega)
    (by simp [zMul, h86, h87]; omega) (by simp [zMul, h86]; omega)
  have ez : (σ.setv 92 W).val (zMul 0) = W ∧ (σ.setv 92 W).val (zMul 1) = W ∧ (σ.setv 92 W).val (zMul 2) = 0 :=
    ⟨by simp [zMul, h86], by simp [zMul], by simp [zMul, h87]⟩
  rw [ez.1, ez.2.1, ez.2.2, Nat.zero_add, show zMul 2 = 87 from rfl] at x2
  have x3 := wclear_spec (cap := cap) 92 W ((σ.setv 92 W).setv 87 (W * W)) (by simp) (by simp; omega)
  have e3 : ((σ.setv 92 W).setv 87 (W * W)).setv 92 0 = σ.setv 87 (W * W) := by
    rw [wsetv_comm _ _ _ (by decide : (92 : Fin 112) ≠ 87), wsetv_setv, Gate.wsetv_zero _ _ (by simp [h92])]
  rw [e3] at x3
  have x4 := wT5_spec cap (σ.setv 87 (W * W)) (W * W) (by simp) (by simp [h89]) (by omega)
  rw [wsetv_setv] at x4
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))

theorem wT3_spec (cap : ℕ) (σ : WState 49 112) (W : ℕ) (h86 : σ.val 86 = W) (h87 : σ.val 87 = 0)
    (h89 : σ.val 89 = 0) (h92 : σ.val 92 = 0) (h93 : σ.val 93 = 0) (h95 : σ.val 95 = 0)
    (hc : 8 * (W * W) + 2 * W + 1 ≤ cap) :
    WExec cap wT3 σ ((σ.setv 95 (2 * W + 1)).setv 87 (8 * (W * W))) (cT3 W) := by
  have x1 := cp_spec cap 86 95 89 (by decide) (by decide) (by decide) σ W h86 h95 h89 (by omega)
  have x2 := dbl_spec' cap 95 (by decide) (σ.setv 95 W) W (by simp) (by simp [h89]) (by omega)
  rw [wsetv_setv] at x2
  have x3 := inc_spec' cap 95 (σ.setv 95 (2 * W)) (2 * W) (by simp) (by omega)
  rw [wsetv_setv] at x3
  have x4 := wT4_spec cap (σ.setv 95 (2 * W + 1)) W (by simp [h86]) (by simp [h87]) (by simp [h89]) (by simp [h92])
    (by simp [h93]) (by omega)
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))

theorem wT2_spec (cap : ℕ) (σ : WState 49 112) (u : ℕ) (h86 : σ.val 86 = u) (h87 : σ.val 87 = 0)
    (h89 : σ.val 89 = 0) (h92 : σ.val 92 = 0) (h93 : σ.val 93 = 0) (h95 : σ.val 95 = 0)
    (hc : 8 * (8 * u * (8 * u)) + 2 * (8 * u) + 1 ≤ cap) :
    WExec cap wT2 σ (((σ.setv 86 (8 * u)).setv 95 (2 * (8 * u) + 1)).setv 87 (8 * (8 * u * (8 * u)))) (cT2 u) := by
  have hu : u ≤ 8 * u * (8 * u) := by nlinarith
  have x1 := dbl_spec' cap 86 (by decide) σ u h86 h89 (by omega)
  have x2 := dbl_spec' cap 86 (by decide) (σ.setv 86 (2 * u)) (2 * u) (by simp) (by simp [h89]) (by omega)
  rw [wsetv_setv] at x2
  have x3 := dbl_spec' cap 86 (by decide) (σ.setv 86 (2 * (2 * u))) (2 * (2 * u)) (by simp) (by simp [h89]) (by omega)
  rw [wsetv_setv, show 2 * (2 * (2 * u)) = 8 * u by ring] at x3
  have x4 := wT3_spec cap (σ.setv 86 (8 * u)) (8 * u) (by simp) (by simp [h87]) (by simp [h89]) (by simp [h92])
    (by simp [h93]) (by simp [h95]) (by omega)
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))

/-- **The widths**: `86 = W = 8(L + n + 2)`, `95 = 2W + 1`, `87 = 8W²`. -/
theorem widthP_spec (cap : ℕ) (σ : WState 49 112) (L n : ℕ) (h85 : σ.val 85 = L) (h64 : σ.val 64 = n)
    (hz : ∀ r : Fin 112, (r = 86 ∨ r = 87 ∨ r = 89 ∨ r = 92 ∨ r = 93 ∨ r = 95) → σ.val r = 0)
    (hcap : 8 * (8 * (L + n + 2) * (8 * (L + n + 2))) + 2 * (8 * (L + n + 2)) + 1 ≤ cap) :
    WExec cap widthP σ (((σ.setv 86 (8 * (L + n + 2))).setv 95 (2 * (8 * (L + n + 2)) + 1)).setv 87
      (8 * (8 * (L + n + 2) * (8 * (L + n + 2))))) (widthCost L n) := by
  have z := hz
  have hb : L + n + 2 ≤ 8 * (8 * (L + n + 2) * (8 * (L + n + 2))) := by nlinarith
  have x1 := cp_spec cap 85 86 89 (by decide) (by decide) (by decide) σ L h85 (z 86 (by decide)) (z 89 (by decide))
    (by omega)
  have x2 := addR_spec cap 64 89 86 (by decide) (by decide) (by decide) (σ.setv 86 L) n (by simp [h64])
    (by simp [z 89 (by decide)]) (by omega) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, wsetv_setv] at x2
  have x3 := inc_spec' cap 86 (σ.setv 86 (L + n)) (L + n) (by simp) (by omega)
  rw [wsetv_setv] at x3
  have x4 := inc_spec' cap 86 (σ.setv 86 (L + n + 1)) (L + n + 1) (by simp) (by omega)
  rw [wsetv_setv, show L + n + 1 + 1 = L + n + 2 by ring] at x4
  have x5 := wT2_spec cap (σ.setv 86 (L + n + 2)) (L + n + 2) (by simp) (by simp [z 87 (by decide)])
    (by simp [z 89 (by decide)]) (by simp [z 92 (by decide)]) (by simp [z 93 (by decide)]) (by simp [z 95 (by decide)])
    hcap
  rw [wsetv_setv] at x5
  rw [widthP_eq]
  exact WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4 x5)))

/-! ## The ruler -/

/-- **The ruler** `false :: 1^W` on `Sm 45`, its head home (`86 = W`, `87 ≥ W + 1`). -/
theorem rulerP_spec (cap : ℕ) (σ : WState 49 112) (W B : ℕ) (hst : σ.st (Sm 45) = []) (hsh : σ.sh (Sm 45) = 0)
    (h86 : σ.val 86 = W) (h87 : σ.val 87 = B) (h92 : σ.val 92 = 0) (h89 : σ.val 89 = 0) (hB : W + 1 ≤ B)
    (hcap : B + W ≤ cap) :
    WExec cap rulerP σ (σ.sets (Sm 45) (false :: List.replicate W true))
      (3 + 1 + (18 * W + 3 + 1 + (7 * W + 1 + 1 + (B * (1 + 8) + 1 + 1 + (7 * B + 1))))) := by
  have x1 := emitW_app cap (Sm 45) false σ (by rw [hsh, hst]; rfl)
  set σ1 := appS σ (Sm 45) [false] with hσ1
  have x2 := FinalPass.Hash4.wcopyR_spec cap 86 92 89 (by decide) (by decide) (by decide) σ1 (by simp [hσ1, h92])
    (by simp [hσ1, h89]) (by simp [hσ1, h86]; omega)
  have e2 : σ1.val 86 = W := by simp [hσ1, h86]
  rw [e2] at x2
  set σ2 := σ1.setv 92 W with hσ2
  have x3 := onesW_spec cap (Sm 45) 92 W σ2 (by simp [hσ2]) (by omega) (by simp [hσ2, hσ1])
  set σ3 := (appS σ2 (Sm 45) (List.replicate W true)).setv 92 0 with hσ3
  have x4 := rewS_spec cap (Sm 45) 87 89 (by decide) σ3 B (by simp [hσ3, hσ2, hσ1, h87]) (by simp [hσ3, hσ2, hσ1, h89])
    (by omega) (by simp [hσ3, hσ2, hσ1, hst]; omega)
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 x4))) ?_ le_rfl
  apply WState.eq
  · funext i; by_cases hi : i = Sm 45
    · subst hi; simp [hsh]
    · simp [hσ3, hσ2, hσ1, Function.update_apply, hi]
  · funext i; by_cases hi : i = Sm 45
    · subst hi; simp [hσ3, hσ2, hσ1, hst]
    · simp [hσ3, hσ2, hσ1, Function.update_apply, hi]
  · funext r; by_cases h : r = 92
    · subst h; simp [hσ3, h92]
    · simp [hσ3, hσ2, hσ1, Function.update_apply, h]
  · rfl

end NearCubicWires.WireExponent3_5.SelectionMachine.Cos
