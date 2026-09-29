import Proof.Wire_3_5.Primitive.SeedFix.W6F

/-! # W6, part 7: register runs and `K = 8(|𝒢|+1)n^D`

P3:2552-2557 ("Given a fixed `D>0`, … `≤ n^{-D}`": `K = 8(|𝒢|+1)n^D`). The numbers machine's arithmetic touches only
registers; **`RegRun cap P f g n`** states that `P` takes every state with registers `f` to the same streams, heads
and cell with registers `g` in `n` steps, so register programs compose by `RegRun.seq`. PA's verified unary
operations become register runs at the uniform cost **`opU cap = 20·sq cap`** (`wcopy_rr`, `inc_rr`, `mulAdd_rr`,
`sub_rr`, `addTo_rr`, `gt_rr`, `div_rr`, `incN_rr`, `clear_rr`, `clog_rr`; `pow_rr` at `(e+1)·opU`), and:
* **`kW`** / **`kW_rr`**: `rK := 8(g+1)n^D` from `rN = n`, `rNG = g`, scratch `0 … 9` at `0` and restored.

Paper quantity of the main type: `K`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

def rNG : Fin 80 := 53
def rE : Fin 80 := 54
def rK : Fin 80 := 55
def rCut : Fin 80 := 56
def rTau : Fin 80 := 57

/-! ## Register runs -/

/-- The uniform cost bound of one register operation. -/
def opU : ℕ := 20 * UnaryPow.sq cap

theorem lin_le_opU : 40 * cap + 40 ≤ opU cap := by
  have := UnaryPow.lin_le_sq cap; unfold opU; omega

theorem quad_le_opU (x y : ℕ) (hx : x ≤ cap) (hy : y ≤ cap) : (x + 2) * (90 * x + 90 * y + 60) ≤ opU cap := by
  have h1 : (x + 2) * (90 * x + 90 * y + 60) ≤ (cap + 2) * (200 * (cap + 2)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (cap + 2) * (200 * (cap + 2)) = UnaryPow.sq cap := by unfold UnaryPow.sq; ring
  unfold opU; omega

/-- **A register run**: `P` takes every state with registers `f` to the same streams, heads and cell with registers
`g`, in `n` steps. -/
def RegRun (P : WP) (f g : Fin 80 → ℕ) (n : ℕ) : Prop :=
  ∀ σ : WL, σ.val = f → WExec cap P σ ⟨σ.sh, σ.st, g, σ.cell⟩ n

theorem RegRun.seq {P Q : WP} {f g h : Fin 80 → ℕ} {n m : ℕ} (hP : RegRun cap P f g n) (hQ : RegRun cap Q g h m) :
    RegRun cap (.seq P Q) f h (n + 1 + m) := fun σ hσ =>
  WExec.seq (hP σ hσ) (hQ ⟨σ.sh, σ.st, g, σ.cell⟩ rfl)

theorem RegRun.mono {P : WP} {f g : Fin 80 → ℕ} {n m : ℕ} (hP : RegRun cap P f g n) (h : n ≤ m) :
    RegRun cap P f g m := fun σ hσ => WExec.mono (hP σ hσ) h

theorem RegRun.congr {P : WP} {f g g' : Fin 80 → ℕ} {n : ℕ} (hP : RegRun cap P f g n) (h : g = g') :
    RegRun cap P f g' n := h ▸ hP

theorem setv_mk (σ : WL) (r : Fin 80) (x : ℕ) :
    σ.setv r x = ⟨σ.sh, σ.st, Function.update σ.val r x, σ.cell⟩ := rfl

theorem wcopy_rr (a b t : Fin 80) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (f : Fin 80 → ℕ) (v : ℕ) (hv : f a = v)
    (hb : f b = 0) (ht : f t = 0) (ha : f a ≤ cap) :
    RegRun cap (wcopyR a b t) f (Function.update f b v) (opU cap) := fun σ hσ => by
  subst hv
  have h := wcopyR_spec cap a b t hab hat hbt σ (by rw [hσ]; exact hb) (by rw [hσ]; exact ht) (by rw [hσ]; exact ha)
  rw [setv_mk, hσ] at h
  exact WExec.mono h (by have := lin_le_opU cap; omega)

theorem inc_rr (r : Fin 80) (f : Fin 80 → ℕ) (v : ℕ) (hv : f r + 1 = v) (h : f r < cap) :
    RegRun cap (.inc r) f (Function.update f r v) (opU cap) := fun σ hσ => by
  subst hv
  have e := WExec.inc (cap := cap) r σ (by rw [hσ]; exact h)
  rw [setv_mk, hσ] at e
  exact WExec.mono e (by have := lin_le_opU cap; omega)

theorem mulAdd_rr (R : Fin 5 ↪ Fin 80) (a b c t w : Fin 80) (h0 : R 0 = a) (h1 : R 1 = b) (h2 : R 2 = c)
    (h3 : R 3 = t) (h4 : R 4 = w) (f : Fin 80 → ℕ) (v : ℕ) (hv : f c + f a * f b = v) (ht : f t = 0) (hw : f w = 0)
    (hb : f b ≤ cap) (hc : f c + f a * f b ≤ cap) (ha : f a ≤ cap) :
    RegRun cap (UnaryArith.mulAddW R) f (Function.update f c v) (opU cap) := by
  subst h0 h1 h2 h3 h4 hv
  intro σ hσ
  have h := UnaryArith.mulAddW_spec cap R σ (by rw [hσ]; exact ht) (by rw [hσ]; exact hw) (by rw [hσ]; exact hb)
    (by rw [hσ]; exact hc) (by rw [hσ]; exact ha)
  rw [setv_mk, hσ] at h
  refine WExec.mono h ?_
  have hq := quad_le_opU cap (f (R 0)) (f (R 1)) ha hb
  nlinarith [Nat.zero_le (f (R 0) * f (R 1)), Nat.zero_le (f (R 0) * f (R 0))]

theorem sub_rr (R : Fin 4 ↪ Fin 80) (a b t w : Fin 80) (h0 : R 0 = a) (h1 : R 1 = b) (h2 : R 2 = t)
    (h3 : R 3 = w) (f : Fin 80 → ℕ) (v : ℕ) (hv : f a - f b = v) (ht : f t = 0) (hw : f w = 0) (ha : f a ≤ cap)
    (hb : f b ≤ cap) :
    RegRun cap (UnaryArith.subW R) f (Function.update f a v) (opU cap) := by
  subst h0 h1 h2 h3 hv
  intro σ hσ
  have h := UnaryArith.subW_spec cap R σ (by rw [hσ]; exact ht) (by rw [hσ]; exact hw) (by rw [hσ]; exact ha)
    (by rw [hσ]; exact hb)
  rw [setv_mk, hσ] at h
  exact WExec.mono h (by have := lin_le_opU cap; omega)

theorem addTo_rr (p q t : Fin 80) (hpq : p ≠ q) (hpt : p ≠ t) (hqt : q ≠ t) (f : Fin 80 → ℕ) (v : ℕ)
    (hv : f q + f p = v) (ht : f t = 0) (hp : f p ≤ cap) (hq : f q + f p ≤ cap) :
    RegRun cap (ParseNat.addTo p q t) f (Function.update f q v) (opU cap) := fun σ hσ => by
  subst hv
  have h := ParseNat.addTo_spec cap p q t hpq hpt hqt σ (by rw [hσ]; exact ht) (by rw [hσ]; exact hp)
    (by rw [hσ]; exact hq)
  rw [setv_mk, hσ] at h
  exact WExec.mono h (by have := lin_le_opU cap; omega)

theorem div_rr (R : Fin 9 ↪ Fin 80) (a b q go g t u w : Fin 80) (h0 : R 0 = a) (h1 : R 1 = b) (h2 : R 2 = q)
    (h3 : R 3 = go) (h4 : R 4 = g) (h5 : R 5 = t) (h6 : R 6 = u) (h7 : R 7 = w) (f : Fin 80 → ℕ) (v x : ℕ)
    (hv : f a % f b = v) (hx : f q + f a / f b = x)
    (hb1 : 1 ≤ f b) (hgo : f go = 0) (hg : f g = 0) (ht : f t = 0) (hu : f u = 0) (hw : f w = 0) (ha : f a ≤ cap)
    (hb : f b ≤ cap) (hq : f q + f a ≤ cap) (hcap : 1 ≤ cap) :
    RegRun cap (UnaryArith.divW R) f (Function.update (Function.update f a v) q x) (opU cap) := by
  subst h0 h1 h2 h3 h4 h5 h6 h7 hv hx
  intro σ hσ
  have h := UnaryArith.divW_spec cap R σ (by rw [hσ]; exact hb1) (by rw [hσ]; exact hgo) (by rw [hσ]; exact hg)
    (by rw [hσ]; exact ht) (by rw [hσ]; exact hu) (by rw [hσ]; exact hw) (by rw [hσ]; exact ha) (by rw [hσ]; exact hb)
    (by rw [hσ]; exact hq) hcap
  rw [setv_mk, setv_mk] at h
  simp only [WState.setv_val, hσ] at h
  exact WExec.mono h (quad_le_opU cap _ _ ha hb)

theorem incN_rr (r : Fin 80) (c : ℕ) (f : Fin 80 → ℕ) (v : ℕ) (hv : f r + c = v) (h : f r + c ≤ cap) :
    RegRun cap (StarNums.incN r c) f (Function.update f r v) (opU cap) := fun σ hσ => by
  subst hv
  have e := StarNums.incN_spec cap r c σ (by rw [hσ]; exact h)
  rw [setv_mk, hσ] at e
  exact WExec.mono e (by have := lin_le_opU cap; omega)

theorem clear_rr (r : Fin 80) (f : Fin 80 → ℕ) (h : f r ≤ cap) :
    RegRun cap (WM.clear r) f (Function.update f r 0) (opU cap) := fun σ hσ => by
  have e := wclear_spec cap r (f r) σ (by rw [hσ]) (by rw [hσ]; exact h)
  rw [setv_mk, hσ] at e
  exact WExec.mono e (by have := lin_le_opU cap; omega)

theorem clog_rr (S : Fin 10 ↪ Fin 80) (x o : Fin 80) (h0 : S 0 = x) (h1 : S 1 = o) (f : Fin 80 → ℕ) (v : ℕ)
    (hv : Nat.clog 2 (f x) = v) (hz : ∀ i : Fin 10, 1 ≤ i.val → f (S i) = 0) (hc : f x + 2 ≤ cap) :
    RegRun cap (SymQM.clogW S) f (Function.update f o v) (opU cap) := by
  subst h0 h1 hv
  intro σ hσ
  have h := SymQM.clogW_spec cap S σ (f (S 0)) (by rw [hσ]) (fun i hi => by rw [hσ]; exact hz i hi) hc
  rw [setv_mk, hσ] at h
  exact h

theorem pow_rr (R : Fin 5 ↪ Fin 80) (a o : Fin 80) (h0 : R 0 = a) (h1 : R 1 = o) (e : ℕ) (f : Fin 80 → ℕ) (v : ℕ)
    (hv : f a ^ e = v) (hz : ∀ i : Fin 5, 1 ≤ i.val → f (R i) = 0) (hc1 : 1 ≤ cap) (ha : f a ≤ cap)
    (hpow : ∀ k ≤ e, f a ^ k ≤ cap) :
    RegRun cap (UnaryPow.powConstW R e) f (Function.update f o v) ((e + 1) * opU cap) := by
  subst h0 h1 hv
  intro σ hσ
  have h := UnaryPow.powConstW_spec cap R e σ (by rw [hσ]; exact hz 1 (by decide)) (by rw [hσ]; exact hz 2 (by decide))
    (by rw [hσ]; exact hz 3 (by decide)) (by rw [hσ]; exact hz 4 (by decide)) hc1 (by rw [hσ]; exact ha)
    (by rw [hσ]; exact hpow)
  rw [setv_mk, hσ] at h
  exact WExec.mono h (Nat.mul_le_mul le_rfl (by unfold opU; omega))

/-! ## `K = 8(|𝒢|+1)n^D` -/

def Rp : Fin 5 ↪ Fin 80 := ⟨![48, 0, 1, 2, 3], by decide⟩
def Rm1 : Fin 5 ↪ Fin 80 := ⟨![4, 0, 6, 7, 8], by decide⟩
def Rm2 : Fin 5 ↪ Fin 80 := ⟨![9, 6, 55, 7, 8], by decide⟩

/-- `rK := 8(g+1)n^D`. -/
def kW (D : ℕ) : WP :=
  .seq (UnaryPow.powConstW Rp D) (.seq (wcopyR rNG 4 5) (.seq (.inc 4) (.seq (UnaryArith.mulAddW Rm1)
    (.seq (StarNums.incN 9 8) (.seq (UnaryArith.mulAddW Rm2) (.seq (WM.clear 0) (.seq (WM.clear 4)
      (.seq (WM.clear 6) (WM.clear 9)))))))))

theorem kW_rr (D : ℕ) (f : Fin 80 → ℕ) (n g : ℕ) (hn : f rN = n) (hg : f rNG = g)
    (hz : ∀ r : Fin 80, r.val < 10 → f r = 0) (hk : f rK = 0) (h1 : 1 ≤ cap)
    (hpow : ∀ k ≤ D, n ^ k ≤ cap) (hK : 8 * ((g + 1) * n ^ D) + 8 ≤ cap) (hn1 : n ≤ cap) (hg1 : g + 1 ≤ cap) :
    RegRun cap (kW D) f (Function.update f rK (8 * (g + 1) * n ^ D)) ((D + 1) * opU cap + 10 * opU cap) := by
  have hnD : n ^ D ≤ cap := hpow D le_rfl
  have hn' : f 48 = n := hn
  have hg' : f 53 = g := hg
  have hk' : f 55 = 0 := hk
  have z0 : f 0 = 0 := hz 0 (by decide)
  have z1 : f 1 = 0 := hz 1 (by decide)
  have z2 : f 2 = 0 := hz 2 (by decide)
  have z3 : f 3 = 0 := hz 3 (by decide)
  have z4 : f 4 = 0 := hz 4 (by decide)
  have z5 : f 5 = 0 := hz 5 (by decide)
  have z6 : f 6 = 0 := hz 6 (by decide)
  have z7 : f 7 = 0 := hz 7 (by decide)
  have z8 : f 8 = 0 := hz 8 (by decide)
  have z9 : f 9 = 0 := hz 9 (by decide)
  have hgn : (g + 1) * n ^ D ≤ cap := by nlinarith
  have c := (pow_rr cap Rp 48 0 rfl rfl D f (n ^ D) (by rw [hn']) (fun i hi => by
      fin_cases i
      · exact absurd hi (by decide)
      all_goals simp [Rp, z0, z1, z2, z3]) h1 (by rw [hn']; exact hn1) (by rw [hn']; exact hpow)).seq cap
    ((wcopy_rr cap 53 4 5 (by decide) (by decide) (by decide) _ g (by simp [Function.update_apply, hg'])
      (by simp [Function.update_apply, z4]) (by simp [Function.update_apply, z5])
      (by simp [Function.update_apply, hg']; omega)).seq cap
    ((inc_rr cap 4 _ (g + 1) (by simp) (by simp; omega)).seq cap
    ((mulAdd_rr cap Rm1 4 0 6 7 8 rfl rfl rfl rfl rfl _ ((g + 1) * n ^ D) (by simp [Function.update_apply, z6])
      (by simp [Function.update_apply, z7]) (by simp [Function.update_apply, z8])
      (by simp [Function.update_apply]; exact hnD) (by simp [Function.update_apply, z6]; exact hgn)
      (by simp [Function.update_apply]; omega)).seq cap
    ((incN_rr cap 9 8 _ 8 (by simp [Function.update_apply, z9]) (by simp [Function.update_apply, z9]; omega)).seq cap
    ((mulAdd_rr cap Rm2 9 6 55 7 8 rfl rfl rfl rfl rfl _ (8 * ((g + 1) * n ^ D))
      (by simp [Function.update_apply, hk'])
      (by simp [Function.update_apply, z7]) (by simp [Function.update_apply, z8])
      (by simp [Function.update_apply]; exact hgn) (by simp [Function.update_apply, hk']; omega)
      (by simp [Function.update_apply]; omega)).seq cap
    ((clear_rr cap 0 _ (by simp [Function.update_apply]; exact hnD)).seq cap
    ((clear_rr cap 4 _ (by simp [Function.update_apply]; omega)).seq cap
    ((clear_rr cap 6 _ (by simp [Function.update_apply]; exact hgn)).seq cap
    (clear_rr cap 9 _ (by simp [Function.update_apply]; omega))))))))))
  have hU := lin_le_opU cap
  refine (c.congr cap ?_).mono cap (by omega)
  funext r
  simp only [Function.update_apply]
  have hrK : (rK : Fin 80) = 55 := rfl
  rw [hrK]
  clear c hU hpow hK hgn hnD hn1 hg1 h1 hz
  split_ifs <;> (try simp_all) <;> ring

end NearCubicWires.WireExponent3_5.PrimT.W6
