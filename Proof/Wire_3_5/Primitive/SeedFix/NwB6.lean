import Proof.Wire_3_5.Primitive.SeedFix.NwB5
import Proof.Wire_3_5.Primitive.SeedFix.NwBT

/-! # NW phase (b), part 6: the value `V = #primes·2^{sb}·Q` in a register

From `|𝒢|`, `cut`, `#primes`, `Σp` (registers `440 … 443`), `2^{sb}` (`421`), `n` (`dN`) and `k_h` (`sKH`):
`q = 2|𝒢|·cut + 1`, `I = |𝒢|·Σp·2^{sb}·q² + 1`, `B = I·8192·n²`, `e = ⌊(5k_h + 3)/4⌋`, `Q = 2^e·B` (the THR sample
count, `ThrCap.thrQ_link`, P3:2987-3000) and `V = Q·2^{sb}·#primes` into `rA` (**`vArith_spec`**), every register
outside the arithmetic's block kept.

Paper quantity of the main type: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` (P3:3044-3048). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec NearCubicWires.WireExponent3_5.UnionMachine

def rG : Fin LNR := ⟨440, by decide⟩
def rCU : Fin LNR := ⟨441, by decide⟩
def rNP : Fin LNR := ⟨442, by decide⟩
def rPS : Fin LNR := ⟨443, by decide⟩
def rQq : Fin LNR := ⟨456, by decide⟩
def rBb : Fin LNR := ⟨457, by decide⟩
def rE2 : Fin LNR := ⟨458, by decide⟩
def rP2 : Fin LNR := ⟨459, by decide⟩
def rSB : Fin LNR := ⟨421, by decide⟩

/-- The division block `(dividend, divisor, quotient, …)`. -/
def D9 : Fin 9 ↪ Fin LNR := ⟨![rA, rMm, rE2, ⟨470, by decide⟩, ⟨471, by decide⟩, ⟨472, by decide⟩, ⟨473, by decide⟩,
  ⟨474, by decide⟩, ⟨475, by decide⟩], by decide⟩
/-- The power block `(e, 2^e, t, w)`. -/
def P4 : Fin 4 ↪ Fin LNR := ⟨![rE2, rP2, ⟨476, by decide⟩, ⟨477, by decide⟩], by decide⟩

variable (cap : ℕ) (x : ℕ)

/-- `q = 2|𝒢|·cut + 1` into `rQq`. -/
def vQW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR rG rA rTm) (.seq (mulR x rCU) (.seq (ParseNat.dbl rA rTm) (.seq (.inc rA)
  (WM.move rA rQq))))

/-- `B = (|𝒢|·Σp·2^{sb}·q² + 1)·8192·n²` into `rBb`. -/
def vIW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR rG rA rTm) (.seq (mulR x rPS) (.seq (mulR x rSB) (.seq (mulR x rQq) (.seq (mulR x rQq)
  (.seq (.inc rA) (.seq (mulC x 8192) (.seq (mulR x dN) (.seq (mulR x dN) (WM.move rA rBb)))))))))

/-- `e = ⌊(5k_h + 3)/4⌋` into `rE2` and `2^e` into `rP2`. -/
def vEW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR sKH rA rTm) (.seq (mulC x 5) (.seq (StarNums.incN rA 3)
  (.seq (StarNums.incN rMm 4) (.seq (UnaryArith.divW D9) (.seq (WM.clear rA) (.seq (WM.clear rMm)
  (UnaryArith.pow2W P4)))))))

/-- `V = 2^e·B·2^{sb}·#primes` into `rA`. -/
def vVW : WM (LNS x) LNR :=
  .seq (FinalPass.Hash4.wcopyR rP2 rA rTm) (.seq (mulR x rBb) (.seq (mulR x rSB) (mulR x rNP)))

/-- **The value's program.** -/
def vArithW : WM (LNS x) LNR := .seq (vQW x) (.seq (vIW x) (.seq (vEW x) (vVW x)))

/-- Register bookkeeping: `setv` chains at the literal registers. -/
local macro "vsimp" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := {decide := true}) [WState.setv_val, Function.update_apply, $hs,*])

/-- The arithmetic's six written registers and the frame. -/
structure St (σ σ' : WState (LNS x) LNR) (a m q b e p : ℕ) : Prop where
  hA : σ'.val rA = a
  hM : σ'.val rMm = m
  hQ : σ'.val rQq = q
  hB : σ'.val rBb = b
  hE : σ'.val rE2 = e
  hP : σ'.val rP2 = p
  fr : ∀ r, r ≠ rA → r ≠ rMm → r ≠ rQq → r ≠ rBb → r ≠ rE2 → r ≠ rP2 → σ'.val r = σ.val r
  st : σ'.st = σ.st
  sh : σ'.sh = σ.sh
  cell : σ'.cell = σ.cell

section StL
variable {x} {σ σ' : WState (LNS x) LNR} {a m q b e p : ℕ}

theorem St.setA (h : St x σ σ' a m q b e p) (a' : ℕ) : St x σ (σ'.setv rA a') a' m q b e p :=
  ⟨by vsimp [], by vsimp [h.hM], by vsimp [h.hQ], by vsimp [h.hB], by vsimp [h.hE], by vsimp [h.hP],
    fun r h1 h2 h3 h4 h5 h6 => by simp [Function.update_apply, h1]; exact h.fr r h1 h2 h3 h4 h5 h6, h.st, h.sh, h.cell⟩
theorem St.setM (h : St x σ σ' a m q b e p) (m' : ℕ) : St x σ (σ'.setv rMm m') a m' q b e p :=
  ⟨by vsimp [h.hA], by vsimp [], by vsimp [h.hQ], by vsimp [h.hB], by vsimp [h.hE], by vsimp [h.hP],
    fun r h1 h2 h3 h4 h5 h6 => by simp [Function.update_apply, h2]; exact h.fr r h1 h2 h3 h4 h5 h6, h.st, h.sh, h.cell⟩
theorem St.setQ (h : St x σ σ' a m q b e p) (q' : ℕ) : St x σ (σ'.setv rQq q') a m q' b e p :=
  ⟨by vsimp [h.hA], by vsimp [h.hM], by vsimp [], by vsimp [h.hB], by vsimp [h.hE], by vsimp [h.hP],
    fun r h1 h2 h3 h4 h5 h6 => by simp [Function.update_apply, h3]; exact h.fr r h1 h2 h3 h4 h5 h6, h.st, h.sh, h.cell⟩
theorem St.setB (h : St x σ σ' a m q b e p) (b' : ℕ) : St x σ (σ'.setv rBb b') a m q b' e p :=
  ⟨by vsimp [h.hA], by vsimp [h.hM], by vsimp [h.hQ], by vsimp [], by vsimp [h.hE], by vsimp [h.hP],
    fun r h1 h2 h3 h4 h5 h6 => by simp [Function.update_apply, h4]; exact h.fr r h1 h2 h3 h4 h5 h6, h.st, h.sh, h.cell⟩
theorem St.setE (h : St x σ σ' a m q b e p) (e' : ℕ) : St x σ (σ'.setv rE2 e') a m q b e' p :=
  ⟨by vsimp [h.hA], by vsimp [h.hM], by vsimp [h.hQ], by vsimp [h.hB], by vsimp [], by vsimp [h.hP],
    fun r h1 h2 h3 h4 h5 h6 => by simp [Function.update_apply, h5]; exact h.fr r h1 h2 h3 h4 h5 h6, h.st, h.sh, h.cell⟩
theorem St.setP (h : St x σ σ' a m q b e p) (p' : ℕ) : St x σ (σ'.setv rP2 p') a m q b e p' :=
  ⟨by vsimp [h.hA], by vsimp [h.hM], by vsimp [h.hQ], by vsimp [h.hB], by vsimp [h.hE], by vsimp [],
    fun r h1 h2 h3 h4 h5 h6 => by simp [Function.update_apply, h6]; exact h.fr r h1 h2 h3 h4 h5 h6, h.st, h.sh, h.cell⟩

end StL

/-- The arithmetic's scratch at `0`. -/
structure Z0 (σ : WState (LNS x) LNR) : Prop where
  t : σ.val rT6 = 0
  u : σ.val rU6 = 0
  w : σ.val rW6 = 0
  v : σ.val rV6 = 0
  tm : σ.val rTm = 0
  z : ∀ r : Fin LNR, 470 ≤ r.val → r.val ≤ 477 → σ.val r = 0

section StM
variable {x} {σ0 σ : WState (LNS x) LNR} {a m q b e p : ℕ}

theorem St.get (h : St x σ0 σ a m q b e p) (r : Fin LNR)
    (hr : r ≠ rA ∧ r ≠ rMm ∧ r ≠ rQq ∧ r ≠ rBb ∧ r ≠ rE2 ∧ r ≠ rP2) : σ.val r = σ0.val r :=
  h.fr r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2

theorem St.mz (h : St x σ0 σ a 0 q b e p) (hz : Z0 x σ0) : MZ x σ :=
  ⟨h.hM, by rw [h.get rT6 (by decide)]; exact hz.t, by rw [h.get rU6 (by decide)]; exact hz.u,
    by rw [h.get rW6 (by decide)]; exact hz.w, by rw [h.get rV6 (by decide)]; exact hz.v,
    by rw [h.get rTm (by decide)]; exact hz.tm⟩

theorem St.zx (h : St x σ0 σ a m q b e p) (hz : Z0 x σ0) (r : Fin LNR) (h1 : 470 ≤ r.val) (h2 : r.val ≤ 477) :
    σ.val r = 0 := by
  have hne : ∀ s : Fin LNR, s.val < 470 → r ≠ s := fun s hs c => by rw [c] at h1; omega
  rw [h.fr r (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide))
    (hne _ (by decide))]
  exact hz.z r h1 h2

theorem St.init (hA : σ.val rA = 0) (hM : σ.val rMm = 0) (hQ : σ.val rQq = 0) (hB : σ.val rBb = 0)
    (hE : σ.val rE2 = 0) (hP : σ.val rP2 = 0) : St x σ σ 0 0 0 0 0 0 :=
  ⟨hA, hM, hQ, hB, hE, hP, fun _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩

end StM

theorem m3 : 64 * (cap + 1) * (cap + 1) + 2 * UnaryPow.sq cap ≤ 3 * UnaryPow.sq cap := by
  unfold UnaryPow.sq; nlinarith

theorem vQ_spec (σ0 σ : WState (LNS x) LNR) (hz : Z0 x σ0) (b e p : ℕ) (h : St x σ0 σ 0 0 0 b e p) (g c : ℕ)
    (hg : σ0.val rG = g) (hc : σ0.val rCU = c) (hgc : g ≤ cap) (hcc : c ≤ cap) (hq : 2 * (g * c) + 1 ≤ cap) :
    ∃ σ' k, WExec cap (vQW x) σ σ' k ∧ k ≤ 6 * UnaryPow.sq cap + 20 ∧
      St x σ0 σ' 0 0 (2 * (g * c) + 1) b e p := by
  have hs := UnaryPow.lin_le_sq cap
  have hm := m3 cap
  have e1 := SparseNum.copy1 cap rG rA rTm (by decide) (by decide) (by decide) g σ
    (by rw [h.get rG (by decide)]; exact hg) h.hA (by rw [h.get rTm (by decide)]; exact hz.tm) hgc
  have h1 := h.setA g
  obtain ⟨k2, e2, c2⟩ := mulR_spec cap x rCU (by decide) (by decide) (by decide) _ g c h1.hA
    (by rw [h1.get rCU (by decide)]; exact hc) (h1.mz hz) (by omega) hgc hcc
  have h2 := h1.setA (g * c)
  have e3 := FiltNum.dbl1 cap rA rTm (by decide) (g * c) _ h2.hA (by rw [h2.get rTm (by decide)]; exact hz.tm)
    (by omega)
  have h3 := h2.setA (2 * (g * c))
  have e4 := WExec.inc (cap := cap) rA _ (by rw [h3.hA]; omega)
  rw [h3.hA] at e4
  have h4 := h3.setA (2 * (g * c) + 1)
  have e5 := wmove_spec cap rA rQq (by decide) (2 * (g * c) + 1) _ h4.hA (by rw [h4.hA]; omega)
    (by rw [h4.hA, h4.hQ]; omega)
  rw [h4.hA, h4.hQ, Nat.zero_add] at e5
  exact ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), by omega, (h4.setA 0).setQ _⟩

theorem vI_spec (σ0 σ : WState (LNS x) LNR) (hz : Z0 x σ0) (q e p : ℕ) (h : St x σ0 σ 0 0 q 0 e p)
    (g ps sb n : ℕ) (hg : σ0.val rG = g) (hps : σ0.val rPS = ps) (hsb : σ0.val rSB = sb) (hn : σ0.val dN = n)
    (hgc : g ≤ cap) (hpc : ps ≤ cap) (hsc : sb ≤ cap) (hqc : q ≤ cap) (hsb1 : 1 ≤ sb) (hq1 : 1 ≤ q) (hn1 : 1 ≤ n)
    (hB : (g * ps * sb * q * q + 1) * 8192 * n * n ≤ cap) :
    ∃ σ' k, WExec cap (vIW x) σ σ' k ∧ k ≤ 23 * UnaryPow.sq cap + 32820 ∧
      St x σ0 σ' 0 0 q ((g * ps * sb * q * q + 1) * 8192 * n * n) e p := by
  have hs := UnaryPow.lin_le_sq cap
  have hm := m3 cap
  have f1 : g * ps ≤ g * ps * sb := Nat.le_mul_of_pos_right _ hsb1
  have f2 : g * ps * sb ≤ g * ps * sb * q := Nat.le_mul_of_pos_right _ hq1
  have f3 : g * ps * sb * q ≤ g * ps * sb * q * q := Nat.le_mul_of_pos_right _ hq1
  have f4 : g * ps * sb * q * q + 1 ≤ (g * ps * sb * q * q + 1) * 8192 := Nat.le_mul_of_pos_right _ (by norm_num)
  have f5 : (g * ps * sb * q * q + 1) * 8192 ≤ (g * ps * sb * q * q + 1) * 8192 * n := Nat.le_mul_of_pos_right _ hn1
  have f6 : (g * ps * sb * q * q + 1) * 8192 * n ≤ (g * ps * sb * q * q + 1) * 8192 * n * n :=
    Nat.le_mul_of_pos_right _ hn1
  have f7 : n ≤ (g * ps * sb * q * q + 1) * 8192 * n := Nat.le_mul_of_pos_left _ (by positivity)
  have f8 : 8192 ≤ (g * ps * sb * q * q + 1) * 8192 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have e1 := SparseNum.copy1 cap rG rA rTm (by decide) (by decide) (by decide) g σ
    (by rw [h.get rG (by decide)]; exact hg) h.hA (by rw [h.get rTm (by decide)]; exact hz.tm) hgc
  have h1 := h.setA g
  obtain ⟨k2, e2, c2⟩ := mulR_spec cap x rPS (by decide) (by decide) (by decide) _ g ps h1.hA
    (by rw [h1.get rPS (by decide)]; exact hps) (h1.mz hz) (by omega) hgc hpc
  have h2 := h1.setA (g * ps)
  obtain ⟨k3, e3, c3⟩ := mulR_spec cap x rSB (by decide) (by decide) (by decide) _ (g * ps) sb h2.hA
    (by rw [h2.get rSB (by decide)]; exact hsb) (h2.mz hz) (by omega) (by omega) hsc
  have h3 := h2.setA (g * ps * sb)
  obtain ⟨k4, e4, c4⟩ := mulR_spec cap x rQq (by decide) (by decide) (by decide) _ (g * ps * sb) q h3.hA h3.hQ
    (h3.mz hz) (by omega) (by omega) hqc
  have h4 := h3.setA (g * ps * sb * q)
  obtain ⟨k5, e5, c5⟩ := mulR_spec cap x rQq (by decide) (by decide) (by decide) _ (g * ps * sb * q) q h4.hA h4.hQ
    (h4.mz hz) (by omega) (by omega) hqc
  have h5 := h4.setA (g * ps * sb * q * q)
  have e6 := WExec.inc (cap := cap) rA _ (by rw [h5.hA]; omega)
  rw [h5.hA] at e6
  have h6 := h5.setA (g * ps * sb * q * q + 1)
  obtain ⟨k7, e7, c7⟩ := mulC_spec cap x 8192 _ (g * ps * sb * q * q + 1) h6.hA (h6.mz hz) (by omega) (by omega)
    (by omega)
  have h7 := h6.setA ((g * ps * sb * q * q + 1) * 8192)
  obtain ⟨k8, e8, c8⟩ := mulR_spec cap x dN (by decide) (by decide) (by decide) _ _ n h7.hA
    (by rw [h7.get dN (by decide)]; exact hn) (h7.mz hz) (by omega) (by omega) (by omega)
  have h8 := h7.setA ((g * ps * sb * q * q + 1) * 8192 * n)
  obtain ⟨k9, e9, c9⟩ := mulR_spec cap x dN (by decide) (by decide) (by decide) _ _ n h8.hA
    (by rw [h8.get dN (by decide)]; exact hn) (h8.mz hz) (by omega) (by omega) (by omega)
  have h9 := h8.setA ((g * ps * sb * q * q + 1) * 8192 * n * n)
  have e10 := wmove_spec cap rA rBb (by decide) _ _ h9.hA (by rw [h9.hA]; omega) (by rw [h9.hA, h9.hB]; omega)
  rw [h9.hA, h9.hB, Nat.zero_add] at e10
  exact ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 (WExec.seq e7
    (WExec.seq e8 (WExec.seq e9 e10)))))))), by omega, (h9.setA 0).setB _⟩

theorem vE_spec (σ0 σ : WState (LNS x) LNR) (hz : Z0 x σ0) (q b : ℕ) (h : St x σ0 σ 0 0 q b 0 0) (kh : ℕ)
    (hk : σ0.val sKH = kh) (hkc : kh * 5 + 3 ≤ cap) (h8 : 8 ≤ cap) (h2 : 2 ^ ((kh * 5 + 3) / 4 + 1) ≤ cap) :
    ∃ σ' k, WExec cap (vEW x) σ σ' k ∧ k ≤ 7 * UnaryPow.sq cap + 200 ∧
      St x σ0 σ' 0 0 q b ((kh * 5 + 3) / 4) (2 ^ ((kh * 5 + 3) / 4)) := by
  have hs := UnaryPow.lin_le_sq cap
  have hm := m3 cap
  have e1 := SparseNum.copy1 cap sKH rA rTm (by decide) (by decide) (by decide) kh σ
    (by rw [h.get sKH (by decide)]; exact hk) h.hA (by rw [h.get rTm (by decide)]; exact hz.tm) (by omega)
  have h1 := h.setA kh
  obtain ⟨k2, e2, c2⟩ := mulC_spec cap x 5 _ kh h1.hA (h1.mz hz) (by omega) (by omega) (by omega)
  have h2' := h1.setA (kh * 5)
  have e3 := StarNums.incN_spec cap rA 3 _ (by rw [h2'.hA]; omega)
  rw [h2'.hA] at e3
  have h3 := h2'.setA (kh * 5 + 3)
  have e4 := StarNums.incN_spec cap rMm 4 _ (by rw [h3.hM]; omega)
  rw [h3.hM, Nat.zero_add] at e4
  have h4 := h3.setM 4
  have e5 := UnaryArith.divW_spec cap D9 _ (by rw [show D9 1 = rMm from rfl, h4.hM]; norm_num)
    (h4.zx hz _ (by decide) (by decide)) (h4.zx hz _ (by decide) (by decide)) (h4.zx hz _ (by decide) (by decide))
    (h4.zx hz _ (by decide) (by decide)) (h4.zx hz _ (by decide) (by decide))
    (by rw [show D9 0 = rA from rfl, h4.hA]; exact hkc) (by rw [show D9 1 = rMm from rfl, h4.hM]; omega)
    (by rw [show D9 2 = rE2 from rfl, show D9 0 = rA from rfl, h4.hE, h4.hA]; omega) (by omega)
  rw [show D9 0 = rA from rfl, show D9 1 = rMm from rfl, show D9 2 = rE2 from rfl, h4.hA, h4.hM, h4.hE,
    Nat.zero_add] at e5
  have h5 := (h4.setA ((kh * 5 + 3) % 4)).setE ((kh * 5 + 3) / 4)
  have e6 := wclear_spec cap rA ((kh * 5 + 3) % 4) _ h5.hA (by rw [h5.hA]; omega)
  have h6 := h5.setA 0
  have e7 := wclear_spec cap rMm 4 _ h6.hM (by rw [h6.hM]; omega)
  have h7 := h6.setM 0
  have e8 := UnaryArith.pow2W_spec cap P4 _ h7.hP (h7.zx hz _ (by decide) (by decide))
    (h7.zx hz _ (by decide) (by decide)) (by rw [show P4 0 = rE2 from rfl, h7.hE]; exact h2)
  rw [show P4 0 = rE2 from rfl, show P4 1 = rP2 from rfl, h7.hE] at e8
  have h8' := h7.setP (2 ^ ((kh * 5 + 3) / 4))
  have hel : (kh * 5 + 3) / 4 < 2 ^ ((kh * 5 + 3) / 4) := Nat.lt_two_pow_self
  have hE2 : 2 * 2 ^ ((kh * 5 + 3) / 4) ≤ cap := by rw [pow_succ] at h2; omega
  have hpw : (kh * 5 + 3) / 4 * (18 * 2 ^ ((kh * 5 + 3) / 4) + 7) + 18 * ((kh * 5 + 3) / 4) + 20 ≤ UnaryPow.sq cap := by
    have hm1 : (kh * 5 + 3) / 4 * (18 * 2 ^ ((kh * 5 + 3) / 4) + 7) ≤ cap * (18 * cap + 7) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hm2 : cap * (18 * cap + 7) + 18 * cap + 20 ≤ UnaryPow.sq cap := by unfold UnaryPow.sq; nlinarith
    omega
  have hdv : (kh * 5 + 3 + 2) * (90 * (kh * 5 + 3) + 90 * 4 + 60) ≤ 2 * UnaryPow.sq cap := by
    have hm1 : (kh * 5 + 3 + 2) * (90 * (kh * 5 + 3) + 90 * 4 + 60) ≤ (cap + 2) * (90 * cap + 420) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hm2 : (cap + 2) * (90 * cap + 420) ≤ 2 * UnaryPow.sq cap := by unfold UnaryPow.sq; nlinarith
    exact le_trans hm1 hm2
  have E7 := WExec.seq e7 e8
  have E6 := WExec.seq e6 E7
  have E5 := WExec.seq e5 E6
  have E4 := WExec.seq e4 E5
  have E3 := WExec.seq e3 E4
  have E2 := WExec.seq e2 E3
  have E1 := WExec.seq e1 E2
  refine ⟨_, _, E1, ?_, h8'⟩
  generalize (kh * 5 + 3 + 2) * (90 * (kh * 5 + 3) + 90 * 4 + 60) = D at hdv ⊢
  generalize (kh * 5 + 3) / 4 * (18 * 2 ^ ((kh * 5 + 3) / 4) + 7) = P at hpw ⊢
  omega

theorem vV_spec (σ0 σ : WState (LNS x) LNR) (hz : Z0 x σ0) (q b e p : ℕ) (h : St x σ0 σ 0 0 q b e p)
    (sb np : ℕ) (hsb : σ0.val rSB = sb) (hnp : σ0.val rNP = np) (hp1 : 1 ≤ p) (hb1 : 1 ≤ b) (hsb1 : 1 ≤ sb)
    (hnp1 : 1 ≤ np) (hV : p * b * sb * np ≤ cap) :
    ∃ σ' k, WExec cap (vVW x) σ σ' k ∧ k ≤ 10 * UnaryPow.sq cap + 10 ∧ St x σ0 σ' (p * b * sb * np) 0 q b e p := by
  have hm := m3 cap
  have f1 : p ≤ p * b := Nat.le_mul_of_pos_right _ hb1
  have f2 : p * b ≤ p * b * sb := Nat.le_mul_of_pos_right _ hsb1
  have f3 : p * b * sb ≤ p * b * sb * np := Nat.le_mul_of_pos_right _ hnp1
  have f4 : b ≤ p * b := Nat.le_mul_of_pos_left _ hp1
  have f5 : sb ≤ p * b * sb := Nat.le_mul_of_pos_left _ (Nat.mul_pos hp1 hb1)
  have f6 : np ≤ p * b * sb * np := Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos hp1 hb1) hsb1)
  have e1 := SparseNum.copy1 cap rP2 rA rTm (by decide) (by decide) (by decide) p σ h.hP h.hA
    (by rw [h.get rTm (by decide)]; exact hz.tm) (by omega)
  have h1 := h.setA p
  obtain ⟨k2, e2, c2⟩ := mulR_spec cap x rBb (by decide) (by decide) (by decide) _ p b h1.hA h1.hB (h1.mz hz)
    (by omega) (by omega) (by omega)
  have h2 := h1.setA (p * b)
  obtain ⟨k3, e3, c3⟩ := mulR_spec cap x rSB (by decide) (by decide) (by decide) _ (p * b) sb h2.hA
    (by rw [h2.get rSB (by decide)]; exact hsb) (h2.mz hz) (by omega) (by omega) (by omega)
  have h3 := h2.setA (p * b * sb)
  obtain ⟨k4, e4, c4⟩ := mulR_spec cap x rNP (by decide) (by decide) (by decide) _ (p * b * sb) np h3.hA
    (by rw [h3.get rNP (by decide)]; exact hnp) (h3.mz hz) (by omega) (by omega) (by omega)
  exact ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega, h3.setA _⟩

/-- **The value in `rA`**, the other five written registers `(0, q, B, e, 2^e)`, every other register kept. -/
theorem vArith_spec (σ : WState (LNS x) LNR) (hz : Z0 x σ) (h0 : St x σ σ 0 0 0 0 0 0)
    (g c ps sb np n kh : ℕ) (hg : σ.val rG = g) (hc : σ.val rCU = c) (hps : σ.val rPS = ps) (hsb : σ.val rSB = sb)
    (hnp : σ.val rNP = np) (hn : σ.val dN = n) (hk : σ.val sKH = kh)
    (hgc : g ≤ cap) (hcc : c ≤ cap) (hpc : ps ≤ cap) (hqc : 2 * (g * c) + 1 ≤ cap)
    (hsb1 : 1 ≤ sb) (hnp1 : 1 ≤ np) (hn1 : 1 ≤ n) (hV : vVal g c ps sb np n kh ≤ cap) :
    ∃ σ' k, WExec cap (vArithW x) σ σ' k ∧ k ≤ 50 * UnaryPow.sq cap + 40000 ∧
      St x σ σ' (vVal g c ps sb np n kh) 0 (2 * (g * c) + 1)
        ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n) ((kh * 5 + 3) / 4)
        (2 ^ ((kh * 5 + 3) / 4)) := by
  unfold vVal at hV
  have hE1 : 1 ≤ 2 ^ ((kh * 5 + 3) / 4) := Nat.one_le_two_pow
  have hI : 8192 ≤ (g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n := by
    have := Nat.le_mul_of_pos_right ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n) hn1
    have := Nat.le_mul_of_pos_right ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192) hn1
    have := Nat.le_mul_of_pos_left 8192 (Nat.succ_pos (g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1)))
    omega
  have hBV := Nat.le_mul_of_pos_left ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n) hE1
  have hV1 := Nat.le_mul_of_pos_right (2 ^ ((kh * 5 + 3) / 4) *
    ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n)) hsb1
  have hV2 := Nat.le_mul_of_pos_right (2 ^ ((kh * 5 + 3) / 4) *
    ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n) * sb) hnp1
  have hEB : 2 ^ ((kh * 5 + 3) / 4) * 8192 ≤ 2 ^ ((kh * 5 + 3) / 4) *
      ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n) := Nat.mul_le_mul_left _ hI
  have hsbV : sb ≤ 2 ^ ((kh * 5 + 3) / 4) *
      ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n) * sb :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hel : (kh * 5 + 3) / 4 < 2 ^ ((kh * 5 + 3) / 4) := Nat.lt_two_pow_self
  have hkc : kh * 5 + 3 ≤ cap := by omega
  have h2e : 2 ^ ((kh * 5 + 3) / 4 + 1) ≤ cap := by rw [pow_succ]; omega
  obtain ⟨σ1, k1, e1, c1, h1⟩ := vQ_spec cap x σ σ hz 0 0 0 h0 g c hg hc hgc hcc hqc
  obtain ⟨σ2, k2, e2, c2, h2⟩ := vI_spec cap x σ σ1 hz _ 0 0 h1 g ps sb n hg hps hsb hn hgc hpc (by omega) hqc hsb1
    (by omega) hn1 (by omega)
  obtain ⟨σ3, k3, e3, c3, h3⟩ := vE_spec cap x σ σ2 hz _ _ h2 kh hk hkc (by omega) h2e
  obtain ⟨σ4, k4, e4, c4, h4⟩ := vV_spec cap x σ σ3 hz _ _ _ _ h3 sb np hsb hnp hE1 (by omega) hsb1 hnp1 hV
  exact ⟨σ4, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega, h4⟩

end NearCubicWires.WireExponent3_5.PrimT.NwB
