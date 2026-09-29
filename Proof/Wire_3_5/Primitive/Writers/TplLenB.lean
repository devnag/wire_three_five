import Proof.Wire_3_5.Primitive.Writers.TplLenA

/-! # SWn item 6, part B: capacities and the first two parts

* `capI` (the inner capacity `10^9·(M+B+L+2)²`), **`caps`** (every capacity need of the three parts from `capI ≤ c`);
* **`p1_spec`** (`4096·B` into `W 2`), **`p2_spec`** (`S`, `J`, `M`, `L` into `W 0`, `W 1`, `W 25`, `W 26`).

Paper quantity of the main types: the stage-5 template word's parameters (`list:base`, P3:1384-1398, 1449-1477). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.TplLen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.CanonicalFourfoldRowProgram (natCeilSqrt)

/-- The inner capacity. -/
def capI (M B L : ℕ) : ℕ := 10 ^ 9 * (M + B + L + 2) ^ 2

/-- **Every capacity need of the three parts.** -/
theorem caps (M B L c : ℕ) (hc : capI M B L ≤ c) :
    B ≤ c ∧ M ≤ c ∧ L ≤ c ∧ B * 4096 + 4096 ≤ c ∧
    (64 ^ 2 * B + 2) * (64 ^ 2 * B + 2) + 64 ^ 2 * B + 10 ≤ c ∧
    LevelW.lvCap (natCeilSqrt (64 ^ 2 * B)) (⟨M, B⟩ : Lists.BaseListParams).J (⟨M, B⟩ : Lists.BaseListParams).J ≤ c ∧
    (FinalPass.SymParts.Tmpl.tplWord M (natCeilSqrt (64 ^ 2 * B)) (⟨M, B⟩ : Lists.BaseListParams).J L).length ≤ c ∧
    (⟨M, B⟩ : Lists.BaseListParams).J + 1 ≤ c ∧ natCeilSqrt (64 ^ 2 * B) ≤ c := by
  unfold capI at hc
  have Z1 : M + B + L + 2 ≤ (M + B + L + 2) ^ 2 := by nlinarith
  have hJ9 := J_le M B
  have hPJ := pow_J_le M B
  have hwl := tplWord_len_le M B L
  have hp : 2 ^ ((⟨M, B⟩ : Lists.BaseListParams).J / 3) ≤ 2 ^ (⟨M, B⟩ : Lists.BaseListParams).J :=
    Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
  have hS0 := LevelW.natCeilSqrt_le (64 ^ 2 * B)
  generalize hXd : 64 ^ 2 * B = X at hS0 hwl ⊢
  have hX4 : X = 4096 * B := by rw [← hXd]; norm_num
  have h1 : X + 2 ≤ 4096 * (M + B + L + 2) := by omega
  have h2 : (X + 2) * (X + 2) ≤ (4096 * (M + B + L + 2)) * (4096 * (M + B + L + 2)) := Nat.mul_le_mul h1 h1
  have h3 : (4096 * (M + B + L + 2)) * (4096 * (M + B + L + 2)) = 16777216 * (M + B + L + 2) ^ 2 := by ring
  unfold LevelW.lvCap
  generalize (M + B + L + 2) ^ 2 = Z2 at Z1 h3 hwl hc ⊢
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

section Parts
variable {ns nr : ℕ} (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RM RB RJ RL RT : Fin nr)

/-- **Part 1.** -/
theorem p1_spec (c : ℕ) (hWB : ∀ i, W i ≠ RB) (σ : WState ns nr) (B : ℕ) (hB : σ.val RB = B)
    (hz : ∀ i, σ.val (W i) = 0) (hBc : B ≤ c) (h4 : B * 4096 + 4096 ≤ c) :
    ∃ s n, WExec c (tplLenP1 W RB) σ s n ∧ n ≤ 5 * UnaryPow.sq c + 4 ∧ (∀ i : Fin 30, i ≠ 2 → s.val (W i) = 0) ∧
      s.val (W 2) = 64 ^ 2 * B ∧ (∀ q, (∀ i, W i ≠ q) → s.val q = σ.val q) ∧ s.st = σ.st ∧ s.sh = σ.sh ∧
      s.cell = σ.cell := by
  have hWe : ∀ i j : Fin 30, W i = W j ↔ i = j := fun i j => W.injective.eq_iff
  have e1 := SparseNum.copy1 c RB (W 11) (W 29) (fun e => hWB 11 e.symm) (fun e => hWB 29 e.symm)
    (by rw [Ne, hWe]; decide) B σ hB (hz 11) (hz 29) hBc
  have e2 := SparseNum.incN0 c (W 3) 4096 (σ.setv (W 11) B) (by simp [hWe, hz]) (by omega)
  have e3 := SparseNum.mulAdd1 c (mulE.trans W) B 4096 0 ((σ.setv (W 11) B).setv (W 3) 4096)
    (by show _ = _; simp [mulE, hWe]) (by show _ = _; simp [mulE, hWe])
    (by show _ = _; simp [mulE, hWe, hz]) (by show _ = _; simp [mulE, hWe, hz]) (by show _ = _; simp [mulE, hWe, hz])
    (by omega) hBc (by omega)
  have e4 := SparseNum.clear1 c (W 3) 4096 (((σ.setv (W 11) B).setv (W 3) 4096).setv ((mulE.trans W) 2)
    (0 + B * 4096)) (by simp [mulE, hWe]) (by omega)
  have e5 := SparseNum.clear1 c (W 11) B ((((σ.setv (W 11) B).setv (W 3) 4096).setv ((mulE.trans W) 2)
    (0 + B * 4096)).setv (W 3) 0) (by simp [mulE, hWe]) hBc
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), by omega, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · intro i hi
    by_cases h11 : i = 11
    · subst h11; simp [mulE, hWe]
    by_cases h3 : i = 3
    · subst h3; simp [mulE, hWe]
    simp [mulE, hWe, hz, Function.update_apply, hi, h11, h3]
  · simp [mulE, hWe]; ring
  · intro q hq
    simp [mulE, Function.update_apply, fun i => (hq i).symm]

/-- **Part 2.** -/
theorem p2_spec (c : ℕ) (hWM : ∀ i, W i ≠ RM) (hWJ : ∀ i, W i ≠ RJ) (hWL : ∀ i, W i ≠ RL) (s : WState ns nr)
    (M B L J : ℕ) (hM : s.val RM = M) (hJ : s.val RJ = J) (hL : s.val RL = L)
    (hz : ∀ i : Fin 30, i ≠ 2 → s.val (W i) = 0) (h2 : s.val (W 2) = 64 ^ 2 * B)
    (hX : (64 ^ 2 * B + 2) * (64 ^ 2 * B + 2) + 64 ^ 2 * B + 10 ≤ c) (hMc : M ≤ c) (hLc : L ≤ c) (hJc : J ≤ c) :
    ∃ s' n, WExec c (tplLenP2 W RM RJ RL) s s' n ∧
      n ≤ (18 * (64 ^ 2 * B) + 3 + 1 + (3 + 1 + ((64 ^ 2 * B + 1) * (LevelW.stepCost (64 ^ 2 * B)
        (natCeilSqrt (64 ^ 2 * B)) + 4) + 1))) + 1 + (UnaryPow.sq c + 1 + (UnaryPow.sq c + 1 + (UnaryPow.sq c + 1 +
        UnaryPow.sq c))) ∧
      s'.val (W 0) = natCeilSqrt (64 ^ 2 * B) ∧ s'.val (W 1) = J ∧ s'.val (W 25) = M ∧ s'.val (W 26) = L ∧
      (∀ i : Fin 30, i ≠ 0 → i ≠ 1 → i ≠ 25 → i ≠ 26 → s'.val (W i) = 0) ∧
      (∀ q, (∀ i, W i ≠ q) → s'.val q = s.val q) ∧ s'.st = s.st ∧ s'.sh = s.sh ∧ s'.cell = s.cell := by
  have hWe : ∀ i j : Fin 30, W i = W j ↔ i = j := fun i j => W.injective.eq_iff
  have e6 := LevelW.sqrtW_spec c (sqE.trans W) s (64 ^ 2 * B) h2 (hz 0 (by decide)) (hz 3 (by decide))
    (hz 4 (by decide)) (hz 5 (by decide)) (hz 6 (by decide)) (hz 7 (by decide)) (hz 8 (by decide))
    (hz 9 (by decide)) (hz 10 (by decide)) hX
  have hSc : natCeilSqrt (64 ^ 2 * B) ≤ c := by
    have := LevelW.natCeilSqrt_le (64 ^ 2 * B); nlinarith
  have e7 := SparseNum.clear1 c (W 2) (64 ^ 2 * B) (s.setv ((sqE.trans W) 1) (natCeilSqrt (64 ^ 2 * B)))
    (by simp [sqE, hWe, h2]) (by nlinarith)
  have e8 := SparseNum.copy1 c RJ (W 1) (W 29) (fun e => hWJ 1 e.symm) (fun e => hWJ 29 e.symm)
    (by rw [Ne, hWe]; decide) J ((s.setv ((sqE.trans W) 1) (natCeilSqrt (64 ^ 2 * B))).setv (W 2) 0)
    (by simp [Function.update_apply, fun i => (hWJ i).symm, hJ]) (by simp [sqE, hWe]; exact hz 1 (by decide))
    (by simp [sqE, hWe]; exact hz 29 (by decide)) hJc
  have e9 := SparseNum.copy1 c RM (W 25) (W 29) (fun e => hWM 25 e.symm) (fun e => hWM 29 e.symm)
    (by rw [Ne, hWe]; decide) M (((s.setv ((sqE.trans W) 1) (natCeilSqrt (64 ^ 2 * B))).setv (W 2) 0).setv (W 1) J)
    (by simp [Function.update_apply, fun i => (hWM i).symm, hM]) (by simp [sqE, hWe]; exact hz 25 (by decide))
    (by simp [sqE, hWe]; exact hz 29 (by decide)) hMc
  have e10 := SparseNum.copy1 c RL (W 26) (W 29) (fun e => hWL 26 e.symm) (fun e => hWL 29 e.symm)
    (by rw [Ne, hWe]; decide) L ((((s.setv ((sqE.trans W) 1) (natCeilSqrt (64 ^ 2 * B))).setv (W 2) 0).setv (W 1)
      J).setv (W 25) M)
    (by simp [Function.update_apply, fun i => (hWL i).symm, hL]) (by simp [sqE, hWe]; exact hz 26 (by decide))
    (by simp [sqE, hWe]; exact hz 29 (by decide)) hLc
  refine ⟨_, _, WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 e10))), le_refl _, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl⟩
  · simp [sqE, hWe]
  · simp [hWe]
  · simp [hWe]
  · simp
  · intro i a b d e
    simp [sqE, hWe, Function.update_apply, a, b, d, e]
    intro h; exact hz i h
  · intro q hq
    simp [sqE, Function.update_apply, fun i => (hq i).symm]

end Parts

end NearCubicWires.WireExponent3_5.PrimAsm.TplLen