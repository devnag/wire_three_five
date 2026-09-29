import Proof.Wire_3_5.Foundations.SwPartsTmpl

/-! # SWn item 6, part A: the template length's program and its bounds

The SWn needs `|levelWord M J W (blank rows of length L)|` of the base list `⟨M, B⟩` in a register (the length of
the template word `S3.templJ k j`). E's `tplW` writes the word raw; here it runs onto a scratch stream and
its output counter is read:

* `WExec.capUp` (a run at a capacity runs at every larger one);
* `mulE`, `sqE`, **`tplLenW`** (copy `B`, `4096·B`, `S = ⌈√(4096·B)⌉` by `LevelW.sqrtW`, copy `J`, `M`, `L`, `tplW`,
  the counter into `RT`, rewind, clears);
* `pow_J_le`, `J_le`, `tplWord_len_le` (the word within `200000·(M+B+L+2)²`).

Paper quantity of the main type: the stage-5 template word's length (`list:base`/`list:flatten`, P3:1449-1477,
the call word `4·3 + j`, P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.TplLen
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.CanonicalFourfoldRowProgram (natCeilSqrt)

section Cap
variable {ns nr : ℕ}

/-- **A run at a capacity runs at every larger capacity.** -/
theorem WExec.capUp {cap cap' : ℕ} (hc : cap ≤ cap') {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ}
    (h : WExec cap P σ τ n) : WExec cap' P σ τ n := by
  induction h with
  | skip σ => exact WExec.skip σ
  | inc r σ hv => exact WExec.inc r σ (by omega)
  | dec r σ hv => exact WExec.dec r σ (by omega)
  | fwd i σ => exact WExec.fwd i σ
  | bwd i σ => exact WExec.bwd i σ
  | wr i b σ => exact WExec.wr i b σ
  | setc v σ => exact WExec.setc v σ
  | seq _ _ ih1 ih2 => exact WExec.seq ih1 ih2
  | ifrT h _ ih => exact WExec.ifrT h ih
  | ifrF h _ ih => exact WExec.ifrF h ih
  | ifsT h _ ih => exact WExec.ifsT h ih
  | ifsF h _ ih => exact WExec.ifsF h ih
  | whrF h => exact WExec.whrF h
  | whrT h _ _ ih1 ih2 => exact WExec.whrT h ih1 ih2
  | whsF h => exact WExec.whsF h
  | whsT h _ _ ih1 ih2 => exact WExec.whsT h ih1 ih2
  | mono _ hnm ih => exact WExec.mono ih hnm

end Cap

/-- `mulAddW`'s registers: `W 11` (`B`), `W 3` (`4096`), `W 2` (the product), `W 4`, `W 5` scratch. -/
def mulE : Fin 5 ↪ Fin 30 := ⟨![11, 3, 2, 4, 5], by decide⟩

/-- `sqrtW`'s registers: `W 2` the radicand, `W 0` the root, `W 3 … 10` scratch. -/
def sqE : Fin 10 ↪ Fin 30 := ⟨![2, 0, 3, 4, 5, 6, 7, 8, 9, 10], by decide⟩

section Prog
variable {ns nr : ℕ} (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RM RB RJ RL RT : Fin nr)

/-- Part 1: `4096·B` into `W 2` (`B` copied into `W 11`, `4096` in `W 3`, both cleared). -/
def tplLenP1 : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR RB (W 11) (W 29)) (.seq (StarNums.incN (W 3) 4096)
    (.seq (UnaryArith.mulAddW (mulE.trans W)) (.seq (WM.clear (W 3)) (WM.clear (W 11)))))

/-- Part 2: `S = ⌈√(4096·B)⌉` into `W 0` (radicand cleared); `J`, `M`, `L` into `W 1`, `W 25`, `W 26`. -/
def tplLenP2 : WM ns nr :=
  .seq (LevelW.sqrtW (sqE.trans W)) (.seq (WM.clear (W 2)) (.seq (FinalPass.Hash4.wcopyR RJ (W 1) (W 29))
    (.seq (FinalPass.Hash4.wcopyR RM (W 25) (W 29)) (FinalPass.Hash4.wcopyR RL (W 26) (W 29)))))

/-- Part 3: E's `tplW` onto `O` (counter `W 24`), the counter into `RT`, the rewind, the clears. -/
def tplLenP3 : WM ns nr :=
  .seq (FinalPass.SymParts.Tmpl.tplW O W) (.seq (FinalPass.Hash4.wcopyR (W 24) RT (W 29))
    (.seq (WM.rewind O (W 24)) (.seq (WM.clear (W 0)) (.seq (WM.clear (W 1))
      (.seq (WM.clear (W 25)) (WM.clear (W 26)))))))

/-- **The template length**: parts 1, 2, 3. -/
def tplLenW : WM ns nr := .seq (tplLenP1 W RB) (.seq (tplLenP2 W RM RJ RL) (tplLenP3 O W RT))

end Prog

/-! ## Bounds -/

theorem J_le (M B : ℕ) : (⟨M, B⟩ : Lists.BaseListParams).J ≤ B + 9 := by
  show Nat.clog 2 B + 9 ≤ B + 9
  have := Nat.clog_le_of_le_pow (b := 2) (x := B) (y := B) Nat.lt_two_pow_self.le
  omega

theorem pow_J_le (M B : ℕ) : 2 ^ (⟨M, B⟩ : Lists.BaseListParams).J ≤ 1024 * (B + 1) := by
  show 2 ^ (Nat.clog 2 B + 9) ≤ 1024 * (B + 1)
  rw [pow_add]
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  · have := LevelW.pow_clog_le B hB
    have e : (2 : ℕ) ^ 9 = 512 := by norm_num
    rw [e]; omega

theorem flatMap_len_le (l : List ℕ) (f : ℕ → List Bool) (K : ℕ) (h : ∀ j ∈ l, (f j).length ≤ K) :
    (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := h a (by simp)
    have h2 := ih (fun j hj => h j (by simp [hj]))
    omega

/-- **The raw template word within `200000·(M+B+L+2)²`.** -/
theorem tplWord_len_le (M B L : ℕ) :
    (FinalPass.SymParts.Tmpl.tplWord M (natCeilSqrt (64 ^ 2 * B)) (⟨M, B⟩ : Lists.BaseListParams).J L).length ≤
      200000 * (M + B + L + 2) ^ 2 := by
  have hS : natCeilSqrt (64 ^ 2 * B) ≤ 4096 * B + 1 := by
    have := LevelW.natCeilSqrt_le (64 ^ 2 * B); norm_num at this ⊢; omega
  have hJ := J_le M B
  have hP := pow_J_le M B
  set J := (⟨M, B⟩ : Lists.BaseListParams).J with hJd
  set Sv := natCeilSqrt (64 ^ 2 * B) with hSd
  have hrec : ∀ j ∈ FinalPass.ListEval.levels J, (FinalPass.SymParts.Tmpl.tplRec Sv J j L).length ≤
      30000 * (M + B + L + 2) := by
    intro j hj
    have hjJ : j ≤ J := by
      simp only [FinalPass.ListEval.levels, List.mem_reverse, List.mem_range] at hj; omega
    rw [FinalPass.SymParts.Tmpl.tplRec_length]
    have hw := LevelW.winAt_le Sv J j
    have hp : 2 ^ (j / 3) ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.div_le_self _ _) hjJ)
    have hc := LevelW.pow_clog_le (2 * LevelW.winAt Sv J j + 1) (by omega)
    omega
  have hfl := flatMap_len_le (FinalPass.ListEval.levels J) (fun j => FinalPass.SymParts.Tmpl.tplRec Sv J j L)
    (30000 * (M + B + L + 2)) hrec
  rw [LevelWordW.levels_length] at hfl
  have hJ1 : J + 1 ≤ 5 * (M + B + L + 2) := by omega
  have hm : (J + 1) * (30000 * (M + B + L + 2)) ≤ (5 * (M + B + L + 2)) * (30000 * (M + B + L + 2)) :=
    Nat.mul_le_mul_right _ hJ1
  have e : (5 * (M + B + L + 2)) * (30000 * (M + B + L + 2)) = 150000 * (M + B + L + 2) ^ 2 := by ring
  have hZ : M + 2 ≤ 5000 * (M + B + L + 2) ^ 2 := by nlinarith
  unfold FinalPass.SymParts.Tmpl.tplWord
  simp only [List.length_append, List.length_cons, List.length_nil, FinalPass.SymParts.Tmpl.repsB_eq,
    List.length_replicate]
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.TplLen