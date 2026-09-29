import Proof.Wire_3_5.Primitive.SeedFix.TplLenC2
import Proof.Wire_3_5.Primitive.SeedFix.TplLenC3

/-! # TplLenC, part 4: the template length program's run and its interface

* **`run_gen`**: the parts 1, 2 (`p1_spec`, `p2_spec`) and the part 3 (`p3_spec`) composed at any capacity `c`
  meeting `caps`: `RT` ends at `|tplWord M S J L|` (`S = ⌈√(64²B)⌉`), every other register as at the entry, `O`
  holds the word, heads and cell kept, cost `≤ 10⁸(c+2)³`;
* **`tplLen_spec`**: `UnionMachine.NumsA.TplIface tplKt tplEt` (`tplKt = 10³⁶`, `tplEt = 6`) for
  `PrimAsm.TplLen.tplLenW`, stated unfolded (`tplNum` unfolded), run at `capI M B L` and lifted by `WExec.capUp`.

Paper quantity of the main type: the stage-5 template's length `|levelWord M J W (L-rows)|` (list:base P3:1449-1477,
the SYM call numbers P3:3170-3178). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.TplLenC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.CanonicalFourfoldRowProgram (natCeilSqrt)

section Run
variable {ns nr : ℕ} (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RM RB RJ RL RT : Fin nr)

/-- **The three parts composed** at a capacity `c` meeting `caps`. -/
theorem run_gen (c : ℕ) (hWR : ∀ i, W i ∉ [RM, RB, RJ, RL, RT]) (σ : WState ns nr) (M B L J : ℕ)
    (vM : σ.val RM = M) (vB : σ.val RB = B) (vJ : σ.val RJ = J) (vL : σ.val RL = L) (vT : σ.val RT = 0)
    (hz : ∀ i, σ.val (W i) = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (hBc : B ≤ c) (hMc : M ≤ c) (hLc : L ≤ c) (h4 : B * 4096 + 4096 ≤ c)
    (hX : (64 ^ 2 * B + 2) * (64 ^ 2 * B + 2) + 64 ^ 2 * B + 10 ≤ c)
    (hcap : LevelW.lvCap (natCeilSqrt (64 ^ 2 * B)) J J ≤ c)
    (hw : (FinalPass.SymParts.Tmpl.tplWord M (natCeilSqrt (64 ^ 2 * B)) J L).length ≤ c) (hJc : J + 1 ≤ c)
    (hSc : natCeilSqrt (64 ^ 2 * B) ≤ c) :
    ∃ τ n, WExec c (TplLen.tplLenW O W RM RB RJ RL RT) σ τ n ∧ n ≤ 10 ^ 8 * (c + 2) ^ 3 ∧
      τ.val RT = (FinalPass.SymParts.Tmpl.tplWord M (natCeilSqrt (64 ^ 2 * B)) J L).length ∧
      (∀ q, q ≠ RT → τ.val q = σ.val q) ∧
      τ.st = Function.update σ.st O (FinalPass.SymParts.Tmpl.tplWord M (natCeilSqrt (64 ^ 2 * B)) J L) ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have hWM : ∀ i, W i ≠ RM := fun i e => hWR i (by rw [e]; simp)
  have hWB : ∀ i, W i ≠ RB := fun i e => hWR i (by rw [e]; simp)
  have hWJ : ∀ i, W i ≠ RJ := fun i e => hWR i (by rw [e]; simp)
  have hWL : ∀ i, W i ≠ RL := fun i e => hWR i (by rw [e]; simp)
  have hWT : ∀ i, W i ≠ RT := fun i e => hWR i (by rw [e]; simp)
  obtain ⟨s, n1, e1, n1le, sz, s2, skeep, sst, ssh, scell⟩ := TplLen.p1_spec W RB c hWB σ B vB hz hBc h4
  obtain ⟨s', n2, e2, n2le, s0, s1, s25, s26, sz', skeep', sst', ssh', scell'⟩ :=
    TplLen.p2_spec W RM RJ RL c hWM hWJ hWL s M B L J (by rw [skeep RM hWM, vM]) (by rw [skeep RJ hWJ, vJ])
      (by rw [skeep RL hWL, vL]) sz s2 hX hMc hLc (by omega)
  obtain ⟨τ, n3, e3, n3le, tT, tW, tkeep, tst, tsh, tcell⟩ :=
    p3_spec c O W RT hWT s' M _ J L s0 s1 s25 s26 sz' (by rw [skeep' RT hWT, skeep RT hWT, vT])
      (by rw [sst', sst, hO]) (by rw [ssh', ssh, hOh]) hcap hw hJc hLc hMc hSc
  have hXc : 64 ^ 2 * B ≤ c := by
    have e : 64 ^ 2 * B = 4096 * B := by norm_num
    omega
  have hS1 := LevelW.natCeilSqrt_le (64 ^ 2 * B)
  refine ⟨τ, _, WExec.seq e1 (WExec.seq e2 e3), cost_le c _ _ J M _ n1 n2 n3 hXc hS1 hJc hMc hw n1le n2le n3le, tT,
    fun q hq => ?_, by rw [tst, sst', sst], by rw [tsh, ssh', ssh], by rw [tcell, scell', scell]⟩
  by_cases hq' : ∃ i, W i = q
  · obtain ⟨i, rfl⟩ := hq'
    rw [tW i, hz i]
  · simp only [not_exists] at hq'
    rw [tkeep q hq hq', skeep' q hq', skeep q hq']

end Run

/-- **The template length program meets `TplIface tplKt tplEt`** (unfolded, `tplNum` unfolded). -/
theorem tplLen_spec : ∀ {ns nr : ℕ} (cap : ℕ) (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RM RB RJ RL RT : Fin nr),
    [RM, RB, RJ, RL, RT].Nodup → (∀ i, W i ∉ [RM, RB, RJ, RL, RT]) → ∀ (σ : WState ns nr) (M B L : ℕ),
    σ.val RM = M → σ.val RB = B → σ.val RJ = (⟨M, B⟩ : Lists.BaseListParams).J → σ.val RL = L → σ.val RT = 0 →
    (∀ i, σ.val (W i) = 0) → σ.st O = [] → σ.sh O = 0 → tplKt * (M + B + L + 2) ^ tplEt ≤ cap →
    ∃ (τ : WState ns nr) (c : ℕ), WExec cap (TplLen.tplLenW O W RM RB RJ RL RT) σ τ c ∧
      τ.val RT = (FinalPass.ListEval.levelWord M (⟨M, B⟩ : Lists.BaseListParams).J
        (⟨M, B⟩ : Lists.BaseListParams).W (fun _ => List.replicate L false)).length ∧
      (∀ q, q ≠ RT → τ.val q = σ.val q) ∧ (∀ i, i ≠ O → τ.st i = σ.st i) ∧
      (τ.st O).length ≤ tplKt * (M + B + L + 2) ^ tplEt ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      c ≤ tplKt * (M + B + L + 2) ^ tplEt := by
  intro ns nr cap O W RM RB RJ RL RT _ hWR σ M B L vM vB vJ vL vT hz hO hOh hcap
  have hK : tplKt * (M + B + L + 2) ^ tplEt = 10 ^ 36 * (M + B + L + 2) ^ 6 := by unfold tplKt tplEt; rfl
  rw [hK] at hcap ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := TplLen.caps M B L _ le_rfl
  obtain ⟨τ, n, e, hn, tT, tkeep, tst, tsh, tcell⟩ :=
    run_gen O W RM RB RJ RL RT (TplLen.capI M B L) hWR σ M B L _ vM vB vJ vL vT hz hO hOh h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hc := capI_le M B L
  have hcc := capI_cube M B L
  refine ⟨τ, n, TplLen.WExec.capUp (le_trans hc hcap) e, ?_, tkeep, fun i hi => ?_, ?_, tsh, tcell,
    le_trans hn hcc⟩
  · rw [tT]
    exact congrArg List.length (FinalPass.SymParts.Tmpl.tplWord_eq ⟨M, B⟩ L)
  · rw [tst, Function.update_of_ne hi]
  · refine le_trans (le_of_eq ?_) (le_trans h7 hc)
    rw [tst]
    simp

end NearCubicWires.WireExponent3_5.PrimT.TplLenC
