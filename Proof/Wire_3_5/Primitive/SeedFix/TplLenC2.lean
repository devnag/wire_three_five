import Proof.Wire_3_5.Primitive.SeedFix.TplLenC1

/-! # TplLenC, part 2: the third part composed

**`p3_spec`**: from part 2's exit (`S, J, M, L` in `W 0, 1, 25, 26`, every other `W i` at `0`, `RT = 0`, `O` blank at
`0`): `RT = |tplWord M S J L|`, every `W i` at `0`, `O` holds the word (head back at `0`), every other register, stream,
head and the cell kept.

Paper quantity of the main type: the stage-5 template word's length (P3:1449-1477, 3170-3178). -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.TplLenC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.TplLen

section P3
variable {ns nr : ℕ} (c : ℕ) (O : Fin (ns + 1)) (W : Fin 30 ↪ Fin nr) (RT : Fin nr)

/-- **Part 3.** -/
theorem p3_spec (hRT : ∀ i, W i ≠ RT) (s : WState ns nr) (M Sv J L : ℕ) (h0 : s.val (W 0) = Sv)
    (h1 : s.val (W 1) = J) (h25 : s.val (W 25) = M) (h26 : s.val (W 26) = L)
    (hz : ∀ i : Fin 30, i ≠ 0 → i ≠ 1 → i ≠ 25 → i ≠ 26 → s.val (W i) = 0) (hT : s.val RT = 0)
    (hO : s.st O = []) (hOh : s.sh O = 0)
    (hcap : LevelW.lvCap Sv J J ≤ c) (hw : (FinalPass.SymParts.Tmpl.tplWord M Sv J L).length ≤ c) (hJc : J + 1 ≤ c)
    (hLc : L ≤ c) (hMc : M ≤ c) (hSc : Sv ≤ c) :
    ∃ τ n, WExec c (tplLenP3 O W RT) s τ n ∧
      n ≤ FinalPass.SymParts.Tmpl.tplWBound c J M + 1 + (UnaryPow.sq c + 1 +
        (5 * (FinalPass.SymParts.Tmpl.tplWord M Sv J L).length + 1 + 1 + (4 * UnaryPow.sq c + 3))) ∧
      τ.val RT = (FinalPass.SymParts.Tmpl.tplWord M Sv J L).length ∧ (∀ i, τ.val (W i) = 0) ∧
      (∀ q, q ≠ RT → (∀ i, W i ≠ q) → τ.val q = s.val q) ∧
      τ.st = Function.update s.st O (FinalPass.SymParts.Tmpl.tplWord M Sv J L) ∧ τ.sh = s.sh ∧ τ.cell = s.cell := by
  have hne : ∀ {i j : Fin 30}, i ≠ j → W i ≠ W j := fun h => W.injective.ne h
  obtain ⟨wd, hwd⟩ : ∃ w, w = FinalPass.SymParts.Tmpl.tplWord M Sv J L := ⟨_, rfl⟩
  rw [← hwd] at hw ⊢
  obtain ⟨n1, e1, n1le⟩ := p3a_spec c O W s M Sv J L h0 h1 h25 h26 hz (by rw [hOh, hO]; rfl) hcap
    (by rw [← hwd]; exact hw) hJc hLc hMc
  rw [← hwd] at e1
  obtain ⟨A, hA⟩ : ∃ a, a = appendO s O (W 24) wd := ⟨_, rfl⟩
  rw [← hA] at e1
  have z24 : s.val (W 24) = 0 := hz 24 (by decide) (by decide) (by decide) (by decide)
  have A24 : A.val (W 24) = wd.length := by rw [hA]; simp [z24]
  have AT : A.val RT = 0 := by rw [hA]; simp [Function.update_of_ne (Ne.symm (hRT 24)), hT]
  have A29 : A.val (W 29) = 0 := by
    rw [hA]; simp [Function.update_of_ne (hne (show (29 : Fin 30) ≠ 24 by decide))]
    exact hz 29 (by decide) (by decide) (by decide) (by decide)
  have e2 := p3b_spec c W RT hRT A wd.length A24 AT A29 hw
  obtain ⟨B, hB⟩ : ∃ b, b = A.setv RT wd.length := ⟨_, rfl⟩
  rw [← hB] at e2
  have B24 : B.val (W 24) = wd.length := by rw [hB]; simp [Function.update_of_ne (hRT 24), A24]
  have e3 := p3c_spec c O W B wd.length B24 hw
  obtain ⟨D, hD⟩ : ∃ d, d = (B.setv (W 24) 0).seth O (B.sh O - wd.length) := ⟨_, rfl⟩
  rw [← hD] at e3
  have Dv : ∀ q, D.val q = Function.update (Function.update (Function.update s.val (W 24) wd.length) RT
      wd.length) (W 24) 0 q := fun q => by
    rw [hD, hB, hA]; simp [z24]
  have D0 : D.val (W 0) = Sv := by
    rw [Dv]; simp [Function.update_of_ne (hne (show (0 : Fin 30) ≠ 24 by decide)), Function.update_of_ne (hRT 0), h0]
  have D1 : D.val (W 1) = J := by
    rw [Dv]; simp [Function.update_of_ne (hne (show (1 : Fin 30) ≠ 24 by decide)), Function.update_of_ne (hRT 1), h1]
  have D25 : D.val (W 25) = M := by
    rw [Dv]; simp [Function.update_of_ne (hne (show (25 : Fin 30) ≠ 24 by decide)), Function.update_of_ne (hRT 25),
      h25]
  have D26 : D.val (W 26) = L := by
    rw [Dv]; simp [Function.update_of_ne (hne (show (26 : Fin 30) ≠ 24 by decide)), Function.update_of_ne (hRT 26),
      h26]
  have e4 := p3d_spec c W D Sv J M L D0 D1 D25 D26 hSc (by omega) hMc hLc
  refine ⟨_, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4)), by omega, ?_, fun i => ?_, fun q hq hqW => ?_, ?_,
    ?_, ?_⟩
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (Ne.symm (hRT 26)), Function.update_of_ne (Ne.symm (hRT 25)),
      Function.update_of_ne (Ne.symm (hRT 1)), Function.update_of_ne (Ne.symm (hRT 0)), Dv,
      Function.update_of_ne (Ne.symm (hRT 24))]
    simp
  · simp only [WState.setv_val]
    by_cases i26 : i = 26
    · subst i26; simp
    by_cases i25 : i = 25
    · subst i25; simp [Function.update_of_ne (hne (show (25 : Fin 30) ≠ 26 by decide))]
    by_cases i1 : i = 1
    · subst i1; simp [Function.update_of_ne (hne (show (1 : Fin 30) ≠ 26 by decide)),
        Function.update_of_ne (hne (show (1 : Fin 30) ≠ 25 by decide))]
    by_cases i0 : i = 0
    · subst i0; simp [Function.update_of_ne (hne (show (0 : Fin 30) ≠ 26 by decide)),
        Function.update_of_ne (hne (show (0 : Fin 30) ≠ 25 by decide)),
        Function.update_of_ne (hne (show (0 : Fin 30) ≠ 1 by decide))]
    rw [Function.update_of_ne (hne i26), Function.update_of_ne (hne i25), Function.update_of_ne (hne i1),
      Function.update_of_ne (hne i0), Dv]
    by_cases i24 : i = 24
    · subst i24; simp
    · rw [Function.update_of_ne (hne i24), Function.update_of_ne (hRT i), Function.update_of_ne (hne i24)]
      exact hz i i0 i1 i25 i26
  · simp only [WState.setv_val]
    rw [Function.update_of_ne (fun e => hqW 26 e.symm), Function.update_of_ne (fun e => hqW 25 e.symm),
      Function.update_of_ne (fun e => hqW 1 e.symm), Function.update_of_ne (fun e => hqW 0 e.symm), Dv,
      Function.update_of_ne (fun e => hqW 24 e.symm), Function.update_of_ne hq,
      Function.update_of_ne (fun e => hqW 24 e.symm)]
  · simp only [WState.setv_st]
    rw [hD]; simp only [WState.seth_st, WState.setv_st]; rw [hB]; simp only [WState.setv_st]; rw [hA]
    simp [hO]
  · simp only [WState.setv_sh]
    rw [hD]
    funext j
    by_cases hj : j = O
    · subst hj; rw [hB, hA]; simp [hOh]
    · simp only [WState.seth_sh, WState.setv_sh, Function.update_of_ne hj]; rw [hB, hA]
      simp [Function.update_of_ne hj]
  · simp only [WState.setv_cell]; rw [hD, hB, hA]; simp

end P3

end NearCubicWires.WireExponent3_5.PrimT.TplLenC
