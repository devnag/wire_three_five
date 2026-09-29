import Proof.Wire_3_5.Primitive.SeedFix.FlipsGen

/-! # FLIPS, part 8: the writer's streams set up (P3:1206-1207)

Before the cell loops, the flips writer's streams hold framed words: the error words' stale frames (`n` zeros, C5's
decoder overwrites them) and the three counters at `0` (`frame (binary kh 0)`, `kh` zeros). **`initStream X src`**
writes `frameP (replicate v false) ++ [false]` on the blank stream `X` (`v` in the register `src`), rewinds it, and
restores every register (`initStream_spec`).

Paper quantity of the main type: the counters' start `frame (binary kh 0)` (the first cell). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Flips
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GS GR gIN gOUT)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem binary_zero : ∀ w : ℕ, binary w 0 = List.replicate w false
  | 0 => rfl
  | w + 1 => by simp [binary, binary_zero w, List.replicate_succ]

section Init
variable (cap : ℕ)

/-- **A blank stream set to `frameP (replicate v false) ++ [false]`** (`v` in `src`), rewound. -/
def initStream (X : Fin (GS + 1)) (src : Fin GR) : WM GS GR :=
  .seq (FinalPass.Hash4.wcopyR src rJ rTmp) (.seq (zerosW X) (.seq (emitW X false) (.seq (.inc rOc) (rew1 X rOc))))

/-- Its cost. -/
def initCost (v : ℕ) : ℕ := 18 * v + 3 + 1 + (v * 20 + 1 + 1 + (3 + 1 + (3 + 1 + ((2 * v + 1) * 5 + 1))))

theorem initStream_spec (X : Fin (GS + 1)) (src : Fin GR) (hsJ : src ≠ rJ) (hsT : src ≠ rTmp) (hsO : src ≠ rOc)
    (σ : WState GS GR) (v : ℕ) (hv : σ.val src = v) (hX : σ.st X = []) (hXh : σ.sh X = 0) (hJ : σ.val rJ = 0)
    (hT : σ.val rTmp = 0) (hO : σ.val rOc = 0) (hcap : 2 * v + 2 ≤ cap) :
    ∃ τ, WExec cap (initStream X src) σ τ (initCost v) ∧ τ.st X = frameP (List.replicate v false) ++ [false] ∧
      τ.sh X = 0 ∧ (∀ i, i ≠ X → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ (∀ r, τ.val r = σ.val r) ∧
      τ.cell = σ.cell := by
  have hJT : rJ ≠ rTmp := by decide
  have s1 := FinalPass.Hash4.wcopyR_spec cap src rJ rTmp hsJ hsT hJT σ hJ hT (by omega)
  rw [hv] at s1
  obtain ⟨σ1, hσ1⟩ : ∃ y, y = σ.setv rJ v := ⟨_, rfl⟩
  rw [← hσ1] at s1
  obtain ⟨σ2, e2, a2, j2, o2, f2⟩ := zerosW_spec cap X v σ1 (by rw [hσ1]; simp [WState.setv])
    (by rw [hσ1]; simp [WState.setv, hX, hXh]) (by rw [hσ1]; simp [WState.setv, Function.update_apply, oJ, hO]; omega)
    (by omega)
  have o1 : σ1.val rOc = 0 := by rw [hσ1]; simp [WState.setv, Function.update_apply, oJ, hO]
  rw [o1, Nat.zero_add] at o2
  have s3 := emitW_spec (cap := cap) X false σ2 a2.sh
  obtain ⟨σ3, hσ3⟩ : ∃ y, y = (σ2.sets X (σ2.st X ++ [false])).seth X ((σ2.st X).length + 1) := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have v3 : σ3.val = σ2.val := by rw [hσ3]; rfl
  have s4 := WExec.inc (cap := cap) rOc σ3 (by rw [v3, o2]; omega)
  obtain ⟨σ4, hσ4⟩ : ∃ y, y = σ3.setv rOc (σ3.val rOc + 1) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have st3 : σ3.st X = frameP (List.replicate v false) ++ [false] := by
    rw [hσ3]; simp [WState.sets, WState.seth, a2.st, hσ1, WState.setv, hX]
  have sh4 : σ4.sh X = 2 * v + 1 := by
    rw [hσ4, hσ3]; simp [WState.setv, WState.sets, WState.seth, a2.st, hσ1, hX]
  have o4 : σ4.val rOc = 2 * v + 1 := by rw [hσ4]; simp [WState.setv, v3, o2]
  obtain ⟨τ, e5, t1, t2, t3, t4, t5, t6⟩ := rew1_spec cap X rOc (2 * v + 1) σ4 o4 sh4 (by omega)
  refine ⟨τ, WExec.seq s1 (WExec.seq e2 (WExec.seq s3 (WExec.seq s4 e5))), ?_, t1, fun i hi => ?_, fun r => ?_, ?_⟩
  · rw [t3, hσ4]; exact st3
  · rw [t3, t4 i hi, hσ4, hσ3]
    simp only [WState.setv, WState.sets, WState.seth, Function.update_apply, if_neg hi]
    rw [(a2.frS i hi).1, (a2.frS i hi).2, hσ1]
    exact ⟨rfl, rfl⟩
  · by_cases h1 : r = rOc
    · subst h1; rw [t2, hO]
    · rw [t5 r h1, hσ4]
      simp only [WState.setv, Function.update_apply, if_neg h1]
      rw [v3]
      by_cases h2 : r = rJ
      · subst h2; rw [j2, hJ]
      · rw [f2 r h2 h1, hσ1]; simp [WState.setv, Function.update_apply, h2]
  · rw [t6, hσ4, hσ3]; simp only [WState.setv, WState.sets, WState.seth]; rw [a2.cell, hσ1]; rfl

end Init

end NearCubicWires.WireExponent3_5.PrimT.Flips
