import Proof.Wire_3_5.Primitive.SeedFix.CtrOps

/-! # X3, part 3: the two position trackers (P3:1202-1206)

"The `s×b` matrix whose columns are the nonzero vectors of `𝔽₂^s`" (P3:1202): position `q` of a block is a parity
position iff `q + 1` is a power of two, and the parity bit `t` reads the data positions `q` whose `q + 1` has bit `t`.
The center writer tracks both with registers:

* **`powStep`** (`rgNP`, `rgE`): the next power of two and the distance to it (`PowT`, `powStep_spec`);
* **`bitStep`** (`rgPW = 2^t`, `rgCD`, `rgF`): bit `t` of the position counter (`BitT`, `bitStep_spec`).

Paper quantity of the main types: the parity positions `2^t − 1` and bit `t` of a position (the parity-check matrix's
columns, P3:1202). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm

section Track
variable (cap : ℕ)

/-- **The next power of two, one position on**: `rgE − 1`, or at a power `rgE := rgNP − 1`, `rgNP := 2·rgNP`. -/
def powStep : CM :=
  .ifr rgE (.dec rgE) (.seq (FinalPass.Hash4.wcopyR rgNP rgE rgT) (.seq (.dec rgE)
    (.seq (FinalPass.Hash4.wcopyR rgNP rgT2 rgT) (WM.move rgT2 rgNP))))

theorem powStep_spec (σ : CS) (q : ℕ) (hP : PowT q (σ.val rgNP) (σ.val rgE)) (hT : σ.val rgT = 0)
    (hT2 : σ.val rgT2 = 0) (hcap : 4 * (q + 1) + 2 ≤ cap) :
    ∃ τ, WExec cap powStep σ τ (100 * (q + 1) + 20) ∧ PowT (q + 1) (τ.val rgNP) (τ.val rgE) ∧
      τ.val rgT = 0 ∧ τ.val rgT2 = 0 ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧
      (∀ r, r ≠ rgNP → r ≠ rgE → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  obtain ⟨hnp, he⟩ := powT_le hP
  by_cases h0 : σ.val rgE = 0
  · have s1 := FinalPass.Hash4.wcopyR_spec cap rgNP rgE rgT (by decide) (by decide) (by decide) σ h0 hT (by omega)
    set σ1 := σ.setv rgE (σ.val rgNP) with hσ1
    have s2 := WExec.dec (cap := cap) rgE σ1 (by simp [hσ1]; omega)
    set σ2 := σ1.setv rgE (σ1.val rgE - 1) with hσ2
    have s3 := FinalPass.Hash4.wcopyR_spec cap rgNP rgT2 rgT (by decide) (by decide) (by decide) σ2
      (by simp [hσ2, hσ1, hT2]) (by simp [hσ2, hσ1, hT]) (by simp [hσ2, hσ1]; omega)
    set σ3 := σ2.setv rgT2 (σ2.val rgNP) with hσ3
    have s4 := wmove_spec cap rgT2 rgNP (by decide) (σ3.val rgT2) σ3 rfl (by simp [hσ3, hσ2, hσ1]; omega)
      (by simp [hσ3, hσ2, hσ1]; omega)
    have w2 : σ2.val rgNP = σ.val rgNP := by simp [hσ2, hσ1]
    have w3 : σ3.val rgT2 = σ.val rgNP := by simp [hσ3, hσ2, hσ1]
    refine ⟨_, WExec.mono (WExec.ifrF h0 (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)))) (by omega),
      ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩
    · have := powT_step0 hP h0
      simp only [hσ3, hσ2, hσ1, WState.setv_val, Function.update_apply]
      simp only [show ¬((8 : Fin 26) = 9) by decide, show ¬((8 : Fin 26) = 17) by decide, if_false, if_true,
        show ¬((9 : Fin 26) = 17) by decide, show ¬((9 : Fin 26) = 8) by decide]
      convert this using 2
      · omega
    · simp [hσ3, hσ2, hσ1, Function.update_apply, hT]
    · simp [hσ3, hσ2, hσ1, Function.update_apply]
    · intro r r1 r2
      by_cases r3 : r = rgT2
      · subst r3; simp [hσ3, hσ2, hσ1, Function.update_apply, hT2]
      · simp [hσ3, hσ2, hσ1, Function.update_apply, r1, r2, r3]
  · have s1 := WExec.dec (cap := cap) rgE σ (by omega)
    refine ⟨_, WExec.mono (WExec.ifrT h0 s1) (by omega), ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩
    · have := powT_stepS hP h0
      simpa [Function.update_apply] using this
    · simp [Function.update_apply, hT]
    · simp [Function.update_apply, hT2]
    · intro r r1 r2
      simp [Function.update_apply, r2]

/-- **Bit `t` of the position counter, one on**: `rgCD − 1`; at `0` the flag toggles and `rgCD := rgPW`. -/
def bitStep : CM := .seq (.dec rgCD) (.ifr rgCD .skip (.seq (togR rgF) (FinalPass.Hash4.wcopyR rgPW rgCD rgT)))

theorem bitStep_spec (σ : CS) (t v : ℕ) (hB : BitT t v (σ.val rgCD) (σ.val rgF)) (hpw : σ.val rgPW = 2 ^ t)
    (hT : σ.val rgT = 0) (hcap : 2 ^ t + 1 ≤ cap) :
    ∃ τ, WExec cap bitStep σ τ (18 * 2 ^ t + 20) ∧ BitT t (v + 1) (τ.val rgCD) (τ.val rgF) ∧ τ.val rgT = 0 ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ (∀ r, r ≠ rgCD → r ≠ rgF → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  obtain ⟨c1, c2, f1⟩ := bitT_pos hB
  have s1 := WExec.dec (cap := cap) rgCD σ (by omega)
  set σ1 := σ.setv rgCD (σ.val rgCD - 1) with hσ1
  by_cases hc : σ.val rgCD = 1
  · have z1 : σ1.val rgCD = 0 := by simp [hσ1, hc]
    have s2 := togR_spec cap rgF σ1 (by simp [hσ1]; omega) (by omega)
    set σ2 := σ1.setv rgF (1 - σ1.val rgF) with hσ2
    have s3 := FinalPass.Hash4.wcopyR_spec cap rgPW rgCD rgT (by decide) (by decide) (by decide) σ2
      (by simp [hσ2, z1]) (by simp [hσ2, hσ1, hT]) (by simp [hσ2, hσ1, hpw]; omega)
    refine ⟨_, WExec.mono (WExec.seq s1 (WExec.ifrF z1 (WExec.seq s2 s3))) (by simp [hσ2, hσ1, hpw]; omega),
      ?_, ?_, rfl, rfl, ?_, rfl⟩
    · have := bitT_flip hB hc
      simpa [hσ2, hσ1, Function.update_apply, hpw] using this
    · simp [hσ2, hσ1, Function.update_apply, hT]
    · intro r r1 r2
      simp [hσ2, hσ1, Function.update_apply, r1, r2]
  · have z1 : σ1.val rgCD ≠ 0 := by simp [hσ1]; omega
    refine ⟨_, WExec.mono (WExec.seq s1 (WExec.ifrT z1 (WExec.skip _))) (by omega), ?_, ?_, rfl, rfl, ?_, rfl⟩
    · have := bitT_keep hB hc
      simpa [hσ1, Function.update_apply] using this
    · simp [hσ1, Function.update_apply, hT]
    · intro r r1 r2
      simp [hσ1, Function.update_apply, r1]

end Track

end NearCubicWires.WireExponent3_5.PrimT.Ctr
