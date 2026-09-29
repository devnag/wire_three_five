import Proof.Wire_3_5.Primitive.SeedFix.Tau

/-! # SB, part 6: the trace mask program with its work words

`tauW_spec` (the trace mask `frame (binary ℓ (GF2.tau p ℓ))` of `GF(2^ℓ)`, P3:2053-2055, 2932-2941) states
the mask, the modulus and the heads; a pool writer (`CoreWordsM`) must also erase the program's five work
streams, so it needs their contents. The program's invariant (`OuterInv`) keeps every work stream an `ℓ`-bit frame:

* **`tauW_spec2`**: `tauW_spec` (its proof, re-run) with `∀ j ≥ 2, ∃ x, τ.st (Sm j) = frame (binary ℓ x)`.

Paper quantity of the main type: the trace mask word (S4's word `4`, `Filt.tauWord`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBTau
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.GF NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT

section Inner
variable {ns nr : ℕ} (cap : ℕ) (Sm : Fin 7 ↪ Fin (ns + 1)) (Rg : Fin 9 ↪ Fin nr)

theorem tauW_spec2 (ℓ p : ℕ) (hc : PrimitiveCert p ℓ) (hcap : 2 * ℓ + 2 ≤ cap) (σ : WState ns nr)
    (hP : σ.st (Sm 0) = frame (binary ℓ p)) (hhP : σ.sh (Sm 0) = 0)
    (hO : σ.st (Sm 1) = frame (binary ℓ 0)) (hhO : σ.sh (Sm 1) = 0)
    (hC : σ.st (Sm 2) = frame (binary ℓ 0)) (hhC : σ.sh (Sm 2) = 0)
    (t0 y0 c0 s0 : ℕ) (hT : σ.st (Sm 3) = frame (binary ℓ t0)) (hhT : σ.sh (Sm 3) = 0)
    (hY : σ.st (Sm 4) = frame (binary ℓ y0)) (hhY : σ.sh (Sm 4) = 0)
    (hA : σ.st (Sm 5) = frame (binary ℓ c0)) (hhA : σ.sh (Sm 5) = 0)
    (hS : σ.st (Sm 6) = frame (binary ℓ s0)) (hhS : σ.sh (Sm 6) = 0)
    (hR0 : ∀ j : Fin 9, j ≠ 4 → σ.val (Rg j) = 0) (hL : σ.val (Rg 4) = ℓ) :
    ∃ τ, WExec cap (tauW Sm Rg) σ τ (tauCost ℓ) ∧
      τ.st (Sm 1) = frame (binary ℓ (GF2.tau p ℓ)) ∧ τ.sh (Sm 1) = 0 ∧
      τ.st (Sm 0) = σ.st (Sm 0) ∧ (∀ j : Fin 7, τ.sh (Sm j) = 0) ∧
      τ.val (Rg 4) = ℓ ∧ (∀ j : Fin 9, j ≠ 4 → τ.val (Rg j) = 0) ∧ WFrame (tauS Sm) (tauR Rg) σ τ ∧
      (∀ j : Fin 7, 2 ≤ j.val → ∃ x, τ.st (Sm j) = frame (binary ℓ x)) := by
  have hℓ := hc.1
  have hI0 : OuterInv Sm Rg ℓ p 0 σ := by
    refine ⟨hP, hhP, ?_, by simp [hhO], hC, hhC, ⟨t0, hT⟩, hhT, ⟨y0, hY⟩, hhY, ⟨c0, hA⟩, hhA, ⟨s0, hS⟩, hhS,
      hR0 0 (by decide), hR0 1 (by decide), hR0 2 (by decide), hR0 3 (by decide), hL, hR0 5 (by decide),
      hR0 6 (by decide), hR0 7 (by decide), hR0 8 (by decide)⟩
    rw [hO, maskBits_zero, frame_binary']
  obtain ⟨σ1, h1, hI1, hF1⟩ := outerLoop_spec cap Sm Rg ℓ p hℓ hcap hc ℓ 0 σ (by omega) hI0
  obtain ⟨i1P, i1hP, i1O, i1hO, i1C, i1hC, ⟨xT, i1T⟩, i1hT, ⟨xY, i1Y⟩, i1hY, ⟨xA, i1A⟩, i1hA, ⟨xS, i1S⟩, i1hS, i1F,
    i1G, i1R, i1RY, i1L, i1B, i1I, i1T1, i1PC⟩ := hI1
  have h2 := retC_spec cap (Sm 1) (Rg 5) (Rg 7) (Rg 8) (by simp) (by simp) (by simp) ℓ σ1 i1B i1T1 (by omega)
    (by omega)
  obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr,
      τ = (σ1.seth (Sm 1) (σ1.sh (Sm 1) - 2 * ℓ)).setv (Rg 8) (σ1.val (Rg 8) - 2 * ℓ) := ⟨_, rfl⟩
  rw [← hσ2] at h2
  have h3 := wclear_spec cap (Rg 5) ℓ σ2 (by rw [hσ2]; simp [i1B]) (by rw [hσ2]; simp [i1B]; omega)
  refine ⟨_, WExec.mono (WExec.seq h1 (WExec.seq h2 h3)) (by unfold tauCost; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WState.setv_st, hσ2]; simp [i1O, maskBits_full p ℓ hc, frame_binary_eq]
  · rw [WState.setv_sh, hσ2]; simp [i1hO]
  · rw [WState.setv_st, hσ2]; simp [i1P, hP]
  · intro j
    rw [WState.setv_sh, hσ2]
    fin_cases j <;> simp [Function.update_apply, i1hP, i1hO, i1hC, i1hT, i1hY, i1hA, i1hS]
  · rw [hσ2]; simp [i1L]
  · intro j hj
    rw [hσ2]
    fin_cases j <;> simp [Function.update_apply, i1F, i1G, i1R, i1RY, i1I, i1T1, i1PC] at hj ⊢
  · rw [hσ2]
    exact (hF1.trans ((frame_seth _ _ _ _ _ ⟨1, rfl⟩).trans (frame_setv _ _ _ _ _ ⟨8, rfl⟩))).trans
      (frame_setv _ _ _ _ _ ⟨5, rfl⟩)
  · intro j hj
    have hS1 : ∀ k : Fin 7, 2 ≤ k.val → Sm k ≠ Sm 1 := fun k hk e => by
      have := Sm.injective e; rw [this] at hk; simp at hk
    rw [WState.setv_st, hσ2]
    simp only [WState.setv_st, WState.seth_st]
    fin_cases j
    · simp at hj
    · simp at hj
    · exact ⟨0, i1C⟩
    · exact ⟨xT, i1T⟩
    · exact ⟨xY, i1Y⟩
    · exact ⟨xA, i1A⟩
    · exact ⟨xS, i1S⟩

end Inner

end NearCubicWires.WireExponent3_5.PrimAsm.SBTau
