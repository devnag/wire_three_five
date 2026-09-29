import Proof.Wire_3_5.Primitive.SeedFix.W6Y

/-! # W6, part 26: the modulus, then the fourteen numbers on their ports

P3:2121-2157 (the modulus `p = GF.firstPrimitive ℓ₀`, port `19`) and P3:2543-2558 (the fourteen numbers in unary, ports
`3 … 16`): the docked search (`gf_phase`) and the outputs (`out_exec`), chained as steps:
* `tail2M`, **`tail2_run`**: `sMod = frame (binary ℓ₀ p)`, `sVal k = 1^{v k}` (`v 13 = p`), every stream off the search's
  streams and `sVal` as found.

Paper quantities of the main type: the modulus and the fourteen numbers on their ports. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (cap : ℕ)

noncomputable def tail2M := Composition.machine gfM outW.toProg.compile

theorem sVal_ne_srT (k : Fin 14) (j : Fin 15) : srT j ≠ sVal k := by
  intro h; have := congrArg Fin.val h; fin_cases j <;> simp [srT, sVal] at this <;> omega

theorem sVal_ne_sMod (k : Fin 14) : sVal k ≠ sMod := by
  intro h; have := congrArg Fin.val h; simp [sVal, sMod] at this; omega

theorem tail2_run (σ : WL) (ℓ : ℕ) (v : Fin 14 → ℕ) (hL : σ.val 65 = ℓ) (h1 : 1 ≤ ℓ) (z66 : σ.val 66 = 0)
    (z75 : σ.val 75 = 0) (z76 : σ.val 76 = 0) (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (z79 : σ.val 79 = 0)
    (hop : σ.val qOP = 0) (hs : ∀ j, σ.st (srT j) = [] ∧ σ.sh (srT j) = 0)
    (hsv : ∀ k, σ.st (sVal k) = [] ∧ σ.sh (sVal k) = 0) (hb : 2 ^ (ℓ + 1) + 2 * ℓ + 4 ≤ cap)
    (hv : ∀ k : Fin 14, k ≠ 13 → σ.val (outReg k) = v k) (hv13 : v 13 = GF.firstPrimitive ℓ)
    (hbv : ∀ k, 2 * v k + 4 ≤ cap) :
    Step tail2M ((20 * (4 * (opU cap + 1) + 1) + 1 + GF2.searchCost ℓ + 1 + (opU cap + 2 * (ℓ + 2) * (40 * 2 ^ ℓ + 40)))
        + 1 + 14 * (4 * (opU cap + 1) + 1))
      (wenc cap σ).H (wenc cap σ).A (wenc cap (outSt (⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st, Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩ : WL) v)).H (wenc cap (outSt (⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st, Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩ : WL) v)).A := by
  have g := gf_phase cap σ ℓ hL h1 z66 z75 z76 z77 z78 z79 hop hs hb
  have o := out_exec cap (⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st, Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩ : WL) v (fun k => by
      by_cases hk : k = 13
      · subst hk; rw [hv13]; show Function.update σ.val 66 (GF.firstPrimitive ℓ) 66 = _; rw [Function.update_self]
      · show Function.update σ.val 66 (GF.firstPrimitive ℓ) (outReg k) = v k
        rw [Function.update_of_ne (by fin_cases k <;> simp_all [outReg] <;> decide)]
        exact hv k hk)
    (fun k => ⟨by
        show (gfQ σ ℓ).st (sVal k) = []
        rw [(gfQ_other σ ℓ (sVal k) (fun j => sVal_ne_srT k j)).1]; exact (hsv k).1,
      by
        show Function.update (gfQ σ ℓ).sh sMod (2 * ℓ) (sVal k) = 0
        rw [Function.update_of_ne (sVal_ne_sMod k), (gfQ_other σ ℓ (sVal k) (fun j => sVal_ne_srT k j)).2]
        exact (hsv k).2⟩)
    (by show Function.update σ.val 66 (GF.firstPrimitive ℓ) qOP = 0; rw [Function.update_of_ne (by decide)]; exact hop)
    (by show Function.update σ.val 66 (GF.firstPrimitive ℓ) 77 = 0; rw [Function.update_of_ne (by decide)]; exact z77)
    (by show Function.update σ.val 66 (GF.firstPrimitive ℓ) 78 = 0; rw [Function.update_of_ne (by decide)]; exact z78) hbv
  exact g.seq (WExec.exec cap o).step

theorem tail2_st_val (σ : WL) (ℓ : ℕ) (v : Fin 14 → ℕ) (k : Fin 14) :
    (outSt (⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st, Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩ : WL) v).st (sVal k) = List.replicate (v k) true := outSt_val _ v k

theorem tail2_st_mod (σ : WL) (ℓ : ℕ) (v : Fin 14 → ℕ) :
    (outSt (⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st, Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩ : WL) v).st sMod = frame (binary ℓ (GF.firstPrimitive ℓ)) := by
  rw [outSt_other _ v sMod (fun k => sVal_ne_sMod k)]
  show (gfQ σ ℓ).st (srT 11) = _
  show RecoveryRootRound.install srT (srSt σ ℓ).st (GF2.srBank ℓ (2 * ℓ + 2) J00 false (2 ^ ℓ)) (srT 11) = _
  rw [RecoveryRootRound.install_slot _ srT_inj]
  exact GF2.srBank_out ℓ (2 * ℓ + 2) J00 false

theorem tail2_st_other (σ : WL) (ℓ : ℕ) (v : Fin 14 → ℕ) (s : Fin 192) (h1 : ∀ j, srT j ≠ s) (h2 : ∀ k, sVal k ≠ s) :
    (outSt (⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st, Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩ : WL) v).st s = σ.st s := by
  rw [outSt_other _ v s h2]
  exact (gfQ_other σ ℓ s h1).1

end NearCubicWires.WireExponent3_5.PrimT.W6
