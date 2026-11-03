import Proof.Wire_3_5.FinalPass.S5TLay2

/-! # S5-THR, part 23: the THR numbers on W6's block (P3:2543-2558, 2596-2599, 2150-2157)

The THR path's first docks on the THR half's layout: the fill count `1^{W_p}` copied from the power `xs j₀`
(`plainCopy`), the prep (`p0_dock`: `1^{|carriers|}`, `1^{cap_T}`, `1^V`, `V = W_p + (n+1)^{26}`), then W6
(`w6_dock`: the THR numbers in unary on its ports `3 … 16`, the primes on slot `13`, the level records on port `18`,
the modulus word on port `19`).

* `updS_st_in`, `updS_st_out`, `updS_sh0` (a docked run's exit state, read off);
* `chainAM`, `chainACost`, **`chainA_spec`**.

Paper quantities of the main type: the THR call's numbers `thrNumVals` (`|𝒢|`, `K`, the cutoff, `τ₀`, the fixed
hash's `M, A, B_*, J, t, e, ℓ₀, p`), THR slot `13` (the primes up to the cutoff). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS sTape_val)
open NearCubicWires.WireExponent3_5.PrimThrW.Nums3 (nums3InPorts nums3OutPorts)
open NearCubicWires.SupplierPipeline

section Upd
variable {ns nr t : ℕ}

theorem updS_st_in (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (hout : Fin t → ℕ) (tout : Fin t → List Bool) (j : Fin t) : (updS tmap σ hout tout).st (tmap j) = tout j :=
  install_slot _ hinj _ _ j

theorem updS_st_out (tmap : Fin t → Fin (ns + 1)) (σ : WState ns nr) (hout : Fin t → ℕ) (tout : Fin t → List Bool)
    (i : Fin (ns + 1)) (hi : ∀ j, tmap j ≠ i) : (updS tmap σ hout tout).st i = σ.st i :=
  install_other _ _ _ _ hi

theorem updS_sh0 (tmap : Fin t → Fin (ns + 1)) (hinj : Function.Injective tmap) (σ : WState ns nr)
    (tout : Fin t → List Bool) (hsh : ∀ i, σ.sh i = 0) : ∀ i, (updS tmap σ (fun _ => 0) tout).sh i = 0 := by
  intro i
  show dockH tmap σ.sh (fun _ => 0) i = 0
  by_cases hi : ∃ j, tmap j = i
  · obtain ⟨j, rfl⟩ := hi; rw [dockH_slot _ hinj]
  · rw [dockH_other _ _ _ _ (fun j h => hi ⟨j, h⟩), hsh]

end Upd

section ChainA

end ChainA

end NearCubicWires.WireExponent3_5.FinalPass.S5T
