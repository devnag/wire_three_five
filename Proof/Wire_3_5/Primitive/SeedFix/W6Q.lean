import Proof.Wire_3_5.Primitive.SeedFix.W6P

/-! # W6, part 17: the modulus phase (C1's search docked)

P3:2121-2157 (filt:majorant: the field `GF(2^{ℓ₀})`, its modulus `p` "the first primitive polynomial of degree `ℓ₀`",
`Majorant.refMod = GF.firstPrimitive ℓ₀`): the entry bank (`srPrep_exec`), C1's verified search `GF2.searchM`
(`search_run`, `srBank_out`) docked onto `srT` (`DockW.dockS`), the modulus read back (`pm_exec`, `fp_split`):
* **`gf_phase`**: `sMod = frame (binary ℓ₀ p)` (port `19`), `rPM = 66 = p`, the search's streams bounded residues
  (`≤ 2ℓ₀+2`), every other stream, head, register and the cell as found.

Paper quantity of the main type: the modulus `p = GF.firstPrimitive ℓ₀`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (cap : ℕ)

/-- **The modulus phase**: the entry bank, the search, the modulus read back. -/
noncomputable def gfM :=
  Composition.machine (Composition.machine srPrep.toProg.compile
    (RecoveryFocus.machine (fun j => sTape (nr := 80) (srT j)) GF2.searchM)) pmW.toProg.compile

/-- The search's exit bank on W6's streams. -/
noncomputable def gfQ (σ : WL) (ℓ : ℕ) : WL :=
  updS srT ⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ (fun _ => 0) (GF2.srBank ℓ (2 * ℓ + 2) J00 false (2 ^ ℓ))

theorem gf_phase (σ : WL) (ℓ : ℕ) (h65 : σ.val 65 = ℓ) (h1 : 1 ≤ ℓ) (z66 : σ.val 66 = 0) (z75 : σ.val 75 = 0)
    (z76 : σ.val 76 = 0) (z77 : σ.val 77 = 0) (z78 : σ.val 78 = 0) (z79 : σ.val 79 = 0) (hop : σ.val qOP = 0)
    (hs : ∀ j, σ.st (srT j) = [] ∧ σ.sh (srT j) = 0) (hb : 2 ^ (ℓ + 1) + 2 * ℓ + 4 ≤ cap) :
    Step gfM (20 * (4 * (opU cap + 1) + 1) + 1 + GF2.searchCost ℓ + 1 + (opU cap + 2 * (ℓ + 2) * (40 * 2 ^ ℓ + 40)))
      (wenc cap σ).H (wenc cap σ).A
      (wenc cap ⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st,
        Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩).H
      (wenc cap ⟨Function.update (gfQ σ ℓ).sh sMod (2 * ℓ), (gfQ σ ℓ).st,
        Function.update σ.val 66 (GF.firstPrimitive ℓ), σ.cell⟩).A := by
  have hpos : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hp2 : 2 ^ (ℓ + 1) = 2 * 2 ^ ℓ := by rw [pow_succ]; ring
  have s1 := (WExec.exec cap (srPrep_exec cap σ ℓ h65 h1 z75 z76 z77 z78 hop hs (by omega))).step
  have h' : Step GF2.searchM (GF2.searchCost ℓ) (fun j => (⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ : WL).sh (srT j))
      (fun j => (⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ : WL).st (srT j)) (fun _ => 0)
      (GF2.srBank ℓ (2 * ℓ + 2) J00 false (2 ^ ℓ)) := by
    have e1 : (fun j => (⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ : WL).sh (srT j)) = fun _ => 0 :=
      funext fun j => (hs j).2
    have e2 : (fun j => (⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ : WL).st (srT j)) =
        GF2.srIn ℓ (2 * ℓ + 2) J00 0 0 false false false := funext fun j => srSt_srIn σ ℓ h1 j
    rw [e1, e2]
    exact GF2.search_run ℓ (2 * ℓ + 2) J00 0 0 false false false h1 le_rfl
  have s2 := dockS cap srT srT_inj (⟨σ.sh, (srSt σ ℓ).st, σ.val, σ.cell⟩ : WL) h'
  have hQst : (gfQ σ ℓ).st sMod = frame (binary ℓ (GF.firstPrimitive ℓ)) := by
    show install srT (srSt σ ℓ).st (GF2.srBank ℓ (2 * ℓ + 2) J00 false (2 ^ ℓ)) (srT 11) = _
    rw [install_slot _ srT_inj]
    exact GF2.srBank_out ℓ (2 * ℓ + 2) J00 false
  have hQsh : (gfQ σ ℓ).sh sMod = 0 := by
    show dockH srT σ.sh (fun _ => 0) (srT 11) = 0
    rw [dockH_slot _ srT_inj]
  have s3 := (WExec.exec cap (pm_exec cap (gfQ σ ℓ) ℓ (GF.firstPrimitive ℓ) h65 hQst hQsh z66 z77 z78 z79 (by omega))).step
  rw [fp_split] at s3
  exact (s1.seq s2).seq s3

/-- Every stream off the search's is as found. -/
theorem gfQ_other (σ : WL) (ℓ : ℕ) (s : Fin 192) (h : ∀ j, srT j ≠ s) :
    (gfQ σ ℓ).st s = σ.st s ∧ (gfQ σ ℓ).sh s = σ.sh s := by
  constructor
  · show install srT (srSt σ ℓ).st _ s = σ.st s
    rw [install_other _ _ _ _ h]
    exact srSt_other σ ℓ s h
  · show dockH srT σ.sh _ s = σ.sh s
    exact dockH_other _ _ _ _ h

end NearCubicWires.WireExponent3_5.PrimT.W6
