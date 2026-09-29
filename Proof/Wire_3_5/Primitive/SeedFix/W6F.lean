import Proof.Wire_3_5.Primitive.SeedFix.W6E

/-! # W6, part 6: `|𝒢|` and the magnitude exponent by proof 1's program

P3:2543-2558 (row:threshold-rows): `|𝒢|` and the family's magnitude exponent are computed by proof 1's verified
program (`PacketsMeta.Prog.prog`) with the tails (`W6Meta.metaC`: `1^{Cv}`, `W6Meta.metaE`:
`1^{clog₂(Fv+1)}`), each run on its own block of 61 streams (`sBC`, `sBE`: the top word on tape `0`, the native word on
tape `2`, blank scratch, the reset counter on tape `60`), wrapped in the masked reset (every head back at `0`) and
docked onto the streams (`DockW.dockS`):
* **`progC_dock`**: block C's tape `1` holds `1^{Cv}`; **`progE_dock`**: block E's tape `1` holds `1^{clog₂(Fv+1)}`;
  every other stream, every register and the cell as found.
The statements stay generic in the request `r` (the concrete THR request is substituted only on the words and the
values: `tw_payOf`, `Cv_thr`, `E_thr`).

Paper quantities of the main types: `|𝒢|` and the magnitude exponent in unary. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.PacketsMeta NearCubicWires.PacketsMeta.Lev NearCubicWires.PacketsMeta.Setup
open NearCubicWires.PacketsMeta.Tail NearCubicWires.PacketsMeta.Prog NearCubicWires.PacketsMeta.Spec
open NearCubicWires.PacketsMeta.Bounds
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.RepairOrdinary.RecoveryRootRound

variable (cap : ℕ)

/-- Block C's tapes. -/
def bC (j : Fin (3 + 57 + 1)) : Fin 192 := sBC ⟨j.val, by omega⟩
/-- Block E's tapes. -/
def bE (j : Fin (3 + 57 + 1)) : Fin 192 := sBE ⟨j.val, by omega⟩

theorem bC_inj : Function.Injective bC := fun a b h => by
  have := congrArg Fin.val h; simp only [bC, sBC] at this; exact Fin.ext (by omega)
theorem bE_inj : Function.Injective bE := fun a b h => by
  have := congrArg Fin.val h; simp only [bE, sBE] at this; exact Fin.ext (by omega)

/-- A block's entry for proof 1's program with its reset counter. -/
theorem blk_in (f1 f2 : List Bool) (L : Fin 61 → List Bool) (h0 : L 0 = f1) (h2 : L 2 = f2)
    (hb : ∀ k : Fin 61, k.val ≠ 0 → k.val ≠ 2 → L k = []) :
    (Fin.addCases (PacketsGlue.RequestMeta.scanIn2 57 f1 f2) (fun _ : Fin 1 => List.replicate 0 false) :
      Fin (3 + 57 + 1) → List Bool) = fun j => L ⟨j.val, by omega⟩ := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun u => ?_) j
  · rw [Fin.addCases_left]
    unfold PacketsGlue.RequestMeta.scanIn2
    by_cases h0' : i.val = 0
    · rw [if_pos h0', show (⟨(Fin.castAdd 1 i).val, _⟩ : Fin 61) = 0 from Fin.ext (by simp [h0']), h0]
    · by_cases h2' : i.val = 2
      · rw [if_neg h0', if_pos h2', show (⟨(Fin.castAdd 1 i).val, _⟩ : Fin 61) = 2 from Fin.ext (by simp [h2']), h2]
      · rw [if_neg h0', if_neg h2', hb _ (by simp [h0']) (by simp [h2'])]
  · rw [Fin.addCases_right, hb _ (by simp) (by simp)]
    rfl

theorem eHin (σ : WL) (tmap : Fin (3 + 57 + 1) → Fin 192) (hsh : ∀ j, σ.sh (tmap j) = 0) :
    (Fin.addCases (fun _ : Fin (3 + 57) => (0 : ℕ)) (fun _ : Fin 1 => 0) : Fin (3 + 57 + 1) → ℕ) =
      fun j => σ.sh (tmap j) := by
  funext j; rw [hsh]; refine Fin.addCases (fun i => ?_) (fun u => ?_) j <;> simp

theorem eHout (H : Fin (3 + 57) → ℕ) :
    (Fin.addCases (fun i : Fin (3 + 57) => if (fun _ => true) i = true then 0 else H i) (fun _ : Fin 1 => (0 : ℕ)) :
      Fin (3 + 57 + 1) → ℕ) = fun _ => 0 := by
  funext j; refine Fin.addCases (fun i => ?_) (fun u => ?_) j <;> simp

/-- The docked block's exit facts. -/
theorem blk_post (σ : WL) (tmap : Fin (3 + 57 + 1) → Fin 192) (hinj : Function.Injective tmap)
    (A1 : Fin (3 + 57) → List Bool) (k : ℕ) (j1 : Fin (3 + 57)) :
    (updS tmap σ (fun _ => 0) (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false))).st
        (tmap (Fin.castAdd 1 j1)) = A1 j1 ∧
      (∀ j, (updS tmap σ (fun _ => 0) (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false))).sh (tmap j) = 0) ∧
      (∀ s, (∀ j, tmap j ≠ s) →
        (updS tmap σ (fun _ => 0) (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false))).st s = σ.st s ∧
        (updS tmap σ (fun _ => 0) (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false))).sh s = σ.sh s) ∧
      (updS tmap σ (fun _ => 0) (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false))).val = σ.val ∧
      (updS tmap σ (fun _ => 0) (Fin.addCases A1 (fun _ : Fin 1 => List.replicate k false))).cell = σ.cell := by
  refine ⟨?_, fun j => ?_, fun s hs => ⟨?_, ?_⟩, rfl, rfl⟩
  · show install tmap σ.st _ (tmap _) = _
    rw [install_slot _ hinj, Fin.addCases_left]
  · show dockH tmap σ.sh _ (tmap j) = 0
    rw [dockH_slot _ hinj]
  · exact install_other _ _ _ _ hs
  · exact dockH_other _ _ _ _ hs

end NearCubicWires.WireExponent3_5.PrimT.W6
