import Proof.MachineModel.BlockUnaryCalc
import Proof.Packets.PacketsClog
import Proof.Packets.PacketsTouch

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

/-! ## Padding -/

theorem step_pad {t s n : ℕ} {p : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p n H A H' A') (cap : Fin t → ℕ) :
    Step p n H (fun i => ZeroPadding.pad (cap i) (A i)) H' (fun i => ZeroPadding.pad (cap i) (A' i)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨u, hu, hf, hsteps, _⟩ := ZeroPadding.run_config p cap n _ r hr
  refine ⟨u, hu, ?_, ?_, by omega⟩
  · rw [hf]; exact hh
  · rw [hf]; funext i; simp only [ZeroPadding.config, ht]

/-! ## Unary product -/

theorem tpl_step (n : ℕ) :
    Step (RepairSource.ProjectionNormalization.DimensionTemplate.machine false) (2 * n + 8) (fun _ => 0)
      ![List.replicate n true, [], []] (fun _ => 0)
      ![List.replicate n true, UnaryTemplate.tape n, List.replicate (n + 3) false] := by
  have h := CloseoutFinalSelector.step_of_clock (RepairSource.ProjectionNormalization.DimensionTemplate.ready false n)
  simpa [RepairSource.ProjectionNormalization.DimensionTemplate.input,
    RepairSource.ProjectionNormalization.DimensionTemplate.output] using h

theorem pad_tpl (y : ℕ) : ZeroPadding.pad (y + 2) (false :: List.replicate y true) = UnaryTemplate.tape y := by
  simp [ZeroPadding.pad, UnaryTemplate.tape]

theorem prod_step (x y : ℕ) :
    Step ClockUnaryProduct.machine (2 * (x * (2 * y + 3) + 2) + 2) (fun _ => 0)
      ![List.replicate x true, UnaryTemplate.tape y, [], []] (fun _ => 0)
      ![List.replicate x true, UnaryTemplate.tape y, List.replicate (x * y) true,
        List.replicate (x * (2 * y + 3) + 2) false] := by
  have h0 := UnaryCalc.product_step x y
  have hi : (Fin.addCases (motive := fun _ : Fin (3 + 1) => List Bool)
      ![List.replicate x true, false :: List.replicate y true, []] (fun _ : Fin 1 => [])) =
      ![List.replicate x true, false :: List.replicate y true, [], []] := by
    funext i; fin_cases i <;> rfl
  rw [hi] at h0
  have h := step_pad h0 ![0, y + 2, 0, 0]
  have e1 : (fun i => ZeroPadding.pad (![0, y + 2, 0, 0] i)
      (![List.replicate x true, false :: List.replicate y true, [], []] i)) =
      ![List.replicate x true, UnaryTemplate.tape y, [], []] := by
    funext i; fin_cases i <;> simp [pad_tpl]
  have e2 : (fun i => ZeroPadding.pad (![0, y + 2, 0, 0] i)
      (![List.replicate x true, false :: List.replicate y true, List.replicate (x * y) true,
        List.replicate (x * (2 * y + 3) + 2) false] i)) =
      ![List.replicate x true, UnaryTemplate.tape y, List.replicate (x * y) true,
        List.replicate (x * (2 * y + 3) + 2) false] := by
    funext i; fin_cases i <;> simp [pad_tpl]
  rw [e1, e2] at h
  exact h



/-! ## Polynomially costed composition -/

/-! ## The input length -/

namespace LenM

end LenM

end
end NearCubicWires.PacketsGlue.RequestMeta

