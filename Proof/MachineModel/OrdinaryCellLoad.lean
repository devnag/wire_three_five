import Proof.MachineModel.OrdinaryFrameLoad

/-! Load a framed rank from an advancing source stream, then execute the
reusable cell emitter. Both global cursors survive the bounded local work. -/
namespace NearCubicWires.RepairOrdinary.CellLoad
open LocalBitMultitape SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def loaderInput (source : List Bool) (position : ℕ) (backing : List Bool) (width : ℕ) : Configuration 3 4 :=
  ⟨0, ![position, 0, 0], ![source, backing, List.replicate (2 * width + 1) false]⟩

theorem loader_run (pre bits suffix backing : List Bool) (hb : backing.length ≤ 2 * bits.length + 1) :
    ∃ r : ExecutionReceipt 3 4,
      runFrom FrameLoad.machine (4 * bits.length + 3)
        (loaderInput (pre ++ frame bits ++ suffix) pre.length backing bits.length) = some r ∧
      r.final = FrameLoad.reset 3 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (frame bits) 0 (2 * bits.length + 1) ∧ r.steps = 4 * bits.length + 3 ∧
      r.peakTapeCells ≤ (pre ++ frame bits ++ suffix).length + 8 * bits.length + 4 := by
  obtain ⟨base, hbRun, hbf, hbs, hbp⟩ := FrameLoad.load_run pre bits suffix backing hb
  let caps : Fin 3 → ℕ := ![0, 0, 2 * bits.length + 1]
  obtain ⟨r, hr, hf, hs, hp⟩ := ZeroPadding.run_config FrameLoad.machine caps _ _ base hbRun
  have hi : ZeroPadding.config caps (FrameLoad.scan 0 (pre ++ frame bits ++ suffix) pre.length [] backing) =
      loaderInput (pre ++ frame bits ++ suffix) pre.length backing bits.length := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, caps, FrameLoad.scan, loaderInput,
        StablePartition.Workspace.overlay, ZeroPadding.pad]
  have he : ZeroPadding.config caps (FrameLoad.reset 3 (pre ++ frame bits ++ suffix)
      (pre.length + 2 * bits.length + 1) (frame bits) 0 (2 * bits.length + 1)) =
      FrameLoad.reset 3 (pre ++ frame bits ++ suffix) (pre.length + 2 * bits.length + 1)
        (frame bits) 0 (2 * bits.length + 1) := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, caps, FrameLoad.reset, ZeroPadding.pad]
  refine ⟨r, by rw [hi] at hr; exact hr, by rw [hf, hbf, he], hs.trans hbs, ?_⟩
  simp [ZeroPadding.cells, caps, Fin.sum_univ_succ] at hp
  omega

def layout : Fin 10 ≃ Fin 10 where
  toFun := ![9, 4, 3, 0, 1, 2, 5, 6, 7, 8]
  invFun := ![3, 4, 5, 2, 1, 6, 7, 8, 9, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem layout_inverse : (layout.symm : Fin 10 → Fin 10) = ![3, 4, 5, 2, 1, 6, 7, 8, 9, 0] := rfl


end NearCubicWires.RepairOrdinary.CellLoad
