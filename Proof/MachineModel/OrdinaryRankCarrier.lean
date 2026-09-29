import Proof.MachineModel.OrdinaryRankLoop

/-! Complete rank labelling in the shared ordinary carrier. Only the framed
record stream is supplied: every work tape really starts empty. -/
namespace NearCubicWires.RepairOrdinary.RankCarrier
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem binary_zero (width : ℕ) : SignedSortKey.binary width 0 = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [SignedSortKey.binary, ih, List.replicate_succ]

def capacity (width : ℕ) : Fin 5 → ℕ := fun i => if i.val < 2 then 0 else width

theorem raw_run (width : ℕ) (words : List (List Bool))
    (hw : ∀ word ∈ words, word.length = width) (hn : words.length < 2 ^ width) :
    ∃ r : ExecutionReceipt 5 20,
      run RankLoop.machine (words.length * (7 * width + 14) + 1)
        (SourceHandoff.sourceTapes (RankLoop.stream words)) = some r ∧
      r.final.tapes 1 = RankLoop.labels width 0 words ++ [false] ∧
      r.steps ≤ words.length * (7 * width + 14) + 1 ∧
      r.peakTapeCells ≤ (RankLoop.stream words).length + words.length * (4 * width + 1) + 10 * width + 3 := by
  obtain ⟨base, hb, hf, hs, hp⟩ := RankLoop.loop_run width words [] [] 0 hw (by simpa using hn)
  have hi : ZeroPadding.config (capacity width)
      (initialConfiguration RankLoop.machine (SourceHandoff.sourceTapes (RankLoop.stream words))) =
      RankPlacement.config (RecordController.test 18) (RankLoop.stream words) 0 [] (SignedSortKey.binary width 0) 0
        (List.replicate width false) 0 (List.replicate width false) 0 := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config, capacity, initialConfiguration, SourceHandoff.sourceTapes,
        RankPlacement.config, ZeroPadding.pad, binary_zero]
  have hb' : runFrom RankLoop.machine (words.length * (7 * width + 14) + 1)
      (ZeroPadding.config (capacity width)
        (initialConfiguration RankLoop.machine (SourceHandoff.sourceTapes (RankLoop.stream words)))) = some base := by
    rw [hi]
    simpa using hb
  obtain ⟨r, hr, hrf, hrs, hrp⟩ := ZeroPadding.run_unpad RankLoop.machine (capacity width) _ _ base hb'
  refine ⟨r, hr, ?_, hrs.le.trans hs, ?_⟩
  · have he := congrArg (fun c : Configuration 5 20 => c.tapes 1) hrf
    rw [hf] at he
    simpa [ZeroPadding.config, capacity, RankPlacement.config] using he
  · simp only [List.nil_append, List.length_nil, Nat.add_zero] at hp
    exact hrp.trans hp

end NearCubicWires.RepairOrdinary.RankCarrier
