import Proof.Wire_3_5.Recovery.HybridAssembly

/-! # The recovery leaf at the re-pinned setup `S₂` with the hybrid language (P3:3699-3756, 3831-3852; D1.6)

Realizes the end of the transfer (P3:3740-3742, 3831-3852) for the hybrid recovered language: the
slice at `n` is the hybrid core of the selected source index `a(n)` (the case split and Case 1 at the refuter
hierarchy's native outer PCP, Case 2 at `S₂`'s padded request), at the refuter's output for the union machine at
`S₂`. This is the language whose `E^NP` certificate the hybrid program computes; `recoveryLeaf` (at `S₁`) is
unchanged.

Paper quantities:
* **`recLanguage2`** and **`recLanguageCut2`** (`false` while `2^{a(n)}` is below a cutoff);
* **`eventually_slice2`**: past an onset, every `SYM∘THR` (`THR∘THR`) circuit on `n` inputs within `⌊w_S(q)⌋`
  (`⌊w_T(q)⌋`) wires agrees with the slice below `1/2 + e_{t(q)}` (the native width `R = R(2^{a(n)})` satisfies
  `a(n) + 1 ≤ R ≤ q ≤ K₁R`);
* **`recLanguageCut2_hard`**: `ThrHardAt (1/8) (11/2)` and `SymHardAt (1/8) (9/2)` at every positive multiplier;
* **`recoveryLeaf2 l G hG cert2 : Split.RecoveryLeaf G (unionSetupS2 l G)`**, the certificate for `recLanguageCut2`
  being the one input (D1.6's program). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule
open NearCubicWires.RepairSource.CloseoutLanguage (core clauseWidth)
open Filter

/-- **The hybrid recovered language**: at length `n`, the hybrid core of the selected source index at the refuter's
output for `M` at `2^{a(n)}`, with `t(q)+1` copies and the clause width at `q = q(2^{a(n)})`. -/
noncomputable def recLanguage2 (l : Literals) (G : Split.Gate) (kclk : ℕ) (M : OrdinaryWeakMachine) : Language :=
  fun n => hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l)
    (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
    ((recRefuter l kclk).output M (2 ^ (recSched l G kclk).sourceIdx n))
    (recCopies (gateZeta_pos l) (gateZeta_lt l) (recWidth l G kclk n)) (clauseWidth (recDG l) (recWidth l G kclk n)) n

/-- **The recovered language with a cutoff**: `false` while `2^{a(n)}` is below the cutoff. -/
noncomputable def recLanguageCut2 (l : Literals) (G : Split.Gate) (kclk : ℕ) (M : OrdinaryWeakMachine) (cutoff : ℕ) :
    Language :=
  fun n => if cutoff ≤ 2 ^ (recSched l G kclk).sourceIdx n then recLanguage2 l G kclk M n else fun _ => false

section Leaf2

end Leaf2

/-- **The hybrid slice in terms of the computed parameters** (the specification the prefix stage must meet): the index
`a(n)` by the upward scan, the width `q(2^{a(n)})` in closed form, the copies `t(q)+1`, the clause width, and the
refuter's output at `2^{a(n)}`. -/
theorem recLanguageCut2_eq (l : Literals) (G : Split.Gate) (kclk : ℕ) (M : OrdinaryWeakMachine) (cutoff n : ℕ) :
    recLanguageCut2 l G kclk M cutoff n =
      if cutoff ≤ 2 ^ sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n then
        hybridCore (recPCP l kclk).pcp (paddedWidth l G (refH l kclk)) (fun _ => le_max_left _ _) (gatePCPP l)
          (selectedAmplifier l.eightSources.amplification (recOracleDeg l))
          ((recRefuter l kclk).output M (2 ^ sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n))
          (sched (gateCParams1 l).ζ (gateZeta_pos l) (gateZeta_lt l)
            (Lq (widthAt kclk G.Apad (sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n))) + 1)
          (clauseWidth (recDG l) (widthAt kclk G.Apad (sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n)))
          n
      else fun _ => false := by
  unfold recLanguageCut2 recLanguage2 recWidth recSched
  rw [sliceIdx_eq, widthAt_eq]
  rfl

end NearCubicWires.WireExponent3_5.Transfer
