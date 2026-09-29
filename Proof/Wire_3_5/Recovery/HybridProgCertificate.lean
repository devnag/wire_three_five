import Proof.Wire_3_5.Recovery.HybridProgChoose
import Proof.Wire_3_5.Recovery.HybridProgRuns
import Proof.Wire_3_5.Assembly.FreeRecovery

/-! # The hybrid slice is in `E^NP` (P3:3758-3759; D1.6 D)

Realizes "The resulting slice is computable in `E^NP`. Run the fixed refuter [...] on the source length `N_{a(n)}`"
(P3:3758-3759) for the recovered language of the hybrid route (`recLanguageCut2`): the hybrid program runs on
every input length within `C·(2^n+1)^E` (`runs`, `exists_budget`), so base's `Closeout.certificate_of_runs` gives an
ordinary `E^NP` certificate of its target (`certificate`, base's `CommonProgramCertificate` restated); with the onset
above `2^{n₀}` the target is `recLanguageCut2` at cutoff = onset (`target_eq`); hence **`certGen`**: `CertGen l`, the
residual of leaf R's checked plan (`Split.recoveryLeafF_of_certGen`).

Paper quantity of the main type (`certGen`): the `E^NP` certificate of the recovered hybrid language. -/

set_option autoImplicit false

namespace NearCubicWires.RepairSource.HybridProgram
open LocalBitMultitape RepairOrdinary SourceInterfaces CloseoutLanguage
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Transfer
noncomputable section

/-- **One ordinary `E^NP` certificate of the hybrid program's target** (base's `certificate`). -/
theorem certificate (p : Parameters) (M : OrdinaryWeakMachine) (c : Constants) (sup : Suppliers p M c) :
    Nonempty (OrdinaryENPCertificate RecoveryOracle.correctedSat (target p M)) := by
  obtain ⟨C, E, h⟩ := exists_budget p c
  refine ⟨Closeout.certificate_of_runs (target p M) (program p) C E ?_⟩
  intro n point
  have hb := h (List.ofFn point)
  simp only [List.length_ofFn] at hb
  exact (runs p M c sup n point).enlarge hb

theorem sliceIdx_le (l : Literals) (G : Split.Gate) (kclk n : ℕ) :
    sliceIdx (gateZeta_pos l) (gateZeta_lt l) kclk G.Apad (recDG l) n ≤ n := by
  rw [sliceIdx_eq]
  exact Nat.findGreatest_le n

/-- **The target is the recovered language** at cutoff = onset, once the onset is above `2^{n₀}`. -/
theorem target_eq (p : Parameters) (M : OrdinaryWeakMachine) (n₀ : ℕ) (h2 : 2 ^ n₀ ≤ p.onset)
    (hn₀ : ∀ n, n₀ ≤ n → index p n = sliceIdx (gateZeta_pos p.l) (gateZeta_lt p.l) p.kclk p.G.Apad (recDG p.l) n) :
    recLanguageCut2 p.l p.G p.kclk M p.onset = target p M := by
  funext n x
  rw [recLanguageCut2_eq]
  by_cases hn : n₀ ≤ n
  · rw [← hn₀ n hn]
    rfl
  · have hi : index p n < n₀ := lt_of_le_of_lt (CertPrefix.prefixS_le _ _ _ _ _ n) (by omega)
    have hs : sliceIdx (gateZeta_pos p.l) (gateZeta_lt p.l) p.kclk p.G.Apad (recDG p.l) n < n₀ :=
      lt_of_le_of_lt (sliceIdx_le p.l p.G p.kclk n) (by omega)
    have hpi : 2 ^ index p n < 2 ^ n₀ := Nat.pow_lt_pow_right (by norm_num) hi
    have hps : 2 ^ sliceIdx (gateZeta_pos p.l) (gateZeta_lt p.l) p.kclk p.G.Apad (recDG p.l) n < 2 ^ n₀ :=
      Nat.pow_lt_pow_right (by norm_num) hs
    rw [if_neg (by omega), inactive_target p M n x (by unfold length; omega)]

/-- **D1.6: `CertGen l`**, the residual of leaf R's plan. -/
theorem certGen (l : Literals) : Split.CertGen l := by
  intro kclk M hM
  have hApad : (gateSource l).degrees.proofLog + 6 ≤ (Split.gate0 l (Split.freeSat l)).Apad := le_rfl
  obtain ⟨e1, e2, e3, f1, f2, f3, f4, onset, Aw, Bw, Aq, Bq, refuter, c, ⟨n₀, h2, hn₀⟩, sup⟩ :=
    choose l (Split.gate0 l (Split.freeSat l)) hApad kclk M hM
  refine ⟨onset, ?_⟩
  have e := target_eq ⟨l, Split.gate0 l (Split.freeSat l), kclk, 0, e1, e2, e3, f1, f2, f3, f4, onset, Aw, Bw, Aq, Bq,
    refuter⟩ M n₀ h2 hn₀
  exact e ▸ certificate _ M c sup

end

end NearCubicWires.RepairSource.HybridProgram
