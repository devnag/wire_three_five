import Proof.Wire_3_5.UnionMachine.FrontAtomDecoder
import Proof.Wire_3_5.UnionMachine.FrontLoopKit
import Proof.Wire_3_5.Transfer.FoldLoop
import Proof.CaseAnalysis.FinalCacheRewind
import Proof.SourceAssembly.SourceFactorSelRunBound

/-! # C6 front, U5: one decoder run that may reject, rewound (the description flags, P3:3670, 3083-3094)

`lem:primitive`'s precondition bounds every circuit's description (`descriptionBits ≤ (n+1)^descDeg`), and v8's
decoder at policy `L` decides exactly that on a decodable atom (base `CloseoutRowsCircuitMeaning.threshold_exact` /
`symmetric_exact`: passing ↔ decoded ∧ wires ≤ `W` ∧ `descriptionBits ≤ L`). The union front runs it on EVERY grid
atom, so the run may reject, and a rejecting run fixes only the raw tape, the driver and the flag. This module wraps
the decoder so that every run ends at zero heads (base's cold rewind `CloseoutFinalC10ColdCacheRewind.machine`, a
recording log on one added tape) and bounds every tape it leaves (base `SourceFactorSel.RunBound.runFrom_bound`), on
`false`-padded banks (base `ZeroPadding`).

* `posM`: the template's head onto its first `1` (`counterStep`, docked).
* **`decR m`** = rewind (`posM` ; decoder); **`decR_step`**: from the padded decoder input at zero heads to a padded
  exit at zero heads whose flag bit is the verdict `passedM`, raw tape and driver restored, every tape bounded.

Paper quantity: the verdict `descriptionBits ≤ L` of one guessed atom. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontDescDecoder
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

/-! ## Padding and steps -/

/-- **A step survives `false`-padding.** -/
theorem Step.pad {t s : ℕ} {p : Machine t s} {n : ℕ} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step p n H A H' A') (cap : Fin t → ℕ) :
    Step p n H (fun i => ZeroPadding.pad (cap i) (A i)) H' (fun i => ZeroPadding.pad (cap i) (A' i)) := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  obtain ⟨r', hr', hf, hsteps, -⟩ := ZeroPadding.run_config p cap n _ r hr
  refine ⟨r', ?_, ?_, ?_, by omega⟩
  · have e : ZeroPadding.config cap (⟨p.start, H, A⟩ : Configuration t s) =
        ⟨p.start, H, fun i => ZeroPadding.pad (cap i) (A i)⟩ := rfl
    rw [← e]; exact hr'
  · rw [hf]; exact hh
  · rw [hf]; funext i; simp only [ZeroPadding.config, ht]

theorem Step.congrOut {t s : ℕ} {p : Machine t s} {n : ℕ} {H0 H1 H2 : Fin t → ℕ} {A0 A1 A2 : Fin t → List Bool}
    (h : Step p n H0 A0 H1 A1) (e1 : H1 = H2) (e2 : A1 = A2) : Step p n H0 A0 H2 A2 := by
  subst e1; subst e2; exact h

/-! ## The template's head -/

/-! ## The decoder behind the head positioning, rewound -/

end NearCubicWires.WireExponent3_5.UnionMachine.FrontDescDecoder
