import ENP.UStage
import Proof.MachineModel.ClockJoin
import W3.Recovery3.Bundle

-- Adapted from the gates module `Recovery.AfterParts` to the narrow bundle `W3.Recovery3.{WS,WP}`.

/-!
# The recovery after the refuter: statements of the helper parts

The near-cubic-gates paper's uniform recovery (sec:all-lengths): "The choices of sec:gadget-transfer are recovered in three stages, by prefix
self-reduction on SAT formulas of size `2^{O(q)}`." The after-prefix program (`Recovery3.AfterSupply`) runs stages 1
and 3 (`ENP.UStage`) on a unary workspace `1^W`; its cost bound `C (2^n + 1)^E` needs

* `UCostPoly d`: one stage costs at most `K (W + 1)^e` once `W` covers the stage's workspace (the three hypotheses of
  `ENP.UStage.stage_run`) — "formulas of size `2^{O(q)}`";
* `UNeedPoly d`: that workspace is at most `K (2^R + 1)^e` (`R = q`, the listed table has `2^w ≤ 2^R` entries).

and two small machines of the program: `NuDonor` (`frame x ↦ 1^{⌊log₂ |x|⌋}`, i.e. `1^ν` from the source input
`z ∈ {0,1}^{2^ν}`; the A-run's port `nIn`, the near-cubic-gates paper's fixed weak machine "the weak machine first rejects unless `N = 2^ν`") and
`Unframe` (`frame d ↦ d`: proof 1's canonical→native converter returns the framed descriptor, the A-run reads the raw
`PCPPNative.descriptor B*_src`, the near-cubic-gates paper's uniform recovery "the algorithm of imp:short-pcp is run deterministically on `⟨B*_src⟩_ν`").
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery3.After

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.ENP

/-- A one-port input bank: `w` on tape `i`, every other tape blank. -/
def oneBank {t : ℕ} (i : Fin t) (w : List Bool) : Fin t → List Bool := fun j => if j = i then w else []

/-- **Stage cost** (paper §11.6, "SAT formulas of size `2^{O(q)}`"): a listed-pairs stage costs at most `K (W+1)^e`
whenever `W` satisfies the workspace hypotheses of `ENP.UStage.stage_run`. -/
def UCostPoly (d : ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (w R W : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n),
    vals.length = 2 ^ w → 0 < oracleSizeBound d R →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ W →
    (DedupBytes.fields (unitPCP w vals)).length ≤ W → 2 ^ R ≤ W →
    UStage.cost d w R W vals hw x ≤ K * (W + 1) ^ e

/-- **Stage workspace** (paper §11.6): the workspace a listed-pairs stage needs is polynomial in `2^R`. -/
def UNeedPoly (d : ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (w R : ℕ) (vals : List Bool), w ≤ R → vals.length = 2 ^ w →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length +
      (DedupBytes.fields (unitPCP w vals)).length + 2 ^ R ≤ K * (2 ^ R + 1) ^ e

/-- **`1^ν`** (paper §11.4, `N = 2^ν`): one machine from `frame x` to `1^{⌊log₂ |x|⌋}` within `K (|x| + 1)` steps. -/
structure NuDonor where
  t : ℕ
  st : ℕ
  M : Machine t st
  inp : Fin t
  outp : Fin t
  ne : inp ≠ outp
  K : ℕ
  run : ∀ x : List Bool, ∃ out, ClockJoin.ReadyRun M (K * (x.length + 1)) (oneBank inp (RepairOrdinary.frame x)) out ∧
    out outp = List.replicate (Nat.log 2 x.length) true

/-- **Unframe** (paper §11.6, the raw descriptor of `B*_src` for the imported constructor): one machine from
`frame d` to `d` within `K (|d| + 1)` steps. -/
structure Unframe where
  t : ℕ
  st : ℕ
  M : Machine t st
  src : Fin t
  dst : Fin t
  ne : src ≠ dst
  K : ℕ
  run : ∀ d : List Bool, ∃ out, ClockJoin.ReadyRun M (K * (d.length + 1)) (oneBank src (RepairOrdinary.frame d)) out ∧
    out dst = d

end NearCubicGates.Close.Recovery3.After
