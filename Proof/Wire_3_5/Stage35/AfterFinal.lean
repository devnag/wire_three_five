import Proof.Wire_3_5.Stage35.AfterMain
import Proof.Wire_3_5.Stage35.AfterHead2
import Proof.Wire_3_5.Stage35.After9Mid
import Proof.Wire_3_5.Stage35.After4Tail
import Proof.Wire_3_5.Stage35.After1HeadRun
import Proof.Wire_3_5.Stage35.Bundle
import ENP.TStage

-- Port of W3 Recovery3/AfterFinal.lean with the copies schedule (Stage35.WQ).

/-!
# The recovery after the refuter: the deliverable

The near-cubic-gates paper's uniform recovery (sec:all-lengths): "For completeness, all canonical choices are recoverable in E^NP" — stage 1 (`B*_src`
or `X_z`), the imported constructor on `⟨B*_src⟩_ν` and stage 2 (`O*` or the zero slice), stage 3 (`B*_pf` or `Ô*`),
then "Run the general amplifier on `X_z` or `Ô*`" or, "in the small-oracle branch, the honest PCPP proof and each AND
helper". `afterSupply_of_head`: `Recovery3.AfterSupply` from the stage-2 producer, the composite (`Setup.CompU`, for
the Case 2 producer) and the first half of the head (pieces 0–10).
-/

set_option autoImplicit false


namespace NearCubicGates.Close.Recovery3.After

open Stage35 _root_.NearCubicGates.Close _root_.NearCubicGates.Close.Recovery3 _root_.NearCubicGates.Close.Recovery3.After

open W3.Recovery3 NearCubicGates.Close.Recovery

open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- **The after-prefix program from the Case-2 kit** (the near-cubic-wires paper, Lemma C.10; gates `afterSupply_of`):
stage 1, the A-run on `⟨B*_src⟩_ν`, stage 2 (`ENP.tStageRuns`), stage 3, then Case 1 (Hard word on `X_z`, Hard oracle on
`Ô*`, gates `C1.caseOneRuns`), the zero slice, or Case 2 (the Case-2 kit `ht`). -/
theorem afterRun_of (s : WS35) (P : NearCubicWires.RepairRepresentation.PointwisePCPPAlgorithm) (g : WQ)
    (hR : AfterReady s g) (ht : HTKit s P g) : Nonempty (AfterRun s P g) :=
  afterRun_of_segs (fun _ _ _ K c => headRuns_of K c (headTwoRuns K c)) (fun _ _ _ K c => midRuns K c)
    (fun _ _ _ K c => tailRuns K c) ENP.tStageRuns s P g hR ht

end NearCubicGates.Close.Recovery3.After

