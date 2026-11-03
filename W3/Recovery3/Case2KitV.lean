import W3.Recovery3.Case2Out
import Recovery.HardTableRuns
import W3.Joins.Cases

/-!
# The Case-2 chain, part 7: the Case-2 run at the kit's instance

The Case-2 kit (`Draft/C2Kit.lean`): from the five port words at a Case-2 source input `z` (`IsCaseTwo`) of a live index `ν`, the
kit returns `frame (coreC … ν z … n point).toNat.bits`. the near-cubic-wires paper and Lemma C.10. At the
instance `kitInst` (word of `C_{⟨B*_src⟩_ν}`, native `B*_pf`, `q = q(2^ν)`) the v3 block's request is D7's `requestAt`
(`kitInst_req`), so proof 1's execution (`erun`) returns the padded unsigned XOR bit of `H_{B*}`'s PCPP, which is
`coreC`'s value by `coreC_hardTable` (both fit tests granted by the run's premises: `ClauseReadyC` past its onset, and
`widthAtC ν ≤ n/2`). Budget here: the exact `ebudget + 9`; the polynomial class is `Case2Cost.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

noncomputable section

/-- The H2′ donor (FRONT's `Succinct.H2.h2Ready`), chosen once. -/
def h2 : Front.H2D := Classical.choice Front.h2D_nonempty

variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm)

/-- The kit's block instance at a Case-2 source input. -/
def kitInst (d ν : ℕ) (z : BitInput (2 ^ ν)) (h : IsCaseTwo mw SV d ν z)
    (hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν)) : Inst a :=
  ⟨Outer.outC mw SV ν (selectedPair mw SV d ν z h).src, Outer.width mw SV (2 ^ ν), (selectedPair mw SV d ν z h).pf, hq⟩

/-- **D7 at the kit**: the block's request is `requestAt` at `B*`. -/
theorem kitInst_req (d ν : ℕ) (z : BitInput (2 ^ ν)) (h : IsCaseTwo mw SV d ν z)
    (hq : a.minimumArity ≤ Outer.width mw SV (2 ^ ν)) :
    (kitInst mw SV a d ν z h hq).req = requestAt mw SV a ν (selectedPair mw SV d ν z h) := by
  rw [requestAt_of mw SV a ν _ hq]
  rfl

end

end W3.NearCubicWires.RepairSource.Outer3.Case2
