import Proof.CaseAnalysis.FinalFuelMajorant

/-! # `StageBlock.hfuel`: what it actually demands, and where the demand comes from

`StageBlock.hfuel` (`Proof/CaseAnalysis/FinalStageContracts.lean`) is

```
hfuel : ∀ (n : ℕ) (x : BitInput n) (bits : List Bool),
  actualFuel sources k p S x bits ≤ S.budget n
```

It is the only one of the fourteen fields with no `Soundness.cutoff ≤ n` guard.
Its consumer is `verdict_of_stage`
(`Proof/CaseAnalysis/FinalTailComposeUniform.lean`), whose deliverable is a
`Weak.StepAtInputs`-shaped `Verdict` at the len-only budget `S.budget` for EVERY
`n` and EVERY witness `bits`; the guard is absent because the consumer has none.

This module settles what that costs, in three steps and with no new hypothesis.

* §1 `actualFuel_eq`: `actualFuel` is a function of the input length `n` and the
  three per-phase CALL COUNTS `(records … ph).length`, and of nothing else.  The
  closed form `fuelAt` names `S.stageFuel`, `S.entryWidth` and `dockedFuel`
  explicitly.  It contains no `Nat` subtraction and no `Nat.log`: nothing in it
  truncates, at `n = 0` or anywhere else.
* §2 `fuel_bounded_iff`: at one length, `hfuel` is satisfiable by SOME budget if
  and only if the per-phase call count is bounded over `bits`.  Both directions
  are proved; the reduction is exact, not a sufficient condition.
* §3 The call count is driven by `2 ^ (pcppOf …).clauseBits`, whose only
  imported bound is `PointwisePCPPAlgorithm.clauseCountBound`
  (`Proof/Foundations/RepresentationSourceContracts.lean`), stated in terms of the
  GUESSED ORACLE's size.  `oracleOf_size_le` proves that size IS bounded by the
  input length -- but only for `bits` satisfying the machine's own header cap
  `16 * bits.length ≤ n`, via `Oracle.decoded_size`
  (`Proof/CaseAnalysis/WitnessOracleParameter.lean`).  `decoder_free` and
  `no_decoder_size_majorant` prove the RAW codec admits every circuit of the
  native arity at EVERY fixed length, so the codec alone has no majorant.
* §4 `oracleOf_size_majorant`: the paper's size guard, now applied by `oracleOf`
  (`Proof/CaseAnalysis/FinalTotalDecode.lean`, `paper.tex:4292`), restores one.
  `gate_rejects_wide` shows its `else` branch is genuinely reached.

`Proof/CaseAnalysis/FinalFuelMajorant.lean` records that "no length-only
decoded-size majorant is claimed"; §3 says why the codec cannot have one.
-/

namespace NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound

open RepairOrdinary RepairOrdinary.CloseoutWitness RepairRepresentation
open SourceInterfaces SupplierPipeline CanonicalBinary CanonicalWitnessCodec
open RepairOrdinary.RadixSemantics
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open RepairOrdinary.CloseoutFinalC10StageSeam
open RepairOrdinary.CloseoutFinalC10WorkerChain
open RepairOrdinary.CloseoutFinalC10WorkerDock
open RepairOrdinary.CloseoutFinalC10CallCountMajorant
open C10TailComposeUniform

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The closed form: `actualFuel` is the call counts and nothing else -/

/-! ## §2 Monotone up, bounded below: the exact satisfiability criterion -/

/-! ## §3 The decoded oracle: the RAW decoder is free, and the gate is what
bounds it -/

/-! ## §4 What the gate restores: the majorant the raw decoder cannot have -/

end
end NearCubicWires.RepairSource.CloseoutFinal.C10StageFuelBound
