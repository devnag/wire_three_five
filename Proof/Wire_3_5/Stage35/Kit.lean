import W3.Joins.Cases
import Recovery.HardTableRuns

/-!
# The Case-2 producer interface with a growing copy count

Paper v2, §H.6 stage 2 (in the near-cubic-wires order: `O*` first, then a proof circuit `B_pf` with `O_{B_pf} = O*`):
"In the yes case (Case 2, Hard proof table), prefix self-reduction recovers `Γ*_pf`. Each honest proof bit is then
computed by the deterministic PCPP algorithm"; §H.5 Case 2: "Lemma H.1 makes `f^{⊕t(q)}` correlation hard".

**Consumer backward.** The consumer is the Case-2 piece of the after-prefix program (`After4Tail3`): after the A-run
and stage 3 it holds the five words of `Recovery.portInput` — the word of `C_{⟨B*_src⟩_ν}`, the framed canonical
description of `B*_pf`, the framed final address, `1^q`, `1^{q^G}` — and needs ONE machine that returns the slice's
bit there. `Kit` is the near-cubic-wires Case-2 kit with the copy count read at the width, `copies q`, instead of a
constant (the number of XOR copies `t(q) + 1` grows with `q`, so one machine must serve every copy count).
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.LocalBitMultitape
open NearCubicGates.Close
open W3.NearCubicWires.RepairSource.Outer3

namespace Stage35

/-- **The Case-2 kit (data)**: one machine; on the five words of `Recovery.portInput` at a Case-2 source input `z`
(`IsCaseTwo`) of a live index `ν` past `cutoff` (`copies(q)·(q + ⌈d_G lg(q+2)⌉ + 1) ≤ n/2`, `q = q(N_ν)`), it reaches
a ready run within `C·(2^n+1)^E` whose output port (index `≥ 5`) holds the framed bit `coreC … ν z (copies q) … n point`
of the slice, at the source index `ν = sel n` the program selects. -/
structure CaseTwoKit (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
    (SV : Outer.SuccinctVerifier H L) (a : PointwisePCPPAlgorithm) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (copies : ℕ → ℕ) (clauseDegree : ℕ) (sel : ℕ → ℕ) where
  t : ℕ
  st : ℕ
  M : Machine t st
  output : Fin t
  large : 5 ≤ output.val
  cutoff : ℕ
  C : ℕ
  E : ℕ
  run : ∀ (n : ℕ) (point : BitInput n) (ν : ℕ) (z : BitInput (2 ^ ν)), ν ≤ n → cutoff ≤ 2 ^ ν → ν = sel n →
    coreWidth (copies (Outer.width mw SV (2 ^ ν))) clauseDegree (Outer.width mw SV (2 ^ ν)) ≤ n / 2 →
    ∀ h : IsCaseTwo mw SV d ν z,
    ∃ out, ClockJoin.ReadyRun M (C * (2 ^ n + 1) ^ E)
      (Recovery.portInput t (Outer.outC mw SV ν (selectedPair mw SV d ν z h).src).word
        (RepairOrdinary.frame (OuterPCPRecovery.canonicalBoundedCircuitDescription
          (oracleSizeBound d (Outer.width mw SV (2 ^ ν))) (selectedPair mw SV d ν z h).pf))
        (RepairOrdinary.frame (List.ofFn point)) (Outer.width mw SV (2 ^ ν))
        (oracleSizeBound d (Outer.width mw SV (2 ^ ν)))) out ∧
      out output = RepairOrdinary.frame
        (coreC mw SV a amplifier ν z (copies (Outer.width mw SV (2 ^ ν)))
          (clauseWidth clauseDegree (Outer.width mw SV (2 ^ ν))) n point).toNat.bits

end Stage35
