import W3.Recovery3.Bundle

/-!
# The parameter record of the after-prefix recovery with a growing XOR schedule

Paper v2, §H.5 Case 2 ("Lemma H.1 makes `f^{⊕t(q)}` correlation hard") and §H.6 ("For source lengths `N_a = 2^a`, put
`m_a = t(q(N_a)) q_0(N_a)`"): the number of XOR copies is a function of the width `q`, `t(q) + 1`, which grows with `q`.
The near-cubic-wires recovery reads its parameters through the record `W3.Recovery3.WP` with a constant copy count
`ampFactor`. `WQ` is the same record with `copies : ℕ → ℕ` read at `q = q(N_ν)`; every accessor keeps its name and
meaning (`gateCore` is the three-way core `coreC` with `copies (q(N_ν))` copies, `coreArity` is
`m(q) = copies(q) · q₀(q)`). `WQ` also carries the amplifier `amp` at the oracle degree `degree` (CLW20 Lemma 3.9 at
`S = q^G`).

`WS35` is the fixed data of the recovery: the clock exponent `k`, the clock, the hierarchy and its refuter at
`n^(k+2)` (CLW20 Theorem 1.13), the short-PCP source `mw` and the succinct verifier `SV` of the refuter's hierarchy.
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.LocalBitMultitape
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.Close NearCubicWires.Bindings.CLW20Lemma311

namespace Stage35

/-- The fixed data of the recovery: the clock `n^(k+2)`, the refuter at that clock, the short-PCP source and the
succinct verifier of the refuter's hierarchy. -/
structure WS35 where
  k : ℕ
  clock : OrdinaryClock (fun n => n ^ (k + 2))
  HR : HierarchyRefuterAlgorithm (fun n => n ^ (k + 2))
  mw : Outer.MWSource
  L : ℕ
  SV : Outer.SuccinctVerifier HR.hierarchy L

/-- The numeric parameters of the recovered language: `G`, `d_G`, the copy schedule `q ↦ t(q)+1`, the source onset,
the selector, and the amplifier at the oracle degree `G`. -/
structure WQ where
  degree : ℕ
  clauseDegree : ℕ
  copies : ℕ → ℕ
  sourceOnset : ℕ
  /-- The source index the program selects at each final length (the Case-2 producer recomputes it). -/
  sel : ℕ → ℕ
  /-- The amplifier's exponent `c`. -/
  ampC : ℕ
  /-- The amplifier at the oracle degree `G` (Case 1). -/
  amp : OrdinaryScheduleAmplifier ampC degree

namespace WQ

open W3.NearCubicWires.RepairSource

/-- `log₂ P − 1 = 0`: the core has `q + ⌈d_G lg(q+2)⌉ + 1` inputs per copy. -/
abbrev positionLog (_g : WQ) : ℕ := 1

/-- `q(N_ν)`. -/
noncomputable abbrev width (_g : WQ) (s : WS35) (ν : ℕ) : ℕ := Outer.width s.mw s.SV (2 ^ ν)

theorem nu_lt_width (g : WQ) (s : WS35) (ν : ℕ) : ν < g.width s ν := Outer3.nu_lt_width s.mw s.SV ν

/-- The `q^G` cap. -/
noncomputable abbrev bound (g : WQ) (s : WS35) (ν : ℕ) : ℕ := oracleSizeBound g.degree (g.width s ν)

/-- `C_{⟨B⟩_ν}`. -/
noncomputable abbrev outC (_g : WQ) (s : WS35) (ν : ℕ) {m : ℕ} (B : BooleanCircuit m) := Outer.outC s.mw s.SV ν B

noncomputable abbrev checkPCP (_g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) := Outer3.checkPCP s.mw s.SV ν z

abbrev SrcExists (g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) : Prop := Outer3.SrcExists s.mw s.SV g.degree ν z

noncomputable abbrev firstSrc (g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.SrcExists s ν z) :
    BooleanCircuit (g.width s ν) := Outer3.firstSrc s.mw s.SV g.degree ν z h

/-- Stage 2's condition: `C_{⟨B*_src⟩_ν}` has an accepted (honest) oracle table. -/
abbrev AcceptedOracle (g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.SrcExists s ν z) : Prop :=
  Outer3.AcceptedOracle s.mw s.SV g.degree ν z h

noncomputable abbrev matchPCP (g : WQ) (s : WS35) (ν : ℕ) {ℓ : ℕ} (hℓ : ℓ ≤ g.width s ν) (t : BitInput (2 ^ ℓ)) :=
  Outer3.matchPCP s.mw s.SV ν hℓ t

noncomputable abbrev srcFn (g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) : BoolFunction (g.width s ν) :=
  Outer3.srcFn s.mw s.SV ν z

abbrev IsCaseTwo (g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) : Prop := Outer3.IsCaseTwo s.mw s.SV g.degree ν z

noncomputable abbrev selectedPair (g : WQ) (s : WS35) (ν : ℕ) (z : BitInput (2 ^ ν)) (h : g.IsCaseTwo s ν z) :
    Outer.OuterGuess (g.width s ν) := Outer3.selectedPair s.mw s.SV g.degree ν z h

/-- **The hard slice** (the three-way core `coreC`) with `copies (q(N_ν))` copies: `cl` is `⌈d_G lg(q+2)⌉`, `pl` is
ignored. -/
noncomputable abbrev gateCore (g : WQ) (s : WS35) (P : PointwisePCPPAlgorithm) {c d : ℕ}
    (amplifier : OrdinaryScheduleAmplifier c d) (ν : ℕ) (z : BitInput (2 ^ ν)) (cl _pl target : ℕ) :
    BoolFunction target :=
  Outer3.coreC s.mw s.SV P amplifier ν z (g.copies (g.width s ν)) cl target

/-- `q₀(q) = q + ⌈d_G lg(q+2)⌉ + 1`. -/
noncomputable abbrev tableArity (g : WQ) (s : WS35) (ν : ℕ) : ℕ :=
  g.width s ν + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog

/-- `m(q) = copies(q) · q₀(q)`. -/
noncomputable abbrev coreArity (g : WQ) (s : WS35) (ν : ℕ) : ℕ := g.copies (g.width s ν) * g.tableArity s ν

end WQ

end Stage35
