import Bindings.CLW20_Lemma3_9_TM2
import Bindings.CLW20_Theorem1_13
import Bindings.CTW26_Lemma3_2
import Bindings.Williams14_Corollary4_4
import Statement
import NearCubicGates.PublishedSources.PCPP
import NearCubicGates.PublishedSources.PrimeDensity
import NearCubicGates.PublishedSources.Witness
import Target
import Proof.CaseAnalysis.PairClockExact
import Proof.Circuits.PolynomialOrdinaryClock

/-!
# Input 8 with the multitape clock gives the amplifier source 

`NineInputs.amplification` is CLW20 Lemma 3.9 with the standard multitape `TimeConstructible`
(`CLW20_Lemma3_9_Multitape`). Proof 1's consumer, `SourceAmplifierFactory`, needs the lemma at the size schedule
`oracleSizeBound d = pairClock D`, `S(n) = (n+1)^K − 1` with `K = 2^D`, `D = oracleDepth d ≥ 1`
(`pairClock_succ_exact`). No multitape clock for `pairClock` exists, so the lemma is applied where the near-cubic-gates paper applies
it, "We use [CLW20, Lemma 3.9] with S(q) = q^G"): at `S'(n) = n^K`, whose multitape clock is
`PolynomialClock.ordinaryClock (K − 2)`. `transfer` then moves the conclusion from `S'` to `S` with the constant
doubled: `S' ≤ S` carries the hardness hypothesis down, and `S ≤ S'^2` for `n ≥ 2` carries the
inapproximability up; `n = 0` is the same statement, and `n = 1` is vacuous (every one-bit function has a
two-node circuit, while `S(1) ≥ 3`). `g`, the arity and the construction are unchanged.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Amplifier

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.Bindings.CLW20Lemma39

/-! ## Monotonicity of the two circuit notions -/

/-! ## One-bit functions have two-node circuits -/

/-! ## The two size functions -/

theorem oracleSizeBound_succ (d n : ℕ) : oracleSizeBound d n + 1 = (n + 1) ^ (2 ^ oracleDepth d) :=
  CloseoutPairClock.pairClock_succ_exact _ _

/-! ## The transfer -/

/-! ## The multitape clock and the adapter -/

end NearCubicGates.Close.Amplifier
