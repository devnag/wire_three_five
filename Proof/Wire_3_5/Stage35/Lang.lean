import Proof.Wire_3_5.Stage35.Bundle
import Proof.Wire_3_5.Recovery.CertSchedule

/-!
# The recovered language: the three-way hard core at the source index of the row-B length schedule

Paper v2, §H.5 "The common hard core" (Cases 1a (Hard word), 1b (Hard oracle) and 2 (Hard proof table), in the order
where the first accepted oracle `O*` is chosen before the proof circuit, as in the near-cubic-wires paper) and §H.6
"Exact lengths and canonical recovery": "For source lengths `N_a = 2^a`, put `m_a = t(q(N_a)) q_0(N_a)`. Choose the
largest `a` such that `m_a ≤ n/2`, and extend the selected core to `n` inputs by ignoring the suffix."

The data are generic: `s : WS35` carries the clock exponent, the refuter at the clock `n^(k+2)`, the short-PCP source
`mw` and the succinct verifier `SV` of the refuter's hierarchy; `P` is the pointwise PCPP algorithm, `amp` the
amplifier at the general-circuit exponent `G` (its oracle degree), `D` the clause exponent `d_G`, and `ζ` the
masked-completeness parameter fixing the XOR schedule `t(q)`.

* `copies q = t(q) + 1` (the row-B XOR schedule with one more copy);
* `schedule`: the row-B length schedule at the padded width `q(N) = Outer.width mw SV N`;
* `width_eq`: the schedule's width at the selected index is `Outer.width mw SV (2^a)` (the two width formulas agree
  definitionally);
* **`slice`**: the slice `F_n`, the three-way core `coreC` at the refuter's word `z` for the machine `M` at `N_a`, with
  `t(q)+1` copies and clause width `⌈d_G log₂(q+2)⌉`, padded to `n`;
* **`language`**, **`languageCut`** (`false` while `2^a` is below a cutoff).
-/

set_option autoImplicit false

namespace Stage35

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.WireExponent3_5.Ledger NearCubicWires.WireExponent3_5.Schedule
open NearCubicGates.Close

section Schedule
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- The XOR schedule `t(q) + 1`: one copy beyond `t(q)` = `sched(⌈log₂(q+2)⌉)`, so that the Case-2 advantage is
strictly below `e_{t(q)}` (`Transfer.recCopies`). -/
abbrev copies (q : ℕ) : ℕ := NearCubicWires.WireExponent3_5.Transfer.recCopies h0 h1 q

/-- The row-B length schedule with `t + 1` copies at width `q(2^a) = nativeWidth k A (2^a)`
(`Transfer.recSchedule`). -/
noncomputable abbrev schedule (k A D : ℕ) : LengthSchedule :=
  NearCubicWires.WireExponent3_5.Transfer.recSchedule h0 h1 k A D

end Schedule

section Language
variable (s : WS35) (P : PointwisePCPPAlgorithm) {c d : ℕ} (amp : OrdinaryScheduleAmplifier c d) (D : ℕ) {ζ : ℚ}
  (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- `A_pad` of the substituted outer verifier. -/
noncomputable abbrev apadOf : ℕ := Outer.apad s.mw s.SV

/-- The length schedule at the outer verifier's padded width. -/
noncomputable abbrev sched35 : LengthSchedule := schedule h0 h1 s.k (apadOf s) D

/-- The selected source index `a(n)`: the largest `a ≤ n` with `m_a ≤ n/2`. -/
noncomputable abbrev index (n : ℕ) : ℕ := (sched35 s D h0 h1).sourceIdx n

/-- The width `q = q(2^{a(n)})` of the slice `n`. -/
noncomputable abbrev widthN (n : ℕ) : ℕ := nativeWidth s.k (apadOf s) (2 ^ index s D h0 h1 n)

/-- The refuter's word at the source length `2^a` for the weak machine `M`. -/
noncomputable abbrev word (M : OrdinaryWeakMachine) (a : ℕ) : BitInput (2 ^ a) :=
  s.HR.output M (2 ^ a)

/-- **The slice `F_n`**: the three-way hard core (Hard word, Hard oracle, Hard proof table; `false` at an exceptional
length without an accepted oracle) at the refuter's word for `M` at `N_{a(n)}`, with `t(q)+1` copies and clause
width `⌈d_G log₂(q+2)⌉` at `q = q(N_{a(n)})`, extended to `n` inputs by ignoring the suffix. -/
noncomputable def slice (M : OrdinaryWeakMachine) (n : ℕ) : BoolFunction n :=
  W3.NearCubicWires.RepairSource.Outer3.coreC s.mw s.SV P amp
    (index s D h0 h1 n) (word s M (index s D h0 h1 n)) (copies h0 h1 (widthN s D h0 h1 n))
    (clauseWidth D (widthN s D h0 h1 n)) n

/-- **The recovered language.** -/
noncomputable def language (M : OrdinaryWeakMachine) : Language := fun n => slice s P amp D h0 h1 M n

/-- **The recovered language with a cutoff**: `false` while `2^{a(n)}` is below the cutoff. -/
noncomputable def languageCut (M : OrdinaryWeakMachine) (cutoff : ℕ) : Language :=
  fun n => if cutoff ≤ 2 ^ index s D h0 h1 n then slice s P amp D h0 h1 M n else fun _ => false

theorem languageCut_live (M : OrdinaryWeakMachine) (cutoff n : ℕ) (h : cutoff ≤ 2 ^ index s D h0 h1 n) :
    languageCut s P amp D h0 h1 M cutoff n = slice s P amp D h0 h1 M n := by
  unfold languageCut; rw [if_pos h]

theorem languageCut_dead (M : OrdinaryWeakMachine) (cutoff n : ℕ) (h : ¬ cutoff ≤ 2 ^ index s D h0 h1 n) :
    languageCut s P amp D h0 h1 M cutoff n = fun _ => false := by
  unfold languageCut; rw [if_neg h]

end Language

end Stage35
