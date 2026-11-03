import W3.Joins.Cases
import Transfer.CaseOne
import Joins.Transfer

/-!
# hardness_pair′ parts: the width schedule at `widthAtC`, the two Case-1 hardness facts, and the
Case-1 finish

* Schedule (C.12, as the old `ScheduleBounds.schedule_onset`): the native widths `q(N_ν)` have bounded
  additive jumps (`Outer.widthOf_step`), so the largest `ν` with `m(q(N_ν)) ≤ n/2` has `n/3 ≤ m ≤ n/2` and passes any
  fixed `s0` eventually. Generic base lemmas `selected_ge`/`selected_fraction`/`core_step`/`core_lower`.
* Hard word: "a circuit with at most q^G gates computing X_z would be a source circuit for z … Hence X_z
  has no general circuit of size q^G" — `srcFn_hard` (gates `Transfer.srcFn_hard`, at `mw SV`).
* Hard oracle: "Ô* has no general circuit of size q^G, since a circuit computing it would satisfy that
  equation" — `pfFn_hard` (gates `Transfer.pfFn_hard`, at `mw SV`).
* Case 1 finish ("in each, a function on q inputs has no general circuit of size q^G, and
  fact:case-one-amplifier applies to it with S(q) = q^G"; §7): `amplified_hard` (old `core_hardness` with
  the gates' `ampCore` in place of `scheduledAmplifierCore`).
-/

set_option autoImplicit false

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.ExecutableInterfaces
open NearCubicWires.CanonicalBinary NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.CircuitRestriction NearCubicWires.PhysicalRecovery
open NearCubicGates.Close

namespace W3.NearCubicWires.RepairSource.Outer3

section Parts

variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  (SV : Outer.SuccinctVerifier H L)

/-- **Hard word** (l.5679–5688): with no CHECK-passing source circuit of `q^G` gates, `X_z` is worst-case hard
(gates `Transfer.srcFn_hard`). -/
theorem srcFn_hard (d ν : ℕ) (z : BitInput (2 ^ ν)) (hno : ¬ SrcExists mw SV d ν z) :
    WorstCaseHardAt (srcFn mw SV ν z) (oracleSizeBound d (Outer.width mw SV (2 ^ ν))) := by
  intro B hB
  by_contra hall
  push Not at hall
  apply hno
  refine ⟨B, hB, fun r => ?_⟩
  apply (ENP.unitOuter_check ν _ _ z z B r).mpr
  funext i
  unfold Outer.ttN
  rw [hall]
  unfold srcFn
  congr 1
  have hlt : i.val < 2 ^ ν := i.isLt
  have : (fun j : Fin ν => Outer.pointOf ν (Outer.width mw SV (2 ^ ν)) i.val
      (Fin.castLE (nu_lt_width mw SV ν).le j)) = fun j : Fin ν => i.val.testBit j.val := by
    funext j
    simp [Outer.pointOf, j.isLt]
  rw [this, binaryAddress_testBit hlt]

/-- **Hard oracle** (l.5705–5708): if no `q^G`-gate circuit answers as the table `t`, then `Ô_t` on `q` bits is
worst-case hard (gates `Transfer.pfFn_hard`). -/
theorem pfFn_hard (d ν : ℕ) (z : BitInput (2 ^ ν)) {ℓ : ℕ} (hℓ : ℓ ≤ Outer.width mw SV (2 ^ ν))
    (t : BitInput (2 ^ ℓ)) (hno : ¬ RecoveryChoice.SmallOracle (matchPCP mw SV ν hℓ t) d z) :
    WorstCaseHardAt (Transfer.GateParams.pfFn (q := Outer.width mw SV (2 ^ ν)) t)
      (oracleSizeBound d (Outer.width mw SV (2 ^ ν))) := by
  intro B hB
  by_contra hall
  push Not at hall
  apply hno
  refine ⟨B, hB, fun r => ?_⟩
  apply (ENP.unitOuter_match ℓ _ hℓ (Transfer.tableOracle t) z B r).mpr
  intro a
  rw [hall]
  unfold Transfer.GateParams.pfFn
  rw [Transfer.truncInput_padQuery hℓ]

end Parts

/-- **Case 1 finish** (Fact C.4): the padded amplified function of a worst-case hard `f` on `q`
inputs has agreement `< 1/2 + γ` with every symmetric/threshold circuit within the caps (old `core_hardness` with the
gates' `ampCore`). -/
theorem amplified_hard {c d q target : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (f : BoolFunction q)
    (hq : 1 ≤ q) (hard : WorstCaseHardAt f (oracleSizeBound d q))
    (normalization : ThresholdNormalizationContract) (symCap thrCap : ℕ)
    (hfit : (amplifier.output q f).arity ≤ target)
    (hsym : 40 * (target + symCap + 2) ^ 4 ≤ integerFloorRoot c (oracleSizeBound d q))
    (hthr : 50 * (target + thrCap + 2) ^ 4 ≤ integerFloorRoot c (oracleSizeBound d q))
    (gamma : ℝ) (hadv : Real.rpow (oracleSizeBound d q : ℝ) (-(1 : ℝ) / c) < gamma) :
    (∀ circuit : SymmetricThresholdCircuit target, circuit.wireCount ≤ symCap →
      agreement circuit.eval (Transfer.GateParams.amplified amplifier q f target) < 1 / 2 + gamma) ∧
    (∀ circuit : ThresholdThresholdCircuit target, circuit.wireCount ≤ thrCap →
      agreement circuit.eval (Transfer.GateParams.amplified amplifier q f target) < 1 / 2 + gamma) := by
  let hardCore := Transfer.ampCore amplifier.toScheduleAmplifier q f hq hard
  have hhard : hardCore.arity ≤ target := hfit
  have heq : Transfer.GateParams.amplified amplifier q f target =
      (padAmplifierCore hardCore target hhard).function := by
    rw [Transfer.amplified_eq amplifier q f target hfit]
    rfl
  have hs := symmetricAverageHard_of_boolean normalization (padAmplifierCore hardCore target hhard) symCap hsym
  have ht := thresholdAverageHard_of_boolean normalization (padAmplifierCore hardCore target hhard) thrCap hthr
  have hstrict : 1 / 2 + (padAmplifierCore hardCore target hhard).advantage < 1 / 2 + gamma := by
    change 1 / 2 + Real.rpow (oracleSizeBound d q : ℝ) (-(1 : ℝ) / c) < 1 / 2 + gamma
    linarith
  rw [heq]
  exact ⟨fun circuit hcap => (hs circuit.eval ⟨circuit, hcap, rfl⟩).trans_lt hstrict,
    fun circuit hcap => (ht circuit.eval ⟨circuit, hcap, rfl⟩).trans_lt hstrict⟩

end W3.NearCubicWires.RepairSource.Outer3
