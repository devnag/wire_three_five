import Close.Chain
import Gadget.ThreeQuery
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NearCubicGates.FiniteAverages
import Target
import Joins.Counter
import Proof.CaseAnalysis.Language
import Proof.Foundations.BooleanCircuitSizePadding
import ENP.UnitPCP

/-!
# J9 and J2 level 2 — the hard table, the gate core, and the closure record ((a′) repair)

* `hardTable` (J9): the near-cubic-gates paper's extraction of the hard table. For an outer verifier `D` that accepts every input (Case 2), the address is
  `(x, clause a, position j)`; the clause list of the three-query PCPP of `checkedCircuit P.code D` is repeated modulo its
  power-of-two count; position `j` reads list entry `j mod 5` of `(X_{a,1}, X_{a,2}, X_{a,3}, Y_a, Y_a)`. Unchanged by
  the repair: it reads `D` only as a circuit on `q` inputs.
* The canonical choices of the near-cubic-gates paper's extraction of the hard table to its uniform recovery (sec:gadget-transfer and sec:all-lengths, the three-way split): the first
  CHECK-passing source circuit `B*_src` (`firstSrc`), the first honest oracle `O*` of `C_{⟨B*_src⟩_ν}` (`firstTable`),
  and the first `q^G`-gate circuit `B*_pf` answering as `O*` (`firstPf`). Case 2 is "`O*` has such a circuit"
  (`IsCaseTwo`); Case 1 is (i) no CHECK-passing source circuit (`srcFn`, the source input itself, is hard) or (iii) `O*`
  has no such circuit (`pfFn`, `O*` itself, is hard). The orders are proof 1's: `canonicalBoundedCircuitDescription` via
  `RecoveryChoice.oracleSelector` on the listed-pairs PCPs (`ENP.unitOuter`, CHECK and `B(a0) = O*(a)`), and
  the false-first order of `boolFunctionTable`, so that the E^NP recovery (the uniform recovery) computes exactly these choices.
* `gateCore`: the native function at one source index. `GateClosure`: what the weak-machine side supplies at one `ε`.
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicWires.ExecutableInterfaces
open NearCubicWires.CanonicalBinary NearCubicWires.RecoveryScheduleEnvelope

/-! ## Honest oracles as tables -/

/-- The oracle given by a table in address order (`binaryAddress`, low bit first, as `boolFunctionTable`). -/
def tableOracle {ℓ : ℕ} (t : BitInput (2 ^ ℓ)) : BitInput ℓ → Bool := fun a => t (binaryAddress a)

/-- `t` is an honest oracle table for `C`: `C^{O_t}` is unsatisfiable (imp:short-pcp's completeness convention). -/
def HonestTable {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) (t : BitInput (2 ^ ℓ)) : Prop :=
  ∀ w, C.eval (tableOracle t) w = false

/-- The false-first least honest table (the near-cubic-gates paper's uniform recovery stage 2: one variable per oracle address, prefix
self-reduction). -/
structure FirstTable {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) where
  table : BitInput (2 ^ ℓ)
  honest : HonestTable C table
  minimal : ∀ t, HonestTable C t → CanonicalBoolListLE (List.ofFn table) (List.ofFn t)

theorem existsFirstTable {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ)
    (h : ∃ t, HonestTable C t) : Nonempty (FirstTable C) := by
  classical
  letI : LinearOrder (BitInput (2 ^ ℓ)) := LinearOrder.lift' List.ofFn List.ofFn_injective
  let eligible : Finset (BitInput (2 ^ ℓ)) := Finset.univ.filter fun t => HonestTable C t
  have hne : eligible.Nonempty := by
    obtain ⟨t, ht⟩ := h
    exact ⟨t, by simp [eligible, ht]⟩
  refine ⟨{ table := eligible.min' hne, honest := ?_, minimal := ?_ }⟩
  · have hm := eligible.min'_mem hne
    simpa only [eligible, Finset.mem_filter, Finset.mem_univ, true_and] using hm
  · intro t ht
    exact eligible.min'_le t (by simp [eligible, ht])

/-- `boolFunctionTable` of a table oracle is the table itself. -/
theorem boolFunctionTable_tableOracle {ℓ : ℕ} (t : BitInput (2 ^ ℓ)) :
    boolFunctionTable (tableOracle t) = List.ofFn t := by
  apply List.ext_getElem
  · simp [boolFunctionTable]
  · intro i h1 h2
    have hi : i < 2 ^ ℓ := by simpa using h2
    simp only [boolFunctionTable, List.getElem_map, List.getElem_range, List.getElem_ofFn, tableOracle]
    rw [binaryAddress_testBit hi]

/-- An oracle making `C^O` unsatisfiable gives an honest table. -/
theorem honestTable_of_oracle {ℓ : ℕ} (C : NearCubicWires.Bindings.MW20.OracleCircuit ℓ ℓ) (O : BitInput ℓ → Bool)
    (hO : ∀ w, C.eval O w = false) : ∃ t, HonestTable C t := by
  refine ⟨fun i => O (NearCubicWires.Bindings.CLW20Lemma310.decodeAddress i), fun w => ?_⟩
  have hO' : tableOracle (fun i => O (NearCubicWires.Bindings.CLW20Lemma310.decodeAddress i)) = O := by
    funext a
    simp only [tableOracle, NearCubicWires.Bindings.CLW20Lemma310.decodeAddress_binaryAddress]
  rw [hO']
  exact hO w

/-! ## The width schedule and the canonical choices (the near-cubic-gates paper's fixed weak machine to its uniform recovery) -/

open NearCubicWires.RepairSource.CloseoutLanguage in
/-- Parameters fixed after `ε` (v2 the fixed weak machine–the uniform recovery): clock exponent `k` (`C_clk = k + 2`), general-oracle exponent
`G = degree`, the instance-length root `lenRoot` (`L_ν = ν^{lenExp+2}` with `lenExp + 2 = 10 (lenRoot + 1)`, so that
`L_ν` is a tenth power and the weak machine's precision guard `γ/L_ν < ε` is its existing `γ < ε·b^{10}` test at
`b = ν^{lenRoot+1}`; Lean's reading of `L_ν = ν^{G+2}`, see `GateParamsReady.lenFit`), clause degree `d_G`, `log₂ P`,
`K_amp`, and the source onset. -/
structure GateParams where
  k : ℕ
  clock : OrdinaryClock (fun n => n ^ (k + 2))
  degree : ℕ
  lenRoot : ℕ
  clauseDegree : ℕ
  positionLog : ℕ
  ampFactor : ℕ
  sourceOnset : ℕ

namespace GateParams
open NearCubicWires.RepairSource.CloseoutLanguage

/-- The instance-length exponent: `L_ν = ν^{lenExp + 2} = (ν^{lenRoot+1})^{10}`. -/
def lenExp (g : GateParams) : ℕ := 10 * g.lenRoot + 8

variable (s : GateSources) (g : GateParams)

/-- lem:succinct-verifier at this clock and instance-length exponent. -/
noncomputable def sv := s.sv g.k g.clock g.lenExp

/-- `O*` as a function of `q` bits (it ignores the last `q − ℓ`); Case 1 (iii). -/
def pfFn {q ℓ : ℕ} (t : BitInput (2 ^ ℓ)) : BoolFunction q := fun r => tableOracle t (Outer.truncInput r)

/-- The amplified, padded Case 1 function. -/
noncomputable def amplified {c d : ℕ} (amplifier : OrdinaryScheduleAmplifier c d) (q : ℕ) (f : BoolFunction q)
    (target : ℕ) : BoolFunction target := by
  classical
  exact
    let gen := amplifier.output q f
    if ht : gen.arity ≤ target then padCore gen.function ht else fun _ => false

end GateParams

/-! ## The closure record -/

end NearCubicGates.Close.Transfer
