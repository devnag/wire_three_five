import Lean
import Proof.Wire_3_5.Recovery.RecoveryLedgerAt
import Proof.Wire_3_5.Recovery.RecoveryCaseOne
import Proof.Foundations.PolynomialSchedule
import W3.Proof.Foundations.SourceRegistry
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Transfer.LiteralSources
import Proof.Wire_3_5.Recovery.RecoveryBudget
import Proof.Wire_3_5.Recovery.RecoveryLanguage
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.UnionSetup
import Proof.Wire_3_5.Recovery.RecoveryEventualBase


noncomputable section
set_option maxRecDepth 120000


/-! # The recovery's per-width facts hold eventually (P3:3657-3697, 3737-3756, 3820-3852; D1.7)

Realizes the "sufficiently large `q`" of the recovery's ledger at the gate constants: the grid, the star, the per-atom
caps `w_i(q) = a_i q^{7/2}/L^{K_i}` ("Take an even `r = Θ(log L)` [...] `w_i(q)`", P3:3820-3824, 3784-3785), the clause
width ("Choose a branch-independent integer `d_G` bounding all PCPP clause counts", P3:3657-3659), the propagated
errors (P3:3616-3624), the Case-1 conditions (P3:3685-3692, 3839-3840), the XOR copies beyond the amplifier's arity
coefficient, and the guess budget "Every guess has `q^{O(1)} = o(N)` bits" (P3:3675-3677).

Paper quantities:
* `xorEpsilon_succ_lt`: one more XOR copy strictly lowers the advantage threshold `e_t`;
* the caps: `q ≤ ⌊w_i(q)⌋` and `⌊w_i(q)⌋ + 1 ≤ 2(q+1)⁴` eventually (`eventually_wireCap_ge`, `eventually_wireCap_le`);
* the grid `s(q) ≤ q` and the clause width `⌈d_G log₂(q+2)⌉ ≤ q` eventually;
* `recKo`: the code bound of one circuit of size `≤ q^G`;
* **`RecQ l G q`** (the per-width facts) and **`eventually_recQ`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Schedule NearCubicWires.RecoveryWitnessPolicy NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open Filter

/-! ## One more XOR copy -/

/-! ## The per-atom caps -/

/-! ## The grid and the clause width -/

/-! ## The guess budget as a fixed polynomial of `q` -/

section BudgetPoly
variable (l : Literals)

/-- The oracle size exponent `2^{oracleDepth G}` (`q^G ≤ (q+1)^{2^{oracleDepth G}}`). -/
noncomputable def recOracleExp : ℕ := 2 ^ RecoveryScheduleEnvelope.oracleDepth (recOracleDeg l)

/-- The oracle code bound `K_O(q)`. -/
noncomputable def recKo (q : ℕ) : ℕ :=
  2 * canonicalBooleanCircuitCodeBitBound ((q + 1) ^ recOracleExp l + 4) + 1

-- The guess-length envelope of the outer step (two circuits, `H_Γ` of size `q^{e_H}`) is stated with the leaf
-- (`HybridLeafOk`); the one of the old outer step is not used.

end BudgetPoly

/-! ## The per-width facts -/

/-- **The recovery's per-width facts** at the width `q`. -/
structure RecQ (l : Literals) (G : Split.Gate) (q : ℕ) : Prop where
  two : 2 ≤ q
  big : 75894 ≤ q + 1
  star : Even (rowBr G.row.cr q) ∧ 2 ≤ rowBr G.row.cr q ∧ 4 * rowBr G.row.cr q ≤ q ∧
    Lq q ≤ starWidth (rowBr G.row.cr q) q ∧ starWidth (rowBr G.row.cr q) q ≤ Lq q ^ G.kDeg
  capS : q ≤ ⌊wireCap G.row.cap .sym q⌋₊ ∧ ⌊wireCap G.row.cap .sym q⌋₊ + 1 ≤ 2 * (q + 1) ^ 4
  capT : q ≤ ⌊wireCap G.row.cap .thr q⌋₊ ∧ ⌊wireCap G.row.cap .thr q⌋₊ + 1 ≤ 2 * (q + 1) ^ 4
  sp : G.row.sp q ≤ q
  cw : clauseWidth (recDG l) q ≤ q
  xi : 1 / (2 : ℝ) ^ (G.filterErrDeg * Nat.clog 2 (q + 2)) ≤ ((gateCParams1 l).ξ : ℝ)
  hD : (1 + (rowBLambda (gateZeta_pos l) (gateZeta_lt l) 2 q : ℝ)) ^ 4 * (q : ℝ) ^ (-(G.D : ℝ)) ≤
    ((gateParams1 l).eps0 : ℝ)
  pow17 : 12800 * (q + 1) ^ 16 ≤ q ^ 17
  adv1 : Real.rpow (RecoveryScheduleEnvelope.oracleSizeBound (17 * l.eightSources.amplification.stvExponent) q : ℝ)
      (-(1 : ℝ) / l.eightSources.amplification.stvExponent) <
    xorEpsilon ((gateCParams1 l).ζ : ℝ) (rowBt (gateZeta_pos l) (gateZeta_lt l) q)
  copies : l.eightSources.amplification.schedule.arityCoefficient ≤
    recCopies (gateZeta_pos l) (gateZeta_lt l) q

/-- **The per-width facts hold eventually** at the gate constants. -/
theorem eventually_recQ (l : Literals) (G : Split.Gate) (hG : GateRel l G) : ∀ᶠ q : ℕ in atTop, RecQ l G q := by
  have hξ : (0 : ℝ) < ((gateCParams1 l).ξ : ℝ) := by
    have e : (gateCParams1 l).ξ = gateEps l / 100 := rfl
    have := gateEps_pos l
    rw [e]; push_cast; positivity
  have he0 : (0 : ℝ) < ((gateParams1 l).eps0 : ℝ) := by
    have e : (gateParams1 l).eps0 = gateEps l ^ 2 / 20000 := rfl
    have := gateEps_pos l
    rw [e]; push_cast; positivity
  have hf : 1 ≤ G.filterErrDeg := by have := G.hG7; omega
  have hcop : ∀ᶠ q : ℕ in atTop,
      l.eightSources.amplification.schedule.arityCoefficient ≤
        recCopies (gateZeta_pos l) (gateZeta_lt l) q :=
    (recSchedule (gateZeta_pos l) (gateZeta_lt l) 0 0 0).t_tendsto.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 75894, eventually_star G.row.cr G.row.cr_pos G.kDeg hG.kdeg,
    eventually_wireCap_ge G.row.cap .sym hG.aS, eventually_wireCap_le G.row.cap .sym,
    eventually_wireCap_ge G.row.cap .thr hG.aT, eventually_wireCap_le G.row.cap .thr,
    eventually_sp_le G.row, eventually_clauseWidth_le (recDG l),
    eventually_hξ G.filterErrDeg hf _ hξ, eventually_hD (gateZeta_pos l) (gateZeta_lt l) G.D G.D_pos _ he0,
    eventually_12800,
    eventually_caseOne_adv (gateZeta_pos l) (gateZeta_lt l) _ l.eightSources.amplification.stvExponentPositive,
    hcop] with q hq hstar hS1 hS2 hT1 hT2 hsp hcw hxi hD h17 hadv hc
  exact ⟨by omega, by omega, hstar, floorCap_facts _ _ q hS1 hS2, floorCap_facts _ _ q hT1 hT2, hsp, hcw, hxi, hD,
    h17, hadv, hc⟩

end NearCubicWires.WireExponent3_5.Transfer

end
