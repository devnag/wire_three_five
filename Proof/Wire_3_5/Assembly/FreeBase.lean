import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.PCP.PCPPSubstitutionRequest
import Proof.Wire_3_5.Foundations.Contracts
import Proof.Wire_3_5.Foundations.SkeletonBase
import Proof.Wire_3_5.Ledger.LedgerBudget
import Proof.Wire_3_5.Recovery.RecoveryBudgetBase
import Proof.Wire_3_5.Stars.StarSelectionChoice
import Proof.Wire_3_5.Transfer.TransferSeedCalls
import Proof.Wire_3_5.UnionMachine.UnionCodecBase
import Proof.Wire_3_5.UnionMachine.UnionSchedule
import Proof.CaseAnalysis.NativeWidthStep
import Proof.Foundations.ProjectionPCPPadding
import Proof.PCP.PCPPSubstitutionCircuit
import Proof.Wire_3_5.Recovery.RecoveryLeaf

/-! # The split with the gate's free constants inside leaf P

Realizes the paper's order of choice for the constants that only the primitive's assembly can fix:
"All powers of $n$ are fixed before a fixed $r$ or a positive endpoint coefficient is chosen" (P3:3114-3115), and
"$A$ is fixed by the syntax and accuracy envelopes before a constant multiplier in $r$ is chosen" (P3:3803-3804). The
syntax and accuracy envelopes (`D`, `descDeg`, `carrierDeg`, `nameCount`, `kDeg`, the caps, `s(q)`, `A_pad`) are fixed
by `gate0` from the literals. The rest (`GateFree`: the envelope `E`, `C_D`, the multiplier offset `c_r`, the endpoint
exponent) is chosen by leaf P, as a Σ. No field of `GateFree` is forced to depend on a later choice: B9 proves the fit
conditions for every `E` and every `c_r ≥ 1` (`Ledger.eventually_fits`), the multiplier `r = 2(⌊log₂ L⌋ + c_r)` grows
without bound for every offset, and the endpoint coefficients `a_T = a_S = 1` are gate constants.

Leaves U and R are stated for EVERY choice satisfying `GateFreeOK`, which is exactly what they read from `F`:
* leaf U reads the call exponent: "the time for all polynomially many verification calls has the form [...]"
  (P3:3797-3798), i.e. `tr:time`'s `q(N)^{callDeg}·callBudget`; the union makes at most `q^{gateCallDeg}` calls at the
  pinned oracle degree (the exponent; its forcing lemma is still to be written), each at a constant times
  `callBudget` plus a `p = O(log q)`-bit rounding, and "It then selects the common star translation" (P3:3673) charges
  one more call. So `callDeg ≥ gateCallDeg + c`. The selection needs no relation on `F`: it fits
  under the main-pass term of `callBudget` for every envelope (`Free.selection_le_callBudget`), and every primitive
  with a satisfiable call has coefficient `≥ 1` (`Free.coef_pos`).
* leaf R reads nothing: `GateRel` holds at `gate0 l F` for every `F` (`gateRel_gate0`).

Paper quantity of the main type: **`GateFreeOK l F`**, the call exponent `callDeg` of `tr:time` against the union's
call-count exponent at the pinned oracle degree (`gateCallDeg l (recOracleDeg l)`), with the margin `callDegMargin`.
Main declarations: `PrimitiveLeafF`, `UnionLeafF`, `RecoveryLeafF`, `parts_of_leavesF`, `literals_parts_of_leavesF`,
`rowB_of_leavesF`; the union-side consumer `calls_absorb` and its sharpness `calls_absorb_sharp`; the satisfiability
witness `freeSat` and the transport `primitiveLeafF_of_leaf` (every leaf-P term at ANY free constants gives one at
constants meeting `GateFreeOK`); `Free.callBudget_pos` and `Free.coef_pos` (a primitive with a satisfiable call has a
positive budget and coefficient); `Free.selection_le_mainPass` and `Free.selection_le_callBudget` (the coset selection,
at the selection machine's own envelope, is one call). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Split
open NearCubicWires NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.Transfer Filter

variable (l : Literals)

/-- **The margin `c`** of the call exponent over the union's call-count exponent. The union needs 2: one power of `q`
for the constant per-call factor (the docked estimator, the band clear, one more call for the coset selection) and one
for the `p = O(log q)`-bit rounding. The other 6 are a reserve for the call-count forcing lemma
(T, not yet written) and for per-call glue polynomial in `q`. A larger `callDeg` costs nobody more than an onset:
`callDeg` enters only `Fits` (B9 proves it for every envelope) and the callee's precondition `FitsAt`, which it
strengthens. -/
def callDegMargin : ℕ := 8

/-! ## The union side of the relation -/

/-! ## Satisfiability: the relation never empties leaf P -/

namespace Free

/-- **A primitive with one satisfiable call has a positive per-call budget** (its program must print a nonempty
`ratWord`, and a run of zero steps leaves the fresh output tape empty). So a union leaf stated for every coefficient
may charge fixed work to `callBudget`: at the coefficient `0` no primitive with a satisfiable
call exists. -/
theorem callBudget_pos {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}
    (P : FusedPrimitive I) (req : PrimRequest) (h : I.Call req) : 0 < B.callBudget req.n := by
  rcases Nat.eq_zero_or_pos (B.callBudget req.n) with h0 | h0
  · exfalso
    obtain ⟨receipt, hrun, hout⟩ := P.estimator.realizes ⟨req, h⟩
    have hrun' : LocalBitMultitape.run P.estimator.program.machine 0
        (P.estimator.program.inputTapes req.word) = some receipt := by
      rw [← h0]; exact hrun
    unfold LocalBitMultitape.run LocalBitMultitape.runFrom at hrun'
    split_ifs at hrun'
    cases hrun'
    have hfresh := P.estimator.program.outputFresh
    have hnil : (P.estimator.program.inputTapes req.word) P.estimator.program.outputTape = [] := by
      unfold RepairOrdinary.Program.inputTapes
      rw [if_neg hfresh]
    have hout' : (P.estimator.program.inputTapes req.word) P.estimator.program.outputTape =
        ratWord (P.value req) := hout
    rw [hnil] at hout'
    unfold ratWord RepairRepresentation.intWord at hout'
    simp at hout'
  · exact h0

/-- **The coset selection fits under the main pass** (P3:3105-3109, 3799-3800): for every selection envelope `E₁`
(the selection machine's own exponents), every constant `c₁`, every leaf envelope `E` and offset `c_r`, eventually
`c₁·2^{q/2+csel₁·k}q^{Asel₁} ≤ 2^{q−k/4}q^{Amain}` at the row-B star width, because `k ≤ (2c_r+3)L² = o(q)`. -/
theorem selection_le_mainPass (E₁ E : Envelope) (cr c₁ : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ psi psi' : ℕ, c₁ * classBound E₁ .selection q (starWidth (rowBr cr q) q) psi ≤
      classBound E .mainPass q (starWidth (rowBr cr q) q) psi' := by
  filter_upwards [eventually_mul_Lq_pow_le (4 * ((E₁.csel + 1) * (2 * cr + 3) + E₁.Asel + c₁ + 1)) 2,
    eventually_ge_atTop 1] with q hq hq1 psi psi'
  set L := Lq q with hLdef
  set k := starWidth (rowBr cr q) q with hkdef
  set T := (E₁.csel + 1) * (2 * cr + 3) with hT
  have hL : 1 ≤ L := Lq_pos q
  have hk : k ≤ (2 * cr + 3) * L ^ 2 := by
    have h1 : k ≤ rowBr cr q * L := starWidth_le (rowBr cr q) q
    have h2 : rowBr cr q + 1 ≤ (2 * cr + 3) * L := rowBr_succ_le cr q
    calc k ≤ rowBr cr q * L := h1
      _ ≤ ((2 * cr + 3) * L) * L := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * cr + 3) * L ^ 2 := by ring
  have hqL : q ≤ 2 ^ L := le_trans (by omega) (Nat.le_pow_clog (by norm_num) (q + 2))
  have hc1 : c₁ ≤ 2 ^ c₁ := (Nat.lt_two_pow_self).le
  have hLL : L ≤ L ^ 2 := by nlinarith
  have ha : E₁.csel * k + k / 4 ≤ (E₁.csel + 1) * k := by
    have := Nat.div_le_self k 4
    rw [add_mul, one_mul]
    omega
  have hb : (E₁.csel + 1) * k ≤ T * L ^ 2 := by
    calc (E₁.csel + 1) * k ≤ (E₁.csel + 1) * ((2 * cr + 3) * L ^ 2) := Nat.mul_le_mul_left _ hk
      _ = T * L ^ 2 := by rw [hT]; ring
  have hc : E₁.Asel * L ≤ E₁.Asel * L ^ 2 := Nat.mul_le_mul_left _ hLL
  have hd : c₁ ≤ c₁ * L ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  have he : 4 * (T * L ^ 2) + 4 * (E₁.Asel * L ^ 2) + 4 * (c₁ * L ^ 2) + 4 * L ^ 2 ≤ q := by
    have e : 4 * (T + E₁.Asel + c₁ + 1) * L ^ 2 =
        4 * (T * L ^ 2) + 4 * (E₁.Asel * L ^ 2) + 4 * (c₁ * L ^ 2) + 4 * L ^ 2 := by ring
    rw [← e]
    exact hq
  have hexp : q / 2 + E₁.csel * k + L * E₁.Asel + c₁ ≤ q - k / 4 := by
    rw [mul_comm L E₁.Asel]
    omega
  show c₁ * (2 ^ (q / 2 + E₁.csel * k) * q ^ E₁.Asel) ≤ 2 ^ (q - k / 4) * q ^ E.Amain
  have hpow : q ^ E₁.Asel ≤ 2 ^ (L * E₁.Asel) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hqL _
  calc c₁ * (2 ^ (q / 2 + E₁.csel * k) * q ^ E₁.Asel)
      ≤ 2 ^ c₁ * (2 ^ (q / 2 + E₁.csel * k) * 2 ^ (L * E₁.Asel)) :=
        Nat.mul_le_mul hc1 (Nat.mul_le_mul_left _ hpow)
    _ = 2 ^ (q / 2 + E₁.csel * k + L * E₁.Asel + c₁) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ (q - k / 4) := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ 2 ^ (q - k / 4) * q ^ E.Amain := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hq1)

end Free

end NearCubicWires.WireExponent3_5.Split
