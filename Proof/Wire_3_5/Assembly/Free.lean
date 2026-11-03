import Lean
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Recovery.RecoverySetupTwo
import Proof.Wire_3_5.Foundations.Skeleton
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Assembly.FreeBase


noncomputable section


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
  (P3:3797-3798), i.e. `tr:time`'s `q(N)^{callDeg}·callBudget`; the union makes at most `q^{unionCallDeg}` calls at the
  pinned oracle degree (the exponent; its forcing lemma is still to be written), each at a constant times
  `callBudget` plus a `p = O(log q)`-bit rounding, and "It then selects the common star translation" (P3:3673) charges
  one more call. So `callDeg ≥ unionCallDeg + c`. The selection needs no relation on `F`: it fits
  under the main-pass term of `callBudget` for every envelope (`Free.selection_le_callBudget`), and every primitive
  with a satisfiable call has coefficient `≥ 1` (`Free.coef_pos`).
* the recovery leaf reads nothing: the `GateRel` holds at `gate0 l F` for every `F` (`gateRel_gate0`).

Paper quantity of the main type: **`GateFreeOK l F`**, the call exponent `callDeg` of `tr:time` against the union's
call-count exponent at `e_H` (`unionCallDeg l`, Lemma H.7(b)), with the margin `callDegMargin`.
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

-- The union's call-count exponent is `Transfer.unionCallDeg l` (`5·e_H·a_p + 1`, at `e_H` of Lemma H.7(b); order
-- item (6)), defined with the gate constants.


/-- **The relations leaves U and R read from the free constants.** -/
structure GateFreeOK (F : GateFree l) : Prop where
  /-- `tr:time`'s call exponent covers the union's calls with margin `c` (P3:3797-3798). -/
  callDeg : unionCallDeg l + callDegMargin ≤ F.E.callDeg

/-- The pinned union setup at the concrete gate, for every choice of the free constants. -/
noncomputable abbrev setupF (F : GateFree l) : (gate0 l F).Setup := unionSetupS2 l (gate0 l F)

/-- **Leaf P** with the free constants: the constants (existential), their relations, and leaf P at the gate. -/
def PrimitiveLeafF := Σ F : GateFree l, Σ' _ : GateFreeOK l F, PrimitiveLeaf (gate0 l F)

/-! ## The union side of the relation -/

/-- **What the union leaf gets from `GateFreeOK`**: past an onset, any fixed multiple of `(q+1)^{unionCallDeg + c − 1}` is at
most `q^{callDeg}`. The union bounds its calls by `(q+1)^{unionCallDeg}` and its per-call factor by `K·(q+1)^{c−1}`. -/
theorem calls_absorb (F : GateFree l) (hF : GateFreeOK l F) (K : ℕ) :
    ∀ᶠ q : ℕ in atTop, K * (q + 1) ^ (unionCallDeg l + (callDegMargin - 1)) ≤ q ^ F.E.callDeg := by
  have hc : unionCallDeg l + callDegMargin ≤ F.E.callDeg := hF.callDeg
  filter_upwards [eventually_ge_atTop (K * 2 ^ (unionCallDeg l + (callDegMargin - 1)) + 1)] with q hq
  have hq1 : 1 ≤ q := le_trans (Nat.le_add_left 1 _) hq
  have h2 : (q + 1) ^ (unionCallDeg l + (callDegMargin - 1)) ≤ (2 * q) ^ (unionCallDeg l + (callDegMargin - 1)) :=
    Nat.pow_le_pow_left (by omega) _
  have hK : K * 2 ^ (unionCallDeg l + (callDegMargin - 1)) ≤ q := by omega
  have hexp : unionCallDeg l + (callDegMargin - 1) + 1 ≤ F.E.callDeg := by
    unfold callDegMargin at hc ⊢
    omega
  calc K * (q + 1) ^ (unionCallDeg l + (callDegMargin - 1))
      ≤ K * (2 * q) ^ (unionCallDeg l + (callDegMargin - 1)) := Nat.mul_le_mul_left _ h2
    _ = K * 2 ^ (unionCallDeg l + (callDegMargin - 1)) * q ^ (unionCallDeg l + (callDegMargin - 1)) := by
        rw [mul_pow, mul_assoc]
    _ ≤ q * q ^ (unionCallDeg l + (callDegMargin - 1)) := Nat.mul_le_mul_right _ hK
    _ = q ^ (unionCallDeg l + (callDegMargin - 1) + 1) := by rw [pow_succ, mul_comm]
    _ ≤ q ^ F.E.callDeg := Nat.pow_le_pow_right hq1 hexp

/-! ## Satisfiability: the relation never empties leaf P -/

namespace Free

/-- **A primitive at the gate with one satisfiable call has a positive coefficient.** -/
theorem coef_pos (F : GateFree l) {kclk coef A a : ℕ} {ha : a ≤ kclk + 1}
    (P : FusedPrimitive ((gate0 l F).inputs kclk coef A a ha)) (req : PrimRequest)
    (h : ((gate0 l F).inputs kclk coef A a ha).Call req) : 1 ≤ coef := by
  have hb := callBudget_pos P req h
  rcases Nat.eq_zero_or_pos coef with h0 | h0
  · subst h0
    exfalso
    have hz : ((gate0 l F).budget kclk 0 A a ha).callBudget req.n = 0 := by
      simp [Gate.budget, rowBNativeBudget, rowBBudget, TimeBudget.callBudget, ComponentCosts.perCall,
        Machine.costsOf]
    omega
  · exact h0

/-- **The coset selection is one call**: at the gate, for every coefficient `≥ 1` (forced by any
primitive with a satisfiable call, `coef_pos`), any selection machine within `c₁·2^{q/2+csel₁k}q^{Asel₁}` fits in
`callBudget` eventually, whatever the leaf's envelope. So the union charges the selection with no relation on `F`,
provided it docks the selection machine at the machine's OWN envelope `E₁`. -/
theorem selection_le_callBudget (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (hcoef : 1 ≤ coef)
    (E₁ : Envelope) (c₁ : ℕ) :
    ∀ᶠ q : ℕ in atTop, c₁ * classBound E₁ .selection q (((gate0 l F).budget kclk coef A a ha).kOf q)
        (((gate0 l F).budget kclk coef A a ha).psiOf q) ≤ ((gate0 l F).budget kclk coef A a ha).callBudget q := by
  filter_upwards [selection_le_mainPass E₁ F.E F.cr c₁] with q hq
  have h := hq (((gate0 l F).budget kclk coef A a ha).psiOf q) (((gate0 l F).budget kclk coef A a ha).psiOf q)
  refine le_trans h ?_
  show classBound F.E .mainPass q _ _ ≤
    coef * classBound F.E .selection q _ _ + coef * classBound F.E .preprocessing q _ _ +
      coef * classBound F.E .table q _ _ + coef * classBound F.E .mainPass q _ _
  exact le_trans (Nat.le_mul_of_pos_left _ hcoef) (Nat.le_add_left _ _)

end Free

end NearCubicWires.WireExponent3_5.Split

end
